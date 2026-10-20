# Using rustd with cargo

There are two ways to use rustd from cargo. `cargo rustd <command>` is an explicit
subcommand, described here. The second, switching rustd on globally so that plain `cargo`
goes through it, has its own section at the end.

Everything in this file was checked against the code in `crates/rustd/src/cargo/` and run on
Linux x86-64. On macOS arm64 `harness/cargo_rustd.py --small` was run, and what is known of
it is under [macOS arm64](#macos-arm64). The design notes it was written from are in
[reports/CARGO.md](reports/CARGO.md).

## Install

`cargo rustd` is cargo's way of running a program called `cargo-rustd` on your `PATH`. That
program is built with rustd and runs the `rustd` executable in the same directory, so the two
have to be installed side by side:

    cargo +1.99.0 build -p rustd --release
    cp target/release/rustd target/release/cargo-rustd ~/.cargo/bin/

The project you build must use Rust 1.99.0, the toolchain rustd is pinned to. Use a
`rust-toolchain.toml`, `rustup override set 1.99.0`, or `RUSTUP_TOOLCHAIN=1.99.0`.

## Commands

    cargo rustd build [cargo's flags]
    cargo rustd run   [cargo's flags] [-- program arguments]
    cargo rustd test  [cargo's flags] [test names] [-- test arguments]
    cargo rustd check [cargo's flags]
    cargo rustd clippy [cargo's flags] [-- -D warnings ...]
    cargo rustd status
    cargo rustd stop

`build`, `run` and `test` take the flags cargo takes and leave the same files in the same
places under `target/`. `check` is `cargo check` and nothing else: rustd has no diagnostics
of its own. `status` prints what the daemon holds, and for every workspace how many builds
the daemon served and how many went to cargo, which through `cargo rustd` is none. `stop` ends the daemon. Any other subcommand is passed to cargo as typed.

## What a build does

The crates of the workspace are compiled by rustd, in the first build and in every build
after it. rustc compiles what the workspace depends on, and nothing of the workspace except
what runs on the host during the build (below). `cargo rustd` never hands a build of the
workspace to cargo: what rustd cannot build fails the build, with the reason.

The first build runs cargo once, with rustd as the `RUSTC_WORKSPACE_WRAPPER`. For a crate
from the registry the wrapper runs rustc exactly as cargo asked, so those are the same
artifacts a plain `cargo build` makes and a shared cache (sccache, a CI cache of `target/`)
serves them. For a crate of the workspace the wrapper gives rustc a source with no code in
it, which only names the crates it is linked against: cargo's plan, its fingerprints and
the linker line are real, and no function of the workspace is compiled by rustc. While
cargo runs, the daemon loads the workspace; when cargo is done, the daemon compiles the
workspace's crates and links the programs, which are put where cargo would have put them.
Two `Finished` lines are printed, cargo's and then rustd's:

    Finished `dev` profile [unoptimized + debuginfo] target(s) in 5.31s
    Finished `dev` profile [rustd] target(s) in 9.87s

A build after an edit does not start cargo at all. The daemon compiles the functions that
changed and either splices them into the executable or links again.

When something cargo acts on has changed (a manifest, `Cargo.lock`, a cargo configuration
file, the toolchain file, a build script or proc macro of the workspace, or something a
build script reads), the build starts over the same way: cargo runs once, rustc builds the
dependencies that are new or changed and reruns the build scripts that have to, and the
daemon loads the workspace again and builds its crates. The same happens when rustd's
records are missing, were written by another version of rustd, or `target/` was removed.
On a large workspace the reload is long: 36 to 51 s on nushell.

A build asked while the daemon is still loading the workspace waits for it.

`run` then runs the program and `test` runs the test executables the way cargo does: the
same working directory, the variables cargo sets, cargo's `Running` lines and the same exit
status.

### What rustc still compiles of the workspace

Build scripts, proc-macro crates, and the workspace crates either of them depends on. They
run on the host inside cargo and rustc while the build is planned, and rustc loads a proc
macro as a dynamic library of its own ABI; rustd makes neither yet. Every other crate of
the workspace is rustd's.

## What fails the build

Each of these is an error that names what is not supported, with exit status 101. None of
them is built by cargo instead.

| Asked | Error |
|---|---|
| `--benches`, `--bench`, `--all-targets` | the daemon does not build the benchmarks of a workspace yet |
| `--message-format` other than `human` and `short` (the JSON ones), `--build-plan`, `--unit-graph` | the flag is not answered by `cargo rustd` yet |
| a `-Z` flag | unstable cargo flags are not read by rustd |
| more than one `--target` | several `--target` in one build are not built by the daemon yet |
| `--target` or `CARGO_BUILD_TARGET` naming a target that is neither ELF nor Mach-O, or one rustd does not know | programs for the triple are not linked through `cargo rustd` yet |
| `RUSTC_WORKSPACE_WRAPPER` set to another wrapper | `cargo rustd` does not run rustc through it |
| `rustd-rustc` or `rustd-rustc-first` missing | `rustd-rustc` (or `rustd-rustc-first`) is not installed next to `rustd` |
| a toolchain other than the one rustd is pinned to | rustc 1.x is not the 1.99.0 this rustd compiles for |
| a workspace crate built as `cdylib`, `dylib`, `staticlib`, or as more than one crate type | the daemon builds a `lib`, an `rlib` or a `bin` alone |
| a workspace in which every crate is a build script's, a proc macro or a dependency of one | the daemon builds none of those yet |
| `lto`, coverage or profiling flags, and what else `plan.rs` refuses | the reason, per program |
| source in which rust-analyzer finds an error | `path:line:column: message [E0308]` |
| a function the daemon cannot compile | the function and the reason |

Tests are the largest of these. rustc compiles a test crate whole in order to write its
harness, and no crate of the workspace is rustc's to compile; the daemon has to write the
harness itself. Doc tests are the daemon's too, with no rustdoc: the examples of a library
are one crate the daemon writes and builds, a module each, and each runs in a process of
its own. An example that only a crate of its own can be (`#![feature]`, `crate::`, another
edition) fails with the reason. A `compile_fail` example passes when rust-analyzer finds an
error in it, so one that only the borrow checker refuses fails, saying so.

These flags are handled: `--target` naming the host, `-p`, `--features`, `--bin`, `--bins`,
`--example`, `--examples`, `--lib`, `--manifest-path`, `--workspace`, `--release`,
`--profile`, `-q`, and the arguments after `--`.

The daemon's state is kept per command line. `cargo rustd build`, `cargo rustd build -q`
and `cargo rustd build --features x` are three different builds to rustd, told apart by a
hash of the subcommand (`run` counts as `build`), the build flags, the working directory
and the environment variables that change what cargo builds. The first use of each runs
cargo once, which has little to do when the dependencies are already built.

## The daemon

There is one daemon per user. It is started by the first `cargo rustd` that needs it, in a
session of its own, and it outlives the command that started it. It exits after 30 minutes
without a request; `RUSTD_IDLE_SECS` sets another time and is read when the daemon starts
(0 means never).

The daemon holds no compiler state itself. It owns worker processes, each holding one
rust-analyzer database for one repository, toolchain, target, feature set and `cfg(test)`
setting. Git worktrees of one repository share a worker, so what they have in common is
analysed once. Different repositories get different workers.

A new worktree still has cargo build the dependencies, because it has a target directory
of its own. What it saves is the daemon's side: the worktree joins the worker that is
already loaded instead of loading the workspace again.

`cargo rustd status` shows the daemon, its workers and their log files:

    daemon: pid 10969, version 0.0.0-3da7208-18df73efa25a74db, exits after 1800s idle
      worker: pid 13169, /dev/shm/ripgrep/, log /home/user/.cache/rustd/workers/f30b80a4e02dffde/log
        /dev/shm/ripgrep: ready
    /dev/shm/ripgrep (dev, 1f59ed7b049b7fa0): 3 builds by the daemon, 0 by cargo

A worker for a large workspace holds a lot of memory: 1.3 GB for ripgrep and 9.4 GB for
dioxus-cli at the end of the agent-style edit runs in [results.md](results.md).

A client and a daemon built from different sources do not talk to each other. A daemon that
gets a build request from another version stops its workers and exits, and the client
starts its own.

### Files

The daemon's directory is `$RUSTD_HOME` if set, else `$XDG_RUNTIME_DIR/rustd`, else
`~/.cache/rustd`. It holds `daemon.sock`, `daemon.sock.lock`, `daemon.log`,
`workers/<id>/` with each worker's socket and log, and `states/`. The directory must belong
to you and be closed to group and others (mode 0700); otherwise the client and the daemon
refuse to use it. The socket is 0600, and a connection from another user is refused before
its request is read.

In a project, rustd keeps its records next to cargo's output, so `cargo clean` removes
them too:

    target/<profile>/.rustd-units/     what the wrapper recorded of each rustc run
    target/rustd/<key>/                state of one command line, and the daemon's objects

Cargo keeps what it builds through a workspace wrapper apart from what it builds without
one. `cargo build` and `cargo rustd build` in one checkout therefore each compile the
workspace's crates once, and share the dependencies.

## Which tests run

`cargo rustd test` remembers the tests that passed, in the daemon's memory: a new daemon
runs every test once. When a test program is built, the
daemon writes beside it what each test can reach: the functions, the instances of generic
ones and the statics, with a print of their code. A test that passed is not run again when
nothing it can reach changed and nothing outside the code changed either. It is listed
as `ok (cached)`. Each test that is run is a process of its own.

Outside the code means the environment, the test's arguments, the other programs of the
build, and the length and time of every file in the package that is not a Rust source the
build compiled. A test that reaches code that is not all known is run every time. A test
that failed is not remembered.

Each test that runs is a process of its own, with as many at once as `--test-threads` says,
or one per core. A test that depends on what another test left in the process fails, as
under nextest. `RUSTD_TEST_TIMEOUT`, in seconds, stops and fails a test that runs longer.

`--rerun-all` or `RUSTD_TEST_CACHE=0` runs every test in one process, as libtest does,
and nothing is remembered from that run.

## Clippy

`cargo rustd clippy` builds what `cargo rustd build` builds, then asks the daemon for
clippy's lints of the crates of those programs and prints them as clippy does. The lints of a
body are one query of the worker's database, so the database runs them again only for the
bodies an edit changed or whose types changed: after an edit to one function, one body is
linted again. `RUSTD_STATS=1` prints how many.

Eight of clippy's lints are there: `bool_comparison`, `eq_op`, `identity_op`,
`len_zero`, `let_unit_value`, `needless_bool`, `needless_return` and `self_assignment`,
at clippy's levels. `#[allow]`, `#[warn]`, `#[deny]` and `#[expect]` on the item, its module
or the crate are read, and so are `-D`, `-W` and `-A` after `--`, `-D warnings` among them.
Nothing in what a macro wrote is linted. rustc's own warnings are not printed, and a
workspace of libraries alone, which builds no program, fails with that reason.
`harness/clippy.py` compares it with clippy.

## Environment variables

These are read by `cargo rustd` and passed to the worker it starts. They are part of which
build a command line is, so changing one starts from a first build again.

| Variable | Meaning | Default |
|---|---|---|
| `RUSTD_BACKEND` | `cranelift` or `llvm`. `llvm` needs a rustd built with `--features llvm` | `cranelift` |
| `RUSTD_OPT` | LLVM optimisation level, 0 to 3. Functions are still compiled one at a time | 2 |
| `RUSTD_EMIT` | LLVM instruction selection: `optimized` or `fast` | `optimized`; `fast` at level 0 |
| `RUSTD_SPLICE` | `0` links in full after every edit instead of splicing | splice |

These are read by the daemon when it starts, from the environment of whichever command
started it. To change one, run `cargo rustd stop` first.

| Variable | Meaning | Default |
|---|---|---|
| `RUSTD_HOME` | the daemon's directory (also read by every client) | see above |
| `RUSTD_IDLE_SECS` | seconds without a request before the daemon exits; 0 is never | 1800 |
| `RUSTD_CACHE` | directory of the disk store; without it nothing is kept on disk | not set |
| `RUSTD_REMOTE` and the other store variables | see [cache.md](cache.md) | not set |

The disk store is off unless `RUSTD_CACHE` is set. That is easy to miss: a daemon started by
a shell without the variable keeps no store, whatever later shells have set.

## Known problems

- **The daemon builds programs rustc would reject.** It refuses source in which
  rust-analyzer finds an error, and those builds fail. It has no borrow checker, so
  a borrow or move error is not found: with a warm daemon, `cargo rustd run` built and ran
  a program that uses a value after moving it. Nothing is reported. Run `cargo rustd check` when you want rustc's verdict.
- Linux x86-64 and macOS arm64 have been run; on macOS only ripgrep, fd and hyperfine and
  the generated workspace of the harness. The code compiles for Windows, but every build
  there fails (the link step knows ELF and Mach-O), and the command has not
  been built or run there. The socket's permission and peer checks do nothing on Windows.
- On Linux `cargo rustd` was measured with the Cranelift backend only; LLVM has been run
  through the harness gate, not through `harness/cargo_rustd.py`. On macOS the harness was
  run under both.
- In ten runs of just's test suite through `harness/cargo_rustd.py` there were two
  differences from cargo that are not explained. One was a test failing in the
  daemon-built executable and passing under cargo. The other was between two executables
  cargo built, which points at the tests being sensitive to load, but that was not shown.
- A function rustc emitted no symbol for is assumed to be dead code. One bug came from that
  assumption being wrong (test functions, fixed); no other is known, and it is not proved
  that there is none.
- The check that only your user can reach the daemon is tested for the same user only.
- `cargo rustd` is not in the CI workflow. `harness/cargo_rustd.py` needs the network and
  about 20 minutes.

## Plain `cargo`, switched on globally

`cargo rustd` needs whoever runs the build to type something different. The global switch is
for when they won't: agents, scripts, editors that call `cargo build` themselves.

    rustd enable     # plain cargo now goes through rustd, for this user
    rustd status     # is it on, and what the daemon served or left to rustc
    rustd disable    # back to how it was

`rustd`, `cargo-rustd`, `rustd-rustc` and `rustd-rustc-first` have to be in the same directory.

Plain `cargo build`, `cargo run` and `cargo test` do not build a workspace while rustd is
enabled: they fail at its first crate with `plain cargo does not build a workspace while rustd
is enabled; \`cargo rustd ...\` builds it`. Build scripts, proc macros and registry crates are
rustc's as before; no other crate of the workspace is compiled by rustc.

### What `enable` changes

One key in `$CARGO_HOME/config.toml` (usually `~/.cargo/config.toml`):

    [build]
    rustc-workspace-wrapper = "<dir>/rustd-rustc"

No shell profile or environment variable is touched. `enable` keeps a copy of the file as it
was in `rustd-enabled.json` next to it. `disable` restores that copy byte for byte, or, if
you edited the file in between, removes only its own line.

### Wrappers you already have

- `build.rustc-wrapper` or `RUSTC_WRAPPER` (sccache and the like) is left alone and runs
  around `rustd-rustc`.
- An existing `rustc-workspace-wrapper` is chained: `rustd-rustc` runs rustc through it, and
  `disable` puts your line back.
- `enable` and `status` print both, so you can see what will run.

A `RUSTC_WORKSPACE_WRAPPER` in the environment, or a project `.cargo/config.toml` that sets
the key, takes precedence over the user config. rustd is not used in that workspace, and
`rustd status` run there says so.

### What you get, and what you don't

The daemon, its loaded workspaces, the sharing between worktrees and the store are the same
ones `cargo rustd` uses. The difference is where rustd sits. Cargo still plans the build and
calls the wrapper once per crate; the daemon answers for programs and test executables, and
workspace library crates are still compiled by rustc. A build with nothing to do costs what
cargo's own no-op costs.

When the daemon cannot serve a unit, rustc builds it and one line on stderr says why:

    rustd: the daemon had not loaded the build yet; rustc links `app`

`rustd status` counts these by reason. A build never fails because rustd is enabled: a
daemon that is missing, dies during the build, or is another version (it gets replaced) all
end in rustc doing the work. An error rustd cannot diagnose itself, such as a use after
move, fails with rustc's message and status 101, as under cargo.

The store is on by default in this mode and in `cargo rustd`: `$XDG_CACHE_HOME/rustd/store`,
else `~/.cache/rustd/store`, limited to 8 GiB. `RUSTD_CACHE=<dir>` moves it, `RUSTD_CACHE=off`
disables it, `RUSTD_CACHE_MAX` sets the limit. The socket and logs are in
`$XDG_RUNTIME_DIR/rustd`, else `~/.cache/rustd`.

### What has been checked

On Linux x86-64, under both backends, with a generated workspace, each of these gave the
same output, exit status and test results as cargo alone on the first build, a warm build
and a build after an edit: `cargo test`, `test --doc`, `test --no-fail-fast` with a failing
test, `run --example`, `run --release`, `run --target <host>`, `run --bin`,
`run --features -p`, `check`, `check --all-targets`, `build --workspace --all-targets`,
`cargo install --path`, and a `cargo check --message-format=json` running beside a build.
Also: 12 builds at once over 3 worktrees on one daemon, the daemon killed during a build,
both kinds of user wrapper, and the `enable`/`disable` round trip. ripgrep, fd and hyperfine
match cargo on every step. `harness/cargo_rustd.py` runs all of this.

Not checked: a proc macro defined in the workspace, `--target` for another triple,
`cargo install` from the registry, a real rust-analyzer session next to it, real sccache (a
stand-in wrapper was used). On Windows every build is cargo's in this mode and nothing was
run. macOS arm64 is below.

### Known problems

- Edits are slower than with `cargo rustd`, and on four of nine projects slower than cargo
  alone (one run each, Cranelift: ripgrep 1.32 s against 0.78 s, eza 2.02 against 1.32,
  tokei 1.23 against 0.70, axum 0.68 against 0.41). The cause has not been measured yet.
- The store grows fast: one harness pass over starship wrote 7.6 GiB.
- A socket path over 108 bytes cannot be bound; the build fails and says so. The default
  locations are well under that.


## macOS arm64

`cargo rustd` and plain cargo after `rustd enable` serve dev and test builds for
`aarch64-apple-darwin`. x86-64 macOS is not a target rustd knows, so builds for it are
cargo's.

Two things differ from Linux. Apple's linker has no way to let the first of two
definitions win, so the daemon links rustc's line with copies of the workspace's objects in
which every definition is weak, and its own object in front; this is the link the daemon
already did on macOS, and the line also gets `-Wl,-headerpad,0x200` so that the executable
can be spliced later. And there is no `/proc`: in the global mode, the cargo above the
wrapper is read through `libproc` and `sysctl`.

What was run, on an 8-CPU Apple M4 virtual machine with macOS 26.5 and Rust 1.99.0:
`harness/cargo_rustd.py --small`, under Cranelift and under LLVM (`RUSTD_OPT=2`,
`RUSTD_EMIT=fast`). Under each it passed: ripgrep, fd and hyperfine gave the same output,
exit status and test results as cargo alone on every step of both modes (134 comparisons),
and the 101 checks of the flags, the daemon and plain cargo held. Those include the
`enable`/`disable` round trip of `config.toml`, byte for byte, over five configurations, and
the second user at the socket, for which the harness uses `nobody` on macOS.

Seconds for the build after an edit, rustd / cargo alone, one run each:

| Project | `cargo rustd`, Cranelift | `cargo rustd`, LLVM | plain cargo, Cranelift | plain cargo, LLVM |
|---|---:|---:|---:|---:|
| ripgrep 15.1.0 | 2.08 / 1.43 | 0.40 / 0.67 | 1.35 / 0.97 | 1.07 / 0.69 |
| fd 10.3.0 | 0.24 / 0.42 | 0.25 / 0.43 | 0.26 / 0.42 | 0.29 / 0.42 |
| hyperfine 1.19.0 | 0.34 / 0.35 | 0.21 / 0.33 | 0.24 / 0.34 | 0.23 / 0.34 |

The ripgrep numbers are not steady. Two earlier Cranelift runs of the same step on the same
machine gave 0.52 / 0.73 and 1.08 / 1.30 for `cargo rustd`, and 1.86 / 0.78 and 1.30 / 1.30
for plain cargo; in every run the daemon did that build, and under plain cargo it was not
faster than cargo. Why ripgrep's edit takes one to two seconds in some runs was not looked
into. A build with no change took 0.03 to 0.06 s through `cargo rustd` against 0.31 to
0.41 s, and 0.16 to 0.19 s through plain cargo.

These runs predate the daemon's first build being the only one. Builds that went to cargo
in them, each with its reason printed: the first build of
every project, the build of source that does not compile, ripgrep's tests after an edit
under `cargo rustd` (a library the unit tests are linked with as rustc built it), and the
tests of ripgrep and hyperfine after an edit under plain cargo ("the build is not one the
daemon has loaded").

Not run on macOS: the projects of the harness other than those three, `cargo rustd` with
debug info looked at in a debugger, and anything on x86-64.
