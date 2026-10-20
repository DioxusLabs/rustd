# rustd

rustd is a Rust compiler daemon. One process per user stays running, keeps rust-analyzer's
analysis of your workspaces in memory and, when given a directory, compiled functions in a
store on disk, and answers builds from that state. After an edit it compiles the functions
that changed, with Cranelift or LLVM, and either links them in front of what rustc built or
splices them into the executable that is already there.

cargo and rustc start from the file system on every build: they parse, resolve, type-check
and generate code for a whole crate again when one function in it changed, and a second
checkout of the same repository starts from nothing. rustd keeps that work. Git worktrees of
one repository share one database, and a function compiled once is found again by the hash of
what it was compiled from, in any workspace on the machine or, through an S3 bucket, on
another machine.

It is meant for people and coding agents who build the same code many times, often in several
worktrees at once.

## Status

This is a prototype, published for the first time. Nobody outside the project has used it.
Read this section before relying on it.

- It was written largely with AI assistance under human direction. What stands behind it
  is the testing: every change is judged by comparing rustd's output with rustc's
  ([docs/harness.md](docs/harness.md)).
- rustc is still required. It builds the crates the workspace depends on, through cargo,
  so the usual caches of those (sccache, a CI cache) still apply. The workspace's own
  crates are rustd's from the first build on, except build scripts, proc-macro crates and
  what those depend on, which run inside cargo and rustc. rustd does not produce `.rlib`
  or `.rmeta` files.
- Once the daemon has a workspace, rustc does not run on an edit at all: no `cargo check`
  beside the build, so nothing competes with it for the CPU. The price is diagnostics.
  rustd refuses source in which rust-analyzer finds a type or name error, and says each
  as `path:line:column: message [E0308]`; the wording is rust-analyzer's, not rustc's. It has no borrow checker: a use after a move, a missing
  `mut` or a reference that outlives its value is built and run. `cargo rustd check` is
  `cargo check` and gives rustc's verdict.
- It never falls back. A function the daemon cannot compile fails the build with the
  function and the reason, and so does a command it does not build, such as
  `cargo rustd test` today: see [What is not supported](#what-is-not-supported). No build
  of the workspace is handed to cargo.
- It is pinned to one toolchain, Rust 1.99.0. It links against rustc's output, so it has to
  agree with that rustc on symbol names, type layout and the unstable Rust ABI.
- `cargo rustd` builds programs on Linux (ELF) and on macOS arm64 (Mach-O), in any profile
  and with `RUSTFLAGS`; other targets fail the build. On macOS it has been run on ripgrep, fd and hyperfine only. The command has not
  been built or run on Windows; the daemon underneath it has, through the harnesses.
- The code rustd generates is for the edit loop. Each function is compiled alone and nothing
  is inlined across functions, under either backend.
- It has been wrong: a fuzzer found twenty-one problems, most of them miscompiles. Four
  known differences from rustc are open and listed in [docs/support.md](docs/support.md).

## Install

On macOS arm64, Linux x86-64 and Linux AArch64:

    curl -fsSL https://dioxuslabs.github.io/rustd/install.sh | sh

On Windows x86-64, in PowerShell:

    irm https://dioxuslabs.github.io/rustd/install.ps1 | iex

The script downloads the latest [release](https://github.com/DioxusLabs/rustd/releases),
checks it against the release's SHA-256 sums and puts `rustd`, `cargo-rustd` and
`rustd-rustc` in `~/.cargo/bin`. `RUSTD_VERSION=nightly` takes the newest build of `main`
instead. You still need Rust 1.99.0 with `rust-src`:

    rustup toolchain install 1.99.0 --component rust-src

The released binaries have the Cranelift backend only. The LLVM backend links LLVM 20 from
the machine it runs on, so it is built from source.

## Build from source

You need Rust 1.99.0 with the `rust-src` component. LLVM 20 is optional and adds the LLVM
backend.

    rustup toolchain install 1.99.0 --component rust-src
    git clone --recursive https://github.com/DioxusLabs/rustd
    cd rustd
    cargo +1.99.0 build -p rustd --release

`vendor/rust-analyzer` is a submodule: rust-analyzer with rustd's changes to it, kept on the
`rust-analyzer` branch of this repository. If you cloned without `--recursive`, run
`git submodule update --init`. With LLVM 20 installed (on Debian and
Ubuntu, `llvm-20-dev` and `libpolly-20-dev` from apt.llvm.org):

    LLVM_SYS_201_PREFIX=/usr/lib/llvm-20 cargo +1.99.0 build -p rustd --release --features llvm

The build leaves `rustd`, `cargo-rustd`, `rustd-rustc` and `rustd-rustc-first` in
`target/release`. Put all four in one directory on your `PATH`; each runs the others from next
to itself.

    cp target/release/{rustd,cargo-rustd,rustd-rustc,rustd-rustc-first} ~/.cargo/bin/

## Quick start

### `cargo rustd`

In any cargo project, with 1.99.0 as the toolchain:

    cargo rustd build
    cargo rustd run -- --some-flag
    cargo rustd test
    cargo rustd check

The first build of a workspace is shared: cargo has rustc build the dependencies while the
daemon loads the workspace, and the daemon then compiles the workspace's crates and links
the program. After that an edit is compiled by the daemon and neither cargo nor rustc
runs. A change to a manifest, `Cargo.lock` or the cargo configuration starts over the same
way: rustc for the dependencies that changed, the daemon for the workspace.
`cargo rustd status` shows what the daemon holds and how many builds it served.
`cargo rustd stop` ends it; it also exits by itself after 30 minutes without a request.
`cargo rustd check` is `cargo check`.

Compiled functions are kept on disk in `~/.cache/rustd/store` (8 GiB at most;
`RUSTD_CACHE=off` turns it off), so a new daemon starts from what the last one built. See [docs/cache.md](docs/cache.md) for the store and the S3 remote.

### Plain `cargo`, switched on globally

Run `rustd enable` once. It adds one key to `~/.cargo/config.toml`
(`build.rustc-workspace-wrapper`, pointing at `rustd-rustc`), and from then on ordinary
`cargo build`, `cargo run` and `cargo test` fail at the first crate of a workspace and name
the `cargo rustd` command that builds it: the daemon is not driven by plain cargo yet. `rustd disable` puts the file back as it was. `rustd status` says whether it is on.

    $ rustd enable
    $ cargo run            # error: ... `cargo rustd run` builds it
    $ rustd disable

`rustd`, `cargo-rustd`, `rustd-rustc` and `rustd-rustc-first` have to be installed in the same
directory. A wrapper you already use, such as sccache, keeps running.
Having plain cargo wait for the daemon, for agents and scripts that call cargo themselves, is
not built yet; see [docs/cargo.md](docs/cargo.md).

## Results

Linux x86-64, 8 CPUs, Cranelift, seconds, plain cargo first and rustd second. Both sides
use the same linker, cargo is warm and incremental, the daemon is warm, and the program
both produce is run and compared. Since these were measured no `cargo check` runs beside
a rustd build and nothing is handed back to cargo, so numbers published earlier, which
included a `cargo check` on every edit, no longer apply and have been removed.

Edits in a generated workspace of 200 crates (`harness/genws.py`, timed by
`harness/editrows.py`), median of three:

| Edit | cargo | rustd | |
|---|---:|---:|---:|
| A function body in the program's crate | 1.76 | 0.42 | 4.2x |
| A function body in the crate every other depends on | 6.33 | 0.60 | 10.6x |
| Function bodies in 30 crates at once | 6.26 | 0.62 | 10.1x |
| A new function | 2.09 | 0.56 | 3.7x |
| A signature whose callers are in every crate | 13.87 | 10.87 | 1.3x |

The rows were run in that order in one daemon, and the first again after the last (1.79
against 0.45). The last row is barely ahead: the edit changes 2,390 files and the daemon
recompiles 6,806 functions, 3 s of it before compiling anything. That is open.

Real projects, one run each, from `harness/cargo_rustd.py --small`. The edit adds a line
to a function:

| Project | No-change build | Build after an edit |
|---|---:|---:|
| ripgrep 15.1.0 | 0.42 / 0.02 | 1.28 / 0.36 |
| fd 10.3.0 | 0.41 / 0.03 | 0.52 / 0.17 |
| hyperfine 1.19.0 | 0.33 / 0.03 | 0.36 / 0.15 |

Most of rustd's time in the second column is the client and the link; the daemon's own
time from the edit to a linked ripgrep was 0.05 s when measured alone.

First build from an empty target directory, where cargo builds
the dependencies and rustd the workspace's crates, one run each except nushell:

| Project | `cargo build` | `cargo rustd build` |
|---|---:|---:|
| ripgrep 15.1.0 | 5.43 | 6.05 |
| fd 10.3.0 | 20.5 | 22.0 |
| nushell 0.108.0 | 42.7, 42.9 | 66.4, 68.1, 89.9 |

rustd is behind on all three, and far behind on nushell, where it compiles 165,000
functions. The nushell it links answered 80 of 80 test commands as cargo's does.
bat, just, axum and nushell edits have not been measured again since the change and are
left out.

The same step on macOS arm64 (8-CPU Apple M4 virtual machine), one run each, from
`harness/cargo_rustd.py --small`:

| Project | No-change build | Build after an edit, Cranelift | Build after an edit, LLVM |
|---|---:|---:|---:|
| ripgrep 15.1.0 | 0.06 / 0.39 | 2.08 / 1.43 | 0.40 / 0.67 |
| fd 10.3.0 | 0.05 / 0.41 | 0.24 / 0.42 | 0.25 / 0.43 |
| hyperfine 1.19.0 | 0.04 / 0.32 | 0.34 / 0.35 | 0.21 / 0.33 |

ripgrep's edit build varied between runs there (0.52 / 0.73 and 1.08 / 1.30 in two other
Cranelift runs); see [docs/cargo.md](docs/cargo.md#macos-arm64).

On nushell the daemon needs 36 to 51 s to load again after a manifest or build script
changes, and builds are cargo's for that long (measured before the change above).

Correctness is measured by building the same program with rustc and with rustd and comparing
what they do. On the last CI run that covered all four native platforms, every function of
the test corpus was compiled by rustd under both backends and no type layout differed from
rustc's (822 functions on Linux x86-64, 825 on Linux AArch64, 830 on Windows, 828 on macOS).
Of rustc's own `tests/ui` run-pass tests, 2686 of 2690 behave the same under Cranelift; 1114
were left out, for reasons listed in the results.

## What is supported

| | Linux x86-64 | Linux AArch64 | Windows x86-64 MSVC | macOS arm64 | wasm32 |
|---|---|---|---|---|---|
| Cranelift | yes | yes | yes | yes | no (own lowering) |
| LLVM | yes | yes | yes | yes | no |
| Full link | yes | yes | yes | yes | older branch only |
| Splice | yes | yes | yes | yes, not with chained fixups | older branch only |
| Debug info | yes | yes | lines only | unverified | no |
| `cargo rustd` | yes | unverified | not run | yes, three projects | no |
| Disk store | yes | yes | yes | yes | unverified |
| S3 remote | yes, not real AWS | unverified | unverified | unverified | unverified |

"yes" means a harness passes there and a report says where it ran. The wasm32 column was
measured on an earlier branch with a nightly toolchain and has not been run since.
[docs/support.md](docs/support.md) has the source of every cell and the same for language and
build-model features.

## What is not supported

These fail the build with an error that names them; `cargo rustd` hands nothing to cargo
([docs/cargo.md](docs/cargo.md#what-fails-the-build) has the list):

- `--benches`, `--bench` and `--all-targets`, which build benchmarks;
- `lto = true` or `"thin"`;
- more than one `--target`, a JSON `--message-format`, `-Z` flags, and a
  `RUSTC_WORKSPACE_WRAPPER` that names another wrapper;
- workspace crates built as `cdylib`, `dylib` or `staticlib`.

Plain cargo after `rustd enable` fails at the first crate of a workspace and names the
`cargo rustd` command that builds it; rustc never compiles the workspace.

So do a few language features, among them
`sym` operands in `asm!` that is not naked, some variadic function definitions, and vectors
in a C ABI.

Not there at all: rustc's diagnostics and the borrow checker, optimised output comparable to `--release`, types and
variables in Windows debug info, and targets other than the ones in the table.

## rust-analyzer

rustd's front end is rust-analyzer: its parser, name resolution, type inference, MIR,
monomorphisation, layout and const evaluation, and its cargo workspace loading. rustd adds a
code generator on top of rust-analyzer's MIR and the daemon around it. rust-analyzer is
included as a submodule. It points at the `rust-analyzer` branch of this repository, which is
upstream rust-analyzer at the commit rustd forked from with rustd's changes committed on top. None of this would exist without the rust-analyzer team's work.
rustd is not part of the rust-analyzer project and is not endorsed by it; please do not
report rustd problems there.

Type layout is computed with rustc's own `rustc_abi` crate, copied unchanged from the 1.99.0
tag into `vendor/rustc_abi`.

## Licence

MIT or Apache-2.0, at your option, the same as rust-analyzer and rustc. See
[LICENSE-MIT](LICENSE-MIT) and [LICENSE-APACHE](LICENSE-APACHE).

## Documentation

- [docs/cargo.md](docs/cargo.md): using `cargo rustd`
- [docs/support.md](docs/support.md): the support matrix
- [docs/platforms.md](docs/platforms.md): the state of each platform
- [docs/cache.md](docs/cache.md): the disk store and the S3 remote
- [docs/architecture.md](docs/architecture.md): how it works
- [docs/results.md](docs/results.md): measurements and where each came from
- [docs/harness.md](docs/harness.md): the test harnesses
- [docs/fuzzing.md](docs/fuzzing.md): the differential fuzzer
- [docs/contributing.md](docs/contributing.md): layout, changing rust-analyzer, moving to a newer one
- [SECURITY.md](SECURITY.md): reporting a problem, and what the daemon and a shared store trust
- `docs/reports/`: the working reports the above were written from
