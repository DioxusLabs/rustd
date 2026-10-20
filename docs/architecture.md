# How rustd works

This is a map of the code for someone who wants to read or change it. Paths are those of the
published tree: `crates/rustd` is the daemon, `crates/hir-ty-codegen` is the code generator
(it is compiled as the module `hir_ty::mir::codegen` of rustd's rust-analyzer branch, see
[contributing.md](contributing.md)), and `vendor/rust-analyzer` is the front end.

## The idea

rustc is a batch compiler. Each invocation reads a crate's source and its dependencies'
metadata, does the whole pipeline, writes files and exits. Cargo decides which crates to
run it on from file timestamps and fingerprints. Incremental compilation saves part of the
work by writing rustc's state to disk and reading it back, per crate, per target directory.

rust-analyzer is the opposite shape. It is a long-running process built on a query database
(salsa) that holds the parsed, name-resolved and type-checked program in memory and
recomputes only what an edit invalidates. It already lowers function bodies to MIR,
monomorphises them, computes type layouts and evaluates constants, because the IDE needs
those for const evaluation and hover.

rustd adds the missing last step, from rust-analyzer's MIR to machine code, and keeps the
process running as a build daemon. An edit then costs what the database has to redo plus
the code of the functions that actually changed.

## The rule

**rustc is the reference.** A program built with rustd's code must behave as the one rustc
built. Where they differ, rustd is wrong.

**Never guess; refuse visibly.** The code generator returns "unsupported" with a reason for
anything it has no explicit lowering for. A refused function fails the build, with the
function and the reason; it is never left to cargo. A refusal is printed, counted
and listed (`--report`, `cargo rustd status`); it is treated as a bug to fix, not as a
normal path. What must not happen is a best-effort lowering of input the generator does not
understand, because that is wrong code nobody sees.

The same rule shapes the smaller pieces. `type_id.rs` computes `TypeId` hashes the way the
pinned rustc does and returns `None` for a type whose hash needs something it does not
reproduce. The splice returns an error for anything it has no answer for and the caller
links in full. When an input cargo acts on changes (a manifest, the lockfile, a build script), `cargo rustd`
has cargo run again for the dependencies and the scripts, and the daemon reloads the
workspace and builds its crates.

## Processes

    cargo rustd build ──► rustd cargo (client) ──► rustd daemon ──► worker: rustd <project> --socket
                              │                         │                │
                              └── cargo + rustc         └── more workers └── one database
                                  (dependencies, build scripts)

The **client** (`crates/rustd/src/cargo/`, entry in `mod.rs`) is what `cargo rustd` runs.
It parses the command line (`cli.rs`), decides whether the daemon can serve it (`state.rs`),
and either asks the daemon or runs cargo.

The **daemon** (`cargo/daemon.rs`) is one process per user on a Unix socket
(`socket.rs`). It loads nothing. It starts workers, passes requests to them, and stops them
and itself when idle. Requests and answers are one JSON object per line.

A **worker** is `rustd <project> --socket <path>`, the long-running mode of `main.rs`. It
holds one rust-analyzer database. A worker is keyed by repository, toolchain, target,
feature set and whether libraries are built with `cfg(test)`, because those are inputs of
loading. Checkouts of one repository join the same worker; another repository gets its own,
so a crash or reload of one does not cost the other its state. A worker exits when the
daemon's end of its standard input closes.

The same worker binary is what the harnesses drive directly, without cargo's wrapper:
`rustd <project> --crate <name> --out <object> --symbols <rlib>... --link-cmd <cmd>
--socket <path>`, then `rustd sync <socket>` to ask for a build. There is no `--help`; the
flags are parsed in `main.rs`.

## The database and what worktrees share

A worker loads a cargo workspace through rust-analyzer's `load-cargo` and
`project-model`, including build script output and proc-macro expansion through
rust-analyzer's proc-macro server. Source changes arrive either from a file watcher or,
under `cargo rustd`, are looked for when a build is requested (`tree.rs` finds added and
removed files by directory timestamps).

A second checkout of the same repository is added to the same database (`--also`, or a
`--project` request to the socket). Crates are identified by their content
(`content.rs`): two checkouts with the same source for a crate have the same crate, and what
was analysed and compiled for one is used for the other. Only the crates that differ, and
the crates that depend on them, exist twice. `harness/worktrees.py` tests this with several
checkouts edited independently under one daemon.

Besides source, a checkout is loaded from its manifests, lock file, cargo configuration,
`RUSTFLAGS` and what its build scripts read. `inputs.rs` checks before each build whether
those are still what was loaded, reruns build scripts where cargo would, and says which
checkouts must be loaded again.

`outline.rs` tells an edit that only changes function bodies from one the rest of the
program can see. After a body-only edit, only what comes from the edited file needs
another look. A body counts as visible when it belongs to a `const fn`, when its type is
part of its signature (`async fn`, `-> impl Trait`), when it is handed to a macro, or when
it declares items.

## From MIR to code

The code generator is `crates/hir-ty-codegen`. `codegen.rs` lowers one monomorphised MIR
body to Cranelift IR. Every local lives in memory. Layout comes from rustc's own
`rustc_abi` crate, and calls follow rustc's unstable Rust ABI for the pinned toolchain, so
that rustd's functions and rustc's can call each other. Vtables (`vtable.rs`), `TypeId`s
(`type_id.rs`) and unwind tables (`unwind.rs`, with `unwind/seh.rs` for Windows) have to
agree with rustc's for the same reason: objects, trait objects and panics cross between the
two compilers' code in both directions.

### One function, one result

Compiling a function is a database query (`fragment.rs`). Its result is machine code that
names the functions and data it uses by what they are, not by where an object file put
them. That makes the result depend on the database alone, so salsa can keep it and reuse it
after an unrelated edit, and a build is the stitching of those results into an object.

An instance of a generic function is compiled from the point of view of the crate its name
mentions, not the crate that asked for it (`home.rs`). Otherwise `Vec<u8>::push` would
depend on every file of whichever workspace crate used it.

### The boundary above the producers

`backend.rs` defines the boundary. Above it, the front half has built Cranelift IR for one
function with layout and calling convention already decided. Below it, a producer returns a
`Code`: bytes, the relocations in them, and how to unwind through them. Nothing after that
can tell which producer made the code.

- **Cranelift** is the default. It compiles the IR directly.
- **LLVM** (`llvm.rs`, `llvm/lower.rs`, `llvm/emitted.rs`; behind the `llvm` cargo feature
  and `RUSTD_BACKEND=llvm`) translates the Cranelift IR of the function into an LLVM module
  holding that one function, optimises it at `RUSTD_OPT`, has LLVM write an object into
  memory, and reads the code, constants, relocations and unwind table back out of it.
  Functions are compiled alone at every level, so nothing is inlined across functions. A
  function LLVM has no lowering for is given to Cranelift, with the reason recorded.
- **wasm** (`wasm.rs`, `wasm_object.rs`). Cranelift has no WebAssembly backend, so for
  `wasm32` targets a hand-written lowering turns the same Cranelift IR into a wasm function
  body, and an object writer emits a relocatable wasm object that `wasm-ld` links. No
  unwinding is emitted; the wasm targets are `panic=abort`.

`asm!` blocks are assembled separately and called as functions of their own, as rustc's
Cranelift backend does (`asm.rs`).

### Targets

The target is an input of the process (`target.rs`): `--target <triple>`, else the host.
Everything platform-dependent asks the `Target` for architecture, object format, calling
convention and unwind format, and never asks what rustd itself was built for. The parser
accepts x86-64, AArch64 and wasm32 with ELF, Mach-O, COFF or wasm objects. What has been
run on each is in [support.md](support.md), and how each port works is in
[platforms.md](platforms.md).

## Linking and splicing

rustd does not produce a program from nothing. rustc and cargo build it once, and rustd
replaces the code of the crates it was asked to compile.

**Full link.** rustd writes one object with its functions and runs rustc's own link line
with that object placed ahead of rustc's rlibs for the same crates. Both define the same
symbols and rustd's must win. An ELF linker and `link.exe` can be told to keep the first
definition. Apple's linker cannot, so there `rustd weaken` makes copies of rustc's objects
whose definitions are weak (`weaken.rs`). `symbols.rs` maps Rust paths to the mangled names
rustc used, read from rustc's rlibs and objects.

**Patch.** After an edit the object of the last full build stays as it is and a small
object holding the changed functions is linked ahead of it (`patch.rs`). Anything the patch
cannot express starts a full object again.

**Splice.** Linking still rewrites the whole executable. The splice
(`crates/rustd/src/splice.rs`) leaves the executable of the last full link as it is and
appends the patch: it lays the patch out behind everything the linker loaded, resolves its
references against the executable's symbols, and writes a jump to the new code over the
entry of each replaced function. Calls, vtables and function pointers still arrive at the
old entry and continue to the new code. A static with a new value is written in place when
it is no larger. Each splice starts from the executable as the linker left it, so splices
do not accumulate. Anything the splice has no answer for is an error and the daemon links in
full; `RUSTD_SPLICE=0` turns it off.

Each object format has its own implementation:

| Format | File | Notes |
|---|---|---|
| ELF | `splice.rs`, `splice/debug.rs` | New segments for read-only data, code and data, new program headers, the unwinder's search table extended. Debug sections are rewritten so a debugger sees the new code. |
| Mach-O arm64 | `splice/macho.rs` | The patch goes where `__LINKEDIT` was, `__LINKEDIT` is written again behind it, and the file is re-signed. Executables with chained fixups are declined. |
| PE x86-64 | `splice/pe.rs` | New sections behind the linker's last, `.pdata` extended for the unwinder. |
| wasm | `splice/wasm.rs` | Nothing jumps: the module is written again with the new function bodies under the same indices. |

## The disk store

`store.rs` is a content-addressed key-value store of compiled functions, independent of
Rust: a key is a hash of what the value was made from. It is used when `RUSTD_CACHE` names
a directory. `stable.rs` gives function instances names that are the same in every run on
the same sources, and `cached.rs` keeps entries under them: a function of a crate that no
edit reaches, as it was stitched into an object. A build that finds an entry for an
instance and for everything it calls puts them in the object without asking the database
about the instance.

On disk the store is a set of immutable packs named by the SHA-256 of their bytes, plus one
open pack per running daemon. Format, locking, integrity checks and size limits are in
[cache.md](cache.md).

## The remote store

`crates/rustd/src/remote.rs` and `remote/` keep a local store in step with a directory or
an S3 bucket. Because packs are immutable and named by their hash, a remote is a set of
pack files, a key list per pack, and a manifest per project. `transfer.rs` moves one object
so that the local file is either complete or absent; `s3.rs` is the bucket through the AWS
SDK; `signed.rs` signs and checks manifests; `collect.rs` is garbage collection;
`keeper.rs` is the background task that pulls and pushes while a daemon runs. `deps.rs`
does the same for what cargo built of registry dependencies.

## The cargo drop-in and the unit graph

`cargo rustd` needs three things from cargo for every program: the rlibs and objects rustc
built, the line rustc ran the linker with, and which workspace crates are in the program.
It gets them by being cargo's `RUSTC_WORKSPACE_WRAPPER` on the first build
(`cargo/wrapper.rs`). Cargo runs the wrapper in place of rustc for every workspace crate
and for no registry crate. The wrapper runs rustc as asked, adding
`--print link-args=FILE -C save-temps` for crates linked into an executable, and writes a
record of the unit: the arguments, and copies of the files a later cargo build would
overwrite (`cargo/units.rs`). The daemon reads and links against the copies, so a cargo
build beside it never changes a file under it.

From those records `cargo/plan.rs` works out what the daemon is asked to build a program
from: its workspace crates, the files to read symbols from, and rustc's link line with the
daemon's objects ahead of rustc's. `crates/rustd/src/plan.rs` computes the units of a build
with the features and profile settings of each, which `cargo metadata` does not give per
build.

`cargo/state.rs` records what a cargo build left and everything whose change makes the next
build cargo's again: manifests, lock file, cargo configuration, toolchain, environment
variables rustc reported reading, and build script inputs. `cargo/script.rs` reruns
workspace build scripts the way cargo does and compares what they printed and wrote; if
that is unchanged, the build stays the daemon's.

The daemon assumes the source it loads is the source rustc compiled. The client records the
time just before cargo starts. When a worker has loaded, the daemon checks that no source
file rustc read is newer than that, and discards the worker if one is.

An alternative wrapper exists in `stub.rs` (`RUSTD_WRAPS_RUSTC`), where rustc compiles only
a stub for each workspace crate and all code is rustd's. It makes the first build faster,
but a function rustd refuses then has no rustc copy to fall back on, so it is used by
`harness/alone.py` and not by `cargo rustd`.

## Debug info

`debuginfo.rs` writes DWARF 4 for rustd's functions: line tables, a subprogram entry per
function, and under Cranelift the parameters and locals. Debug info is written for ELF
targets. It is not written for Windows, and has not been checked on macOS. See
[support.md](support.md).

## rustd in the browser

`crates/rustd-wasm` is an experiment that builds the compiler itself for wasm and runs it in
a web page. It is excluded from the workspace and is not part of the daemon. See
[reports/WASM.md](reports/WASM.md). The website runs a small
version of it: [playground.md](playground.md).
