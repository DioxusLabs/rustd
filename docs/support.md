# What is supported

Every cell here points at a report or a harness run. "CI" is GitHub Actions run
39057174862 on commit 888e87df74, the last run recorded in the reports that covered all
four native platforms under both backends ([reports/PLAT-ABI2.md](reports/PLAT-ABI2.md)).
"Local" is a run of the gate on Linux x86-64 at f191c6e42a, the commit these docs were
written against, under both backends (see [results.md](results.md)). [platforms.md](platforms.md) describes each port. "Unverified" means
nobody recorded running it; it does not mean it is known to fail.

"Yes" has a narrow meaning: the named harness passes there. It does not mean your project
will build without fallbacks.

## Toolchain

Rust 1.99.0 only. rustd links against what rustc built, so it must agree with that rustc on
symbol mangling, type layout, the unstable Rust ABI, vtable layout and `TypeId` hashes. The
layout code is rustc's own `rustc_abi` crate from the 1.99.0 tag. Nothing has been run on
another stable version. Some reports were measured on `nightly-2026-05-10` before the move
to stable; those are marked where they are used.

## Platforms

| | Linux x86-64 | Linux AArch64 | Windows x86-64 MSVC | macOS arm64 | wasm32 |
|---|---|---|---|---|---|
| Cranelift | yes (1) | yes (1) | yes (1) | yes (1) | does not apply (2) |
| LLVM | yes (1) | yes (1) | yes (1) | yes (1) | no |
| Full link | yes (1) | yes (1) | yes (1) | yes (1) | yes, older branch (2) |
| Splice | yes (3) | yes (3) | yes (4) | yes, with a limit (5) | yes, older branch (2) |
| Debug info | yes (6) | yes (6) | lines only (7) | unverified (7) | no |
| `cargo rustd` | yes (8) | unverified (9) | no: fails the build (9) | no: fails the build (9) | no |
| Disk store | yes (10) | yes (10) | yes (10) | yes (10) | unverified |
| Remote store | yes, not real AWS (11) | unverified | unverified | unverified | unverified |
| Fuzzed | yes (12) | no | no | no | no |

1. CI: `difftest.py corpus --layouts` compiles every function of the corpus with rustd and
   matches rustc under both backends: 822 of 822 functions on Linux x86-64, 825 of 825 on
   native AArch64, 830 of 830 on Windows, 828 of 828 on macOS, with 0 type layouts
   differing. `programs`, `stress`, `breakers`, `unwinds`, `splices`, `asmedits`,
   `includes`, `worktrees` and `keys` ran on every leg. Under LLVM, `backends.py` reports no
   corpus function left to Cranelift on any of the four. Local: 822 of 822 under both.
2. wasm32 uses its own lowering from Cranelift IR, not Cranelift's or LLVM's code
   generation. [reports/WASM32.md](reports/WASM32.md) measured `wasm32-wasip1` under
   wasmtime on the `rustd-wasm32-target` branch with `nightly-2026-05-10`: corpus MATCH with
   655 of 656 functions from rustd, stress 99 of 99, splices 71 of 71 with 62 spliced. wasm
   is not in CI and nobody has recorded a run since the move to 1.99.0. No unwinding is
   emitted; the wasm targets are `panic=abort`. `wasm32-unknown-unknown` was only exercised
   through one Dioxus page.
3. `splices.py` 71 of 71 in CI on both Linux architectures; `farsplices.py` 6 of 6 on
   AArch64, where a branch reaches only 128 MB. Not every edit can be spliced: about 60 of
   the 71 steps are, and the rest link in full by design (an executable somebody else
   wrote, a static that grew, a running executable, and similar).
4. [platforms.md](platforms.md), Windows: 71 of 71 with 61 spliced and 10 full links,
   and the harness fails on Windows if the count is not 61.
5. [platforms.md](platforms.md), macOS: `splices.py` 71 of 71. Executables with chained
   fixups are declined and linked in full; that was measured with
   `MACOSX_DEPLOYMENT_TARGET=13.0`. rustc's default target of 11.0 splices.
6. [reports/DEBUGINFO.md](reports/DEBUGINFO.md) for x86-64 and PLAT-ABI2 for native
   AArch64: `debuginfo.py` passes under both backends. See "Debug info" below for what that
   covers.
7. On Windows rustd writes CodeView procedures and line tables, checked by `debuginfo.py`
   with `llvm-pdbutil` and `cdb` (WINDOWS.md). There are no types, parameters or locals,
   and the PDB is stale after a splice until the next full link. On macOS debug info is
   not checked here.
8. `harness/cargo_rustd.py`, Cranelift only: seven real projects with no difference from
   cargo, 66 of 66 flag steps, 11 of 11 lifecycle checks
   ([reports/CARGO.md](reports/CARGO.md)). Not in CI. Run by hand for these docs on a new
   project and on ripgrep 15.1.0.
9. `cargo rustd` hands any target that is not ELF to cargo (`unsupported_target` in
   `cargo/cli.rs`), and has not been built or run on macOS or Windows. Nobody recorded
   running it on Linux AArch64.
10. CI: `storekills.py`, `storecorrupts.py` and `storeshared.py` on all four platforms.
    `storefull.py` on Linux only. The earlier
    [reports/DISKCACHE.md](reports/DISKCACHE.md) says "Linux x86-64 only"; PLAT-ABI2 is
    later and is what this row follows.
11. `harness/remote.py` against MinIO and SeaweedFS over loopback
    ([reports/REMOTE.md](reports/REMOTE.md)); MinIO runs in the Linux x86-64 CI job. Real
    AWS S3 has not been run.
12. [reports/FUZZ.md](reports/FUZZ.md). Linux x86-64 only; the smoke run is in that CI job.

Other targets. `x86_64-apple-darwin` is refused: with the triple forced through, the link
fails on the unwind table ([platforms.md](platforms.md)). Windows targets other than x86-64 MSVC have
nothing implemented or run. Cross compiling from Linux x86-64 to
`aarch64-unknown-linux-gnu` and `x86_64-unknown-linux-musl` is covered by the build-model
harness below.

## Backends

Cranelift is the default and needs nothing installed. LLVM needs LLVM 20 and a rustd built
with `--features llvm`, and is selected with `RUSTD_BACKEND=llvm`. Everything that was
measured under LLVM used `RUSTD_OPT=2 RUSTD_EMIT=fast`. Other levels are accepted and are
not covered by the gate.

Neither backend inlines one function into another, so LLVM at `-O2` is not comparable to a
release build. LLVM gives a function it has no lowering for to Cranelift. One LLVM bug is
worked around by turning off a vectoriser pass (finding 6 in FUZZ.md).

## Debug info

On ELF, every function rustd compiles is described in DWARF 4 with line tables and a
subprogram entry. Checked on Linux x86-64 and native AArch64: backtraces with
`RUST_BACKTRACE=1` have the same workspace frames as cargo's build, `llvm-dwarfdump
--verify` finds no errors (also after a splice), and gdb stops and steps by line.

What is missing:

- Under LLVM no parameters or locals are described. Under Cranelift they are, without
  lexical scopes, so a local is visible from the start of the function, and a name bound
  more than once is not described at all.
- Enums, unions and closures are described by name and size only.
- Under LLVM at `-O2` a backtrace can have a frame fewer than rustc's, where a tail call
  became a jump.
- `line-tables-only` and `limited` are treated the same as full debug info.
- DWARF 5 and split debug info are not done. An executable with compressed debug sections
  is not spliced.
- After a splice, a breakpoint set by function name can land on the old copy. Breaking by
  file and line finds the new code.

## Language

rustd compiles what rust-analyzer can lower to MIR and what the code generator has an
explicit lowering for. The rest is refused per function, with a reason, and rustc's copy of
that function is used. Measured on rustc's own tests
([reports/RUSTCSUITES.md](reports/RUSTCSUITES.md), Linux x86-64): of the `tests/ui`
run-pass tests that can run on stable, rustd compiled 5558 of 5615 functions and refused
57; in the standard library's test suites it refused 11 of 2846.

Known refusals:

| What | Why |
|---|---|
| `sym` operands in `asm!` that is not naked; `sym` naming a generic function or a thread-local | the block's function has no way yet to carry what its symbols name; generic arguments of a `sym` path are not inferred |
| a naked function whose assembly defines a symbol or has data in another section | not read back from the assembler |
| an `asm!` constant that is not a literal | not lowered |
| some C-variadic definitions: on x86-64 System V a named parameter on the stack or one that is not an integer or float of at most eight bytes; on Windows a named parameter wider than eight bytes and a definition with no named parameter; on AArch64 a named aggregate | each convention's `va_list` is implemented for the common shapes only |
| an argument passed in memory aligned to more than 16 bytes, and a vector in a C ABI | no lowering |
| the `win64` calling convention on Linux | no lowering |
| pattern matching on a union | not lowered from MIR |
| upcasting a `dyn` type with bound regions | not lowered |
| `Location::caller()` in a constant | rustd does not know what file name rustc uses there |
| `type_name` of a function item or of a `dyn` type with a binder | rustc's exact text is not reproduced |
| `%` on floats in a constant; `type_id` of a type with lifetimes in a constant | const evaluation gaps |
| a body in which rust-analyzer's type inference fails or finds errors rustc does not | no MIR, so no code; examples are range patterns over associated constants and an empty array whose element type comes from a single `PartialEq` impl |
| 15 functions of the `generic-array` crate | a trait-solver gap on `GenericArray<T, N>` |

Nightly features are out of scope: rustd is tested against stable 1.99.0.

Known differences from rustc, where rustd does compile the code. These are the cases
marked open in `harness/breakers.py`:

| Case | Difference |
|---|---|
| `assert_message` | `assert!` of a condition longer than a line prints it on one line; rustc breaks it over several |
| `future_unwind_flags` | a future can be one byte smaller than rustc's, because rustc keeps a drop flag rustd does not. Only code that depends on the exact size of a future sees it |
| `raw_write_then_match` | a value written through a raw pointer into a local rustc believes is `None`, then partly moved out, is dropped by rustd and leaked by rustc |
| `fragment_edition_through_macro` | rustd does what rustc's own test says rustc will do once rust-lang/rust#130484 is fixed |

The differential fuzzer found twenty-one problems in generated programs, most of them
miscompiles in the order temporaries are dropped. Twenty are fixed or worked around and one
is the first row above. Nearly every full-size run found something, so expect that more
exist.

rustd has no borrow checker and no diagnostics. The daemon refuses source in which
rust-analyzer finds an error (a type mismatch, an unresolved name, a missing field), and
under `cargo rustd` cargo then runs and rustc reports it. An error rust-analyzer does not
find is not refused. Borrow-check errors are the main case: with a warm daemon,
`cargo rustd run` built and ran a program that uses a `String` after moving it, which rustc
rejects with E0382 (checked by hand at f191c6e42a). Run `cargo rustd check` or
`cargo check` to get rustc's verdict.

## Cargo's build model

There are two layers, and they support different things.

The daemon itself, driven by the harness, follows most of cargo's build model.
`harness/buildmodel.py` has a small project per feature and compares against cargo under
both backends. The latest recorded result is 208 of 208 on Linux x86-64 and 204 of 204 on
native AArch64, where four rows that need an x86-64 host are not run (CI on `51339e5`).
[reports/BUILDMODEL.md](reports/BUILDMODEL.md) has the table at 97 cases per backend, of
which 92 were supported and 5 refused.

`cargo rustd` is narrower. What it does not build fails the build with the reason, as
[cargo.md](cargo.md) lists; nothing of the workspace is handed to cargo.

| Feature | Daemon (`buildmodel.py`) | `cargo rustd` |
|---|---|---|
| dev and test profiles | supported | served |
| release and custom profiles, `opt-level`, `debug-assertions`, `overflow-checks`, `codegen-units`, `strip`, per-package overrides | supported | unverified |
| `panic = "abort"` | supported | unverified |
| `lto = true`, `lto = "thin"` | refused: rustc recompiles the whole program at link time and leaves no library to link rustd's functions against | fails the build |
| `lto = "off"` | supported | unverified |
| crate types `bin`, `lib`, `rlib`, `dylib`, `cdylib`, `staticlib` | supported | programs only; a `cdylib` or `staticlib` that is not linked into an executable has nothing to splice into |
| proc macros (attribute, derive, function-like) | supported: rustc's build of the macro is loaded and its expansion is compiled by rustd | served; the proc-macro crate itself is rustc's, and an edit to it has cargo rebuild it before the daemon reloads |
| build scripts (`rerun-if-changed`, `rerun-if-env-changed`, `rustc-cfg`, `rustc-env`, `rustc-link-lib`, `OUT_DIR`, `links`) | supported | served; the script is rustc's, and a change to it or its inputs has cargo run it again before the daemon reloads |
| unit tests, integration tests, examples, benches | supported | examples served; tests and benches fail the build (`--doc` aside) |
| doctests | supported through `cargo rustd test --doc` and `cargo rustd test` | served: the examples of a library are one crate of the daemon's; an example that needs a crate of its own, a `compile_fail` one rust-analyzer finds no error in, and the examples of a proc macro fail with the reason |
| features, optional and weak dependencies, feature unification under resolvers 1, 2 and 3 | supported | `--features` served; `--all-features` and `--no-default-features` unverified |
| path, git, registry, renamed, vendored, `[patch]` and `[replace]` dependencies | supported | served |
| an edit to a path dependency the daemon was not asked to build | refused with a reason | fails the build |
| `RUSTFLAGS` and `[build] rustflags`, including `-C target-cpu` and `target-feature` | supported | unverified |
| `.cargo/config.toml` `[env]`, `linker`, `runner` | supported | unverified |
| `env!` and `option_env!` | supported, and followed when the variable changes | served; a changed variable that rustc reported reading has cargo run again for the dependencies, and the daemon reloads |
| mixed editions 2015 to 2024 | supported | served |
| `#![no_std]`, `#![no_main]` | supported | unverified |
| cross compilation to `aarch64-unknown-linux-gnu` and `x86_64-unknown-linux-musl` from Linux x86-64 | supported | unverified; a target that is not ELF or Mach-O fails the build |
| manifest, lock file or workspace membership changing under a running daemon (`git checkout` between commits) | supported | cargo builds the dependencies, then the daemon reloads |

"Supported" for a release profile means the program printed the same as cargo's. It does
not mean the code is as fast: rustd's code is not optimised across functions under either
backend.
