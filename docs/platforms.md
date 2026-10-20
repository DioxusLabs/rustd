# Platforms

This is the current state of each platform rustd has been run on, in one place. The
numbers are from GitHub Actions run 39057174862 on commit 888e87df74, the last recorded run
that covered all four native platforms under both backends, unless a line says otherwise.
The report behind it is [reports/PLAT-ABI2.md](reports/PLAT-ABI2.md). The table of what is
supported where is in [support.md](support.md); this page says how each port works and what
is specific to it.

The earlier per-platform reports (first ports, measured on a nightly toolchain, and the ABI
rounds that followed) are superseded by this page and are kept on the development branch
only.

## What is common

The target is an input of the process: `--target <triple>`, else the host. One process has
one target. Everything that differs between platforms asks the `Target` in `target.rs` for
the architecture, object format, calling convention and unwind format.

Three things are implemented once for all platforms and were the subject of the last
round:

- `sym` operands in `naked_asm!` are one MIR operand and one table of relocations with rows
  for ELF x86-64, ELF AArch64, COFF x86-64 and Mach-O arm64.
- A 128-bit integer or an aggregate aligned to 16 bytes that does not fit the remaining
  registers goes to the stack whole, for AAPCS64 and Apple alike. On x86-64 an aggregate
  aligned to 16 bytes on the stack is padded where needed; before that fix it could land
  eight bytes off.
- C-variadic calls and definitions have one model with three conventions: System V,
  Windows, and Apple.

On every platform the gate in CI is the corpus with layouts, programs, stress, breakers,
unwinds, splices, asmedits, includes, worktrees, keys, storekills, storecorrupts and
storeshared, under Cranelift and under LLVM at `-O2` with fast instruction selection.

| Platform | Corpus functions from rustd, both backends | Layouts that differ | LLVM compiled itself |
|---|---|---|---|
| Linux x86-64 | 822 of 822 | 0 of 893 | 11,787 of 11,787 |
| Linux AArch64, native | 825 of 825 | 0 of 903 | 11,813 of 11,813 |
| Windows x86-64 MSVC | 830 of 830 | 0 of 898 | 11,801 of 11,801 |
| macOS arm64 | 828 of 828 | 0 of 914 | 11,879 of 11,879 |

The counts differ because some corpus cases are for one architecture or one operating
system.

## Linux x86-64

The platform the work was done on, and the only one where everything has been run: the
whole gate, `debuginfo.py`, `buildmodel.py`, `storefull.py`, `remote.py` against MinIO, the
fuzzer, rustc's own test suites, the crate sweep and `cargo rustd`. The gate was rerun for
these documents at f191c6e42a under both backends; see [results.md](results.md).

Objects are ELF. A full link runs rustc's link line with rustd's object first and
`--allow-multiple-definition`, so the first definition wins. The splice appends segments to
the executable and rewrites the debug sections so that a debugger sees the new code. About
60 of the 71 steps of `splices.py` are spliced; the others link in full by design. An edit
made while the program is running is linked in full, because the kernel refuses the write.

## Linux AArch64

Runs natively on `ubuntu-24.04-arm` in CI under both backends, including `debuginfo.py`
(under Cranelift gdb prints 9 of 9 locals; under LLVM no locals are described),
`buildmodel.py` (204 of 204, four rows that need an x86-64 host not run), `storefull.py`
and `farsplices.py`.

A `b` or `bl` reaches 128 MB. When a function and its replacement are further apart than
that, the splice uses a longer jump, and a function too short to hold it is linked in full.
`farsplices.py` tests this with 160 MB between the code and the splice (6 of 6).

An executable marked as needing BTI landing pads is declined by the splice. That check is
written and has never been exercised: no test builds such an executable.

AArch64 can also be a cross target from Linux x86-64, with the programs run under
`qemu-aarch64`. The counts are the same as native except `debuginfo.py`, which does not
pass under qemu because the harness runs gdb and backtraces without the emulator.

The fuzzer has not been run on AArch64, and nobody has recorded running `cargo rustd`
there.

## Windows x86-64 (MSVC)

Runs on `windows-latest` in CI under both backends. Objects are COFF and link with MSVC
`link.exe` using rustc's line, with `/FORCE:MULTIPLE` so that rustd's definitions win.

What is specific to the port:

- Unwinding. Windows unwinds in two passes and expects landing pads to be separate
  functions. Cranelift cannot make a call that names its landing pad for the Windows
  calling convention, so a call with a pad is a plain call followed by a look at a slot of
  the frame, and each object carries a personality function of its own (`unwind/seh.rs`).
  This costs a load and a branch after every such call. Exceptions that are not C++
  exceptions (structured exceptions, foreign unwinds) pass through rustd's frames without
  running cleanup; that is inferred from the code and not tested. A Rust panic is a C++
  exception on MSVC and is handled.
- The splice (`splice/pe.rs`) adds sections behind the linker's last. `splices.py` is 71 of
  71 with 61 spliced and 10 full links, and fails on Windows if the count is not 61. COFF
  has no symbol sizes, so each named static gets a section of its own, and a static that
  grows is not spliced. Thread-local data in a patch declines the splice. Executables with
  Control Flow Guard, a signature, or no PDB always take the full link (inferred from the
  checks in the code; the harness links none of these).
- A running `.exe` cannot be written, even by the linker. The daemon renames it aside and
  links a new file.
- The daemon's socket is an AF_UNIX socket. The check that only the user can reach it is
  not implemented on Windows.

Debug info is CodeView procedures and line tables: backtraces and breakpoints by line work,
a debugger shows no types, parameters or locals. The PDB is stale after a splice until the
next full link. `cargo rustd`
hands every build to cargo, because its link step is written for ELF, and has not been run
on Windows. `remote.py` and the fuzzer are not run. The GNU and ARM64 Windows targets have nothing implemented.

## macOS arm64

Runs on `macos-latest` in CI under both backends, with `worktrees.py` in all three of its
modes. Objects are Mach-O.

What is specific to the port:

- Linking. Apple's linker has no flag to keep the first of two definitions. `rustd weaken`
  makes copies of rustc's objects and archives whose definitions are weak, and rustd's
  object is linked ahead of them.
- The splice (`splice/macho.rs`). The loader wants `__LINKEDIT` last with the signature at
  its end. The patch goes where `__LINKEDIT` was, in two new segments, `__LINKEDIT` is
  written again behind them, the unwind tables are rebuilt and the ad hoc signature is
  redone. The result is written to a copy that replaces the executable by rename. The file
  does not grow from splice to splice.
- The unwind tables stay sections of `__TEXT`. The dyld of macOS 15 tells the unwinder only
  of `__unwind_info` and `__eh_frame` that the segment command of `__TEXT` lists, whatever
  segment name their own headers carry, and it refuses an executable with a section outside
  the segment that lists it. So the rebuilt tables are written between the load commands
  and the first section, which is inside `__TEXT`. That room is the linker's
  `-headerpad`: when rustd links it asks for two segment commands plus the tables of the
  executable that is there, a quarter more and 64 KiB, and links once more when what it
  linked has tables that do not fit. Without the room the splice declines.
- Executables with chained fixups are declined and linked in full. That was measured with
  `MACOSX_DEPLOYMENT_TARGET=13.0`; rustc's default deployment target of 11.0 produces dyld
  info and splices.
- The calling convention is Apple's variant of AAPCS64, including its rule that variadic
  arguments always go on the stack.

Not there: debug info is not checked on macOS (the harness reads DWARF out of ELF).
`cargo rustd` and plain cargo after `rustd enable` serve dev and test builds;
`harness/cargo_rustd.py --small` (ripgrep, fd, hyperfine) passes under both backends, and
the larger projects of that harness have not been run ([cargo.md](cargo.md#macos-arm64)).
`buildmodel.py`,
`storefull.py`, `remote.py`, `farsplices.py` and the fuzzer are not run. The first port
noted that under LLVM the unwind rules are not exact inside prologues and epilogues;
nothing later says that changed.

`x86_64-apple-darwin` is refused. With the triple forced through, rustd compiled the corpus
and the link failed on a relocation in the unwind table; the splice and the LLVM object
reader are arm64 only as well.

## wasm32

rustd runs natively and emits wasm32 with its own lowering from Cranelift IR, written as a
relocatable object that `rust-lld` links ahead of rustc's rlibs. The splice writes the
module again with new function bodies under the same indices.

This was measured once, on an earlier branch with `nightly-2026-05-10`, for `wasm32-wasip1`
under wasmtime: corpus MATCH with 655 of 656 functions from rustd, stress 99 of 99, splices
71 of 71 with 62 spliced ([reports/WASM32.md](reports/WASM32.md)). It is not in CI and has
not been rerun on Rust 1.99.0, so treat it as unverified at the current commit.

Limits stated in that report: no unwinding is emitted (the wasm targets are
`panic=abort`), threads are not supported, `v128` and some wide-integer operations are
refused, and `wasm32-unknown-unknown` was exercised only through one Dioxus page.
wasm-bindgen has to run again after every edit and takes 0.27 to 0.36 s on a hello world,
more than the compile and the splice together. There is no LLVM backend for wasm.

Running the compiler itself in a browser is a separate experiment in `crates/rustd-wasm`.

## Still refused on every platform

- `sym` in an `asm!` block that is not naked, a `sym` that names a generic function, and
  one that names a thread-local.
- A naked function whose assembly defines a symbol of its own or has data in another
  section.
- Some variadic definitions. On x86-64 System V: a named parameter that is on the stack or
  is not an integer or float of at most eight bytes. On Windows: a named parameter wider
  than eight bytes or passed as an aggregate, and a definition with no named parameter. On
  AAPCS64 and Apple: a named aggregate.
- An argument in memory aligned to more than 16 bytes, and a vector in a C ABI.
