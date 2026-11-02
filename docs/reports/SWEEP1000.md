# The test suites of 1100 crates.io crates through rustd

`harness/sweep1000.txt` holds 1100 `name-version` lines: the most downloaded crates on
crates.io, each at its newest version, as the crates.io API returned them on 2026-10-17.
`cratesweep.sh` runs each crate's tests built by rustc and built by rustd, and compares what
they print. `.github/workflows/sweep.yaml` runs the whole list every Sunday on 16 machines,
under both backends.

## Where this stands

The last full run is of `1c918a904f` (the branch of #8, before its last commits), run
39508254606: every crate under Cranelift and under LLVM. The rows that differed were run again
by hand on the head of #10, under both backends; the table of causes below says what each
came to.

| | Cranelift | LLVM |
|---|---:|---:|
| tests print the same as under rustc | 851 | 851 |
| differ | 10 | 9 |
| rustc's own runs differ from each other (`UNSTABLE`) | 4 | 5 |
| untested | 232 | 232 |
| timed out at 20 minutes | 2 | 2 |
| the harness failed | 1 | 1 |
| tests run and compared | 70,288 | 70,288 |
| functions from rustd | 369,328 of 370,137 | 369,328 of 370,137 |

What this comes to on the head of #10: every row that differed is fixed or is not rustd's,
except the text of a failed `assert!` (num_enum, proc-macro-crate). Nothing in the run was a
wrong result that is still open. The full sweep has not been run again on this head; the
numbers above will move when it is.

## The rows that differed, by cause

Each was run again on the head of #10 with `cratesweep.sh`, under both backends unless the
row says otherwise.

| crate | backend | what differed | cause | on the head of #10 |
|---|---|---|---|---|
| cpp_demangle, stacker | both | tests that recurse deep on a small stack overflowed under rustd only | rustd's frames were bigger than rustc's: scalar temporaries promoted to registers kept their stack slots. cpp_demangle's recursion test needed 2.19 MB of stack under rustd against 1.42 MB under rustc | fixed in `81e1afdd52`, case `frame_of_temporaries` (a frame of 7,632 bytes, 144 now, 1,312 under rustc). cpp_demangle 57 tests, stacker 7, match |
| jsonschema | Cranelift | three `long_ref_chain_compiles_on_small_stack` tests overflowed | the same | fixed in `81e1afdd52`; 11 binaries, 2,101 tests match |
| curve25519-dalek | both | the test binary crashed under rustd | not bisected | matches, 109 tests |
| ron | both | typetag's tests found nothing in their registry | two `inventory` constructors of one path in one body did not get rustc's symbols, so rustc's constructor filled a registry that rustd's code never read | fixed in `f4abc71fbd`, case in `breakers`; 73 binaries, 428 tests match |
| scc | both | the size of four futures, 8 to 16 bytes off | a value moved out of `Some` did not leave the `Option` empty, and drop flags sat in a prefix shared by every state | fixed in #8 (`92408cb314`), after the run; 119 tests match under both. One Cranelift rerun differed the other way: rustc's own build failed `insert_prune_any_async` (a shift overflow in a tokio worker) while rustd's passed, and the next rerun matched |
| backtrace | LLVM | frames missing from a backtrace | LLVM turned calls into jumps | fixed in `31c5193005`; 8 binaries match, `sp_smoke_test` among them |
| crc32c, web-time | both | the build of the tests failed (`can't find bench`), or the harness did | the published package lists a bench or test file it leaves out, and test builds asked cargo for `--all-targets` | fixed in `87f91963f2`; crc32c 3 tests match. web-time builds now, and its one test binary runs no test on Linux, so it is untested |
| zbus | both | the unit tests crashed under rustd (SIGSEGV) in their first test | not bisected | matches under both: 11 binaries, 249 tests. The `e2e` test names `zbus_xml`, which the published crate does not depend on, so cargo builds it for neither side |
| num_enum, proc-macro-crate | both | the text of a failed `assert!`; the tests run cargo on a manifest the published crate leaves out, so they fail under both | rustc prints the condition as its pretty printer breaks it over lines, rustd prints it on one line | open: breakers `assert_message` and `assert_long_expression` |
| base64 | both | timed out at 20 minutes | its unit tests are slow in a debug build: the run on the head of #10 took 33 minutes for both builds, and which build is the slow one was not measured | matches under Cranelift with a longer limit: 3 binaries, 13 tests |
| aws-sdk-s3 | both | timed out at 20 minutes | each test binary takes all 19,598 functions of the crate from rustd and there are many of them; one (`aws_chunked`) does not build under cargo either | not rustd; it needs a longer limit to finish |

The `UNSTABLE` rows (colored, openssl, procfs, semver-parser, and os_pipe under LLVM) print
something else in different runs of rustc's own binary, so the sweep does not compare them.

## Functions left to rustc

809 of 370,137, the same under both backends. 617 of them are left only because they share an
`async` block with a function that is (zbus, async-process). The rest, by reason:

| reason | functions | crates |
|---|---:|---|
| `TypeId` of a type rustd does not hash as rustc does | 56 | zbus, error_chain, rusty-fork, typeid, wit-component |
| `mir: UnresolvedMethod` | 33 | generic-array, html5ever, markup5ever, procfs |
| a writable static without a rustc symbol (`DTORS`, `GLOBAL_PANIC_COUNT`, `__CALLSITE` and others) | 34 | async-process, zbus |
| `mir: MissingFunctionDefinition` | 17 | async-process, ring, wide |
| `mir: HasErrors` | 14 | html5ever, markup5ever, structopt |
| `mir: NotSupported` | 7 | bigdecimal, html5ever, ring, zbus |
| `mir: IncompleteExpr`, `mir: UnsizedTemporary` | 8 | zvariant |
| a call to a trait method with no body and no rustc symbol, a builtin `Clone`, or the `fmt` of a vtable | 12 | html5ever, markup5ever |
| LLVM intrinsic `x86.aesni.aeskeygenassist` | 3 | aes |
| calling convention `EfiApi` | 3 | r-efi |
| a layout (`GenericArray`, an alias, an array) | 4 | generic-array, ron, wit-bindgen |
| `mir: UnresolvedName` | 1 | pyo3 |

`harness/sweepreport.py <dir>` prints this list from a sweep's directory.

## How to rerun

```
LLVM_SYS_201_PREFIX=/usr/lib/llvm-20 cargo build -p rustd --release --features llvm
cd harness
RUSTD_BIN=$PWD/../target/release/rustd CLEAN=1 JOBS=3 BACKENDS="cranelift llvm" \
    ./cratesweep.sh ~/sweep/out $(cat sweep1000.txt)
./sweepreport.py ~/sweep/out/cranelift
```

The sweep runs every crate under the first backend before it starts the second. A crate with a
`<name>.status` in `~/sweep/out/<backend>` is not run again; delete the file to rerun it.
`cratetest.py vendor/<name>` runs one crate and `--bisect` names the functions that differ.
