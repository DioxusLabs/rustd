#!/usr/bin/env bash
# The harnesses CI runs, on every platform: `ci.sh PART` runs the ones of that part, under
# the backend in RUSTD_BACKEND, and says at the end which failed. A harness that is not of a
# platform says so here and is skipped there.
set -u
cd "$(dirname "$0")"
want=${1:?usage: ci.sh core|keys|store|model}
os=$(uname -s) arch=$(uname -m)
case "$os" in
MINGW* | MSYS*)
    os=Windows py=python
    RUSTD_BIN="$(cygpath -w "$(cd .. && pwd)")\\target\\release\\rustd.exe"
    ;;
*)
    py=python3
    RUSTD_BIN="$(cd .. && pwd)/target/release/rustd"
    ;;
esac
export RUSTD_BIN
linux() { [ "$os" = Linux ]; }
macos() { [ "$os" = Darwin ]; }

# Parts are by how long they take: keys.py alone, buildmodel.py alone, the store and the
# daemon under load, and the rest.
part() { case "$1" in keys.py) echo keys ;; buildmodel.py) echo model ;; store* | remote.py | stress.py | selects.py) echo store ;; *) echo core ;; esac; }
failed=
run() {
    [ "$(part "$1")" = "$want" ] || return 0
    echo "::group::$*"
    "$py" "$@" || { failed="$failed [$*]"; echo "::error::$* failed"; }
    echo "::endgroup::"
}

run difftest.py corpus --bin runner --crate cases --layouts
run programs.py
run stress.py
run breakers.py
run unwinds.py
run splices.py
# A branch reaches 128 MB on AArch64, and the splice has to get past that. Mach-O is not spliced.
if linux && [ "$arch" = aarch64 ]; then RUSTD_SPLICE=1 run farsplices.py; fi
run asmedits.py
run includes.py
run worktrees.py
if macos; then
    run worktrees.py --join --together
    run worktrees.py --overlay
fi
run keys.py
# Generated programs and edits on fixed seeds. Only x86-64 has been fuzzed so far.
if linux && [ "$arch" = x86_64 ]; then
    run fuzz/fuzz.py smoke --backends "$RUSTD_BACKEND"
    run fuzz/edits.py smoke --backends "$RUSTD_BACKEND"
fi
# How much of the corpus LLVM compiled itself, and what it left to Cranelift and why.
if [ "$RUSTD_BACKEND" = llvm ]; then run backends.py corpus runner cases --bin runner --levels 2f; fi
# debuginfo.py reads DWARF out of an ELF or a PDB; buildmodel.py builds for Linux targets,
# and says which of its cases are of another host than this one.
if ! macos; then
    run debuginfo.py
    run buildmodel.py --backend "$RUSTD_BACKEND"
fi
run storekills.py --kills 100
run storecorrupts.py --rounds 4
# storefull.py mounts a tmpfs.
if ! macos; then run storefull.py; fi
run storeshared.py
if linux; then
    run storeguards.py
    run selects.py
    if [ -x "$HOME/s3tools/minio" ]; then run remote.py; fi
fi
echo "failed:${failed:- none}"
test -z "$failed"
