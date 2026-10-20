#!/usr/bin/env bash
# What CI runs, on every platform:
#   ci.sh                   every harness part, under both backends, all at once
#   ci.sh BACKEND PART      the harnesses of one part under one backend
#   ci.sh projects GROUP... cargo_rustd.py on each group of projects, under both backends, all
#                           at once: `small` is the CI's three with the flags, the daemon's
#                           life and plain cargo, and another group is projects by name
# Each lane run at once has a temporary directory, a daemon home, a cache and a copy of the
# harness of its own (the harnesses build in the workspaces beside them), and its output is
# printed whole when it ends. A harness that is not of a platform is skipped
# here, and this says why.
set -u
cd "$(dirname "$0")"
os=$(uname -s) arch=$(uname -m)
case "$os" in
MINGW* | MSYS*)
    os=Windows py=python
    : "${RUSTD_BIN:=$(cygpath -w "$(cd .. && pwd)")\\target\\release\\rustd.exe}"
    base=$(cygpath -m "${RUNNER_TEMP:-$TEMP}")/ci
    ;;
*)
    py=python3
    : "${RUSTD_BIN:=$(cd .. && pwd)/target/release/rustd}"
    base=/tmp/ci-$$
    ;;
esac
export RUSTD_BIN
linux() { [ "$os" = Linux ]; }
macos() { [ "$os" = Darwin ]; }
backends="cranelift llvm"
parts="codegen keys store model"

names=() pids=()
# A lane's directory is its number: a daemon's worker sockets are deep under it, and a socket's
# path is at most 108 bytes on Linux and 104 on macOS.
lane() {
    local name=$1 dir="$base/${#names[@]}"
    shift
    mkdir -p "$dir/t"
    (
        export TMPDIR="$dir/t" RUSTD_HOME="$dir/h" XDG_CACHE_HOME="$dir/c" RUSTD_PROJECTS="$dir/p" RUSTD_REPORTS="$dir"
        start=$SECONDS
        "$@" >"$dir/log" 2>&1
        status=$?
        echo "$status $((SECONDS - start))" >"$dir/end"
        echo "ended: $name, exit $status after $(((SECONDS - start) / 60))m$(((SECONDS - start) % 60))s"
        exit $status
    ) &
    names+=("$name") pids+=($!)
}
lanes() {
    local failed= i
    for i in "${!pids[@]}"; do
        wait "${pids[$i]}" && continue
        failed="$failed [${names[$i]}]"
    done
    for i in "${!names[@]}"; do
        local dir="$base/$i"
        echo "::group::${names[$i]}: exit $(cut -d' ' -f1 "$dir/end"), $(cut -d' ' -f2 "$dir/end")s"
        # Groups do not nest.
        sed -e 's/^::group::/== /' -e '/^::endgroup::$/d' "$dir/log"
        echo "::endgroup::"
    done
    echo "failed:${failed:- none}"
    [ -z "$failed" ] && rm -rf "$base"
    test -z "$failed"
}

if [ $# = 0 ]; then
    for backend in $backends; do
        for part in $parts; do
            copy="$base/${#names[@]}/r"
            mkdir -p "$copy/.cargo"
            cp ../.cargo/config.toml "$copy/.cargo/"
            (cd .. && git ls-files -z harness | tar -cf - --null -T -) | tar -xf - -C "$copy"
            lane "$backend $part" bash "$copy/harness/ci.sh" "$backend" "$part"
        done
    done
    lanes
    exit
fi
if [ "$1" = projects ]; then
    shift
    for backend in $backends; do
        for group in "$@"; do lane "$backend $group" bash ci.sh project "$backend" "$group"; done
    done
    lanes
    exit
fi
if [ "$1" = project ]; then
    export RUSTD_BACKEND=$2
    if [ "$3" = small ]; then args=--small; else args="$3 --only-projects"; fi
    # Incremental compilation is left to the profile, as on a developer's machine.
    env -u CARGO_INCREMENTAL "$py" cargo_rustd.py $args
    status=$?
    cat "${RUSTD_REPORTS:-.}"/CARGO-RUSTD*.md
    exit $status
fi

export RUSTD_BACKEND=$1
want=$2
# Parts are by how long they take, about the same each, the longest harness of each first.
part() {
    case "$1" in
    storekills.py | difftest.py | programs.py | storefull.py | fuzz/fuzz.py) echo store ;;
    keys.py | remote.py | stress.py) echo keys ;;
    buildmodel.py | storecorrupts.py | storeshared.py | fuzz/edits.py | storeguards.py | worktrees.py | selects.py) echo model ;;
    *) echo codegen ;;
    esac
}
failed=
run() {
    [ "$(part "$1")" = "$want" ] || return 0
    echo "::group::$*"
    local start=$SECONDS
    "$py" "$@" || { failed="$failed [$*]"; echo "::error::$RUSTD_BACKEND $want: $* failed"; }
    echo "took $((SECONDS - start))s: $*"
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
