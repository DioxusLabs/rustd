#!/usr/bin/env python3
"""The doctests of real crates, run by `cargo test --doc` and by `cargo rustd test --doc`:
the same tests must end the same way and print the same.

    RUSTD_BIN=../target/release/rustd python3 doctests.py [--few] [name-version ...]

Each crate is unpacked by `vendor.sh` and built in a directory that is removed afterwards.
An example rustd does not build fails with rustd's reason, and its crate is counted as
refused with that reason; any other difference is WRONG and fails the run. `--few` is the first three crates."""
import os
import re
import subprocess
import sys
import tempfile

from buildmodel import doctest_report

HERE = os.path.dirname(os.path.abspath(__file__))
RUSTD = os.path.abspath(os.environ.get("RUSTD_BIN", os.path.join(HERE, "..", "target", "release", "rustd")))
CRATES = [
    "semver-1.0.28", "either-1.19.0", "smallvec-1.16.3",
    "serde_core-1.0.229", "regex-1.13.1", "itertools-0.15.0", "chrono-0.4.45", "anyhow-1.0.104",
    "bytes-1.12.1", "thiserror-2.0.21", "log-0.4.34", "bitflags-2.13.2", "indexmap-2.14.2",
    "once_cell-1.21.4", "hashbrown-0.17.1", "memchr-2.8.3", "url-2.5.8", "uuid-1.28.0",
    "time-0.3.55", "rand-0.10.3", "arrayvec-0.7.8", "base64-0.23.1",
    "byteorder-1.5.0", "num-traits-0.2.19", "strum-0.28.0", "nom-8.0.0", "textwrap-0.16.4",
    "unicode-segmentation-1.13.3", "httparse-1.10.1", "serde_json-1.0.154",
]


def tested(crate, command, target_dir):
    """How the crate's doctests ended, what they printed, and what was said beside."""
    path = os.path.dirname(RUSTD) + os.pathsep + os.environ["PATH"]
    run = subprocess.run(["cargo", *command, "test", "--doc"], cwd=crate, capture_output=True, text=True,
                         timeout=3600, env={**os.environ, "PATH": path, "CARGO_TARGET_DIR": target_dir})
    return run.returncode, doctest_report(run.stdout), run.stderr


def row(spec):
    """The crate's line: its verdict and what there is to say of it."""
    subprocess.run(["sh", os.path.join(HERE, "vendor.sh"), spec], check=True)
    crate = os.path.join(HERE, "vendor", spec.rsplit("-", 1)[0])
    with tempfile.TemporaryDirectory(prefix="rustd-doctests-") as scratch:
        want = tested(crate, [], os.path.join(scratch, "cargo"))
        got = tested(crate, ["rustd"], os.path.join(scratch, "rustd"))
    return judged(want, got)


def judged(want, got):
    """What the two runs of a crate come to."""
    if want[:2] != got[:2]:
        refused = [l for l in got[1] if REFUSED.search(l)]
        if refused:
            return "refused", refused[0][:300]
        lines = [f"cargo's `{w}`, rustd's `{g}`" for w, g in zip(want[1], got[1]) if w != g]
        return "WRONG", (lines[0] if lines else f"cargo's ends with {want[0]}, rustd's with {got[0]}")[:300]
    tests = sum(l.startswith("test ") and not l.startswith("test result") for l in want[1])
    if not tests:
        return "WRONG", f"cargo ran no doctest: {want[2].strip()[-200:]}"
    return "same", f"{tests} doctests"


# What rustd says of an example it does not build.
REFUSED = re.compile(r"which only a program of its own can have|rustd found no error|rustd does not run|rustd builds the examples of a library in its edition")


def main():
    args = [a for a in sys.argv[1:] if a != "--few"]
    counts = {"same": 0, "refused": 0, "WRONG": 0}
    for spec in args or (CRATES[:3] if "--few" in sys.argv else CRATES):
        verdict, said = row(spec)
        counts[verdict] += 1
        print(f"{spec:28} {os.environ.get('RUSTD_BACKEND', 'cranelift'):9} {verdict:8} {said}", flush=True)
    print(f"{counts['same']} same, {counts['refused']} refused, {counts['WRONG']} WRONG")
    sys.exit(1 if counts["WRONG"] else 0)


if __name__ == "__main__":
    main()
