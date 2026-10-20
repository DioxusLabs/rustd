#!/usr/bin/env python3
"""clippy.py: `cargo rustd clippy` against clippy, on the workspace in clippy/.

Each lint rustd has is looked for where clippy finds it: the same file, line and message,
and no more. Then the daemon is asked again with nothing changed, and after an edit to one
function, and has to lint no body again, then only that one. Then `-- -D warnings` and an
`#[allow]` written above the edited function.

    python3 clippy.py
"""
import json, os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cargo_rustd import RUSTD, base_env

# The lints rustd has, by clippy's name.
LINTS = {"bool_comparison", "eq_op", "identity_op", "needless_return", "len_zero", "let_unit_value", "self_assignment", "needless_bool"}

failures = []


def check(name, held, detail=""):
    print(f"  {'ok' if held else 'WRONG'}  {name}  {detail}", flush=True)
    if not held:
        failures.append(name)


def clippys(ws, env):
    """What clippy finds of the lints rustd has: (file, line, message), and its exit status."""
    run = subprocess.run(["cargo", "clippy", "--message-format=json"], cwd=ws, env=env, capture_output=True, text=True)
    found = set()
    for line in run.stdout.splitlines():
        message = json.loads(line)
        if message.get("reason") != "compiler-message":
            continue
        diagnostic = message["message"]
        code = (diagnostic.get("code") or {}).get("code", "")
        if not code.startswith("clippy::") or code[8:] not in LINTS:
            continue
        span = next(it for it in diagnostic["spans"] if it["is_primary"])
        found.add((span["file_name"], span["line_start"], diagnostic["message"]))
    return found, run.returncode


def rustds(ws, env, *args):
    """What `cargo rustd clippy` prints, as (file, line, message), its exit status, and how
    many bodies it linted again of how many."""
    run = subprocess.run(["cargo", "rustd", "clippy", *args], cwd=ws, env=dict(env, RUSTD_STATS="1"), capture_output=True, text=True)
    found = set(
        (path, int(line), message)
        for message, path, line in re.findall(r"^(?:warning|error): (.*)\n\s*--> ([^:\n]+):(\d+):\d+", run.stderr, re.M)
    )
    stats = re.search(r"rustd: linted (\d+) of (\d+) bodies anew", run.stderr)
    return found, run.returncode, (int(stats[1]), int(stats[2])) if stats else None, run.stderr


def main():
    work = os.path.realpath(tempfile.mkdtemp(prefix="rustd-clippy-", dir="/tmp" if sys.platform == "darwin" else None))
    ws = os.path.join(work, "ws")
    shutil.copytree(os.path.join(HERE, "clippy"), ws)
    env = base_env(os.path.join(work, "home"))
    try:
        want, want_status = clippys(ws, dict(env, CARGO_TARGET_DIR=os.path.join(work, "target-clippy")))
        got, status, stats, said = rustds(ws, env)
        check("clippy finds what the fixture is for", len(want) >= 10, f"{len(want)} findings")
        check("rustd finds what clippy does", got == want,
              f"clippy only {sorted(want - got)}, rustd only {sorted(got - want)}" if got != want else f"{len(got)} findings")
        check("and ends as clippy does", status == want_status, f"{status}, clippy {want_status}")
        if got != want or status != want_status:
            print(said)
        _, _, again, _ = rustds(ws, env)
        check("asked again, it lints no body again", again is not None and again[0] == 0, f"{again}")
        main_rs = os.path.join(ws, "app/src/main.rs")
        text = open(main_rs).read()
        open(main_rs, "w").write(text.replace("fn pick(flag: bool) -> bool {\n", "fn pick(flag: bool) -> bool {\n    let _edited = 1;\n"))
        moved = {(f, l + (f == "app/src/main.rs" and l > 14), m) for f, l, m in want}
        got, _, edited, _ = rustds(ws, env)
        check("after an edit to one function, it lints that one again", edited is not None and 1 <= edited[0] <= 2, f"{edited}")
        check("and finds what it found, moved", got == moved, f"{sorted(got ^ moved)}")
        _, status, _, _ = rustds(ws, env, "--", "-D", "warnings")
        check("`-- -D warnings` fails the build", status == 101, f"{status}")
        open(main_rs, "w").write(open(main_rs).read().replace("fn pick(", "#[allow(clippy::needless_bool)]\nfn pick("))
        got, _, _, _ = rustds(ws, env)
        check("an `#[allow]` above it leaves it alone", not any("returns a bool literal" in m and l < 20 for _, l, m in got if True), f"{sorted(m for _, _, m in got if 'bool literal' in m)}")
    finally:
        subprocess.run(["cargo", "rustd", "stop"], cwd=ws, env=env, capture_output=True)
        if "--keep" not in sys.argv:
            shutil.rmtree(work, ignore_errors=True)
    print(f"{'all right' if not failures else f'{len(failures)} WRONG'}")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
