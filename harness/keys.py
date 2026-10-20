#!/usr/bin/env python3
"""keys.py: whether the store hands a build code that was compiled from something else.

The workspace in harness/keys has a function for each thing code can depend on that is not the
text of its file. Each case builds the workspace with an empty store, changes one such thing,
and builds again with the store the first build filled: the program has to print what cargo's
does. "again" changes the checkout where it is, "elsewhere" changes a copy of it at another
path, as a second worktree or another machine would have it.

usage: keys.py [case ...]
"""
from concurrent.futures import ProcessPoolExecutor
import os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from difftest import Fixture


def write(path, text):
    return lambda ws, env, args: open(os.path.join(ws, path), "w").write(text)


def replace(path, old, new):
    def edit(ws, env, args):
        text = open(os.path.join(ws, path)).read()
        assert old in text, (path, old)
        open(os.path.join(ws, path), "w").write(text.replace(old, new))
    return edit


def append(path, text):
    return lambda ws, env, args: open(os.path.join(ws, path), "a").write(text)


def both(*changes):
    return lambda ws, env, args: [change(ws, env, args) for change in changes]


def setenv(name, value):
    return lambda ws, env, args: env.__setitem__(name, value)


def arg(*more):
    return lambda ws, env, args: args.extend(more)


# What rustd says of a function it leaves to rustc because the copy of an instance it calls
# is one rustc picked and rustd cannot tell which.
REFUSED = "overflow checks"

# What rustd does not do yet: these differ, and are told apart when they do.
OPEN = set()

# (name, the change, the line of the program's output it has to show in or None for no line)
CASES = [
    ("nothing", lambda ws, env, args: None, None),
    ("a file outside the package that is included", write("shared.txt", "shared anew"), "outside"),
    ("a file of the package that is included", write("klib/src/inside.txt", "inside anew"), "inside"),
    ("what a build script reads and generates code from", write("klib/gen.txt", "8"), "generated"),
    ("a variable a build script reads and sets for the crate", setenv("KEYS_SCRIPT", "set"), "script_env"),
    ("a cfg a build script sets", write("klib/flag", ""), "script_cfg"),
    ("a feature", arg("--features", "extra"), "feature"),
    ("a variable of the process read by option_env!", setenv("KEYS_PROCESS", "set"), "process_env"),
    ("a variable of .cargo/config.toml", replace(".cargo/config.toml", '"config"', '"config anew"'), "config_env"),
    # With the flag `difftest` sets, which this would otherwise take the place of: without it
    # rustc keeps to one object the functions nothing else calls, and those are left to rustc.
    ("a cfg of RUSTFLAGS", setenv("RUSTFLAGS", "-C link-dead-code --cfg keys_flag"), "flag_cfg"),
    ("the release profile", arg("--release"), "assertions"),
    ("overflow checks of the dev profile", append("Cargo.toml", "\n[profile.dev]\noverflow-checks = false\n"), "overflows"),
    ("debug assertions of the dev profile", append("Cargo.toml", "\n[profile.dev]\ndebug-assertions = false\n"), "assertions"),
    ("a profile of its own", both(append("Cargo.toml", '\n[profile.quick]\ninherits = "dev"\noverflow-checks = false\n'), arg("--profile", "quick")), "overflows"),
    ("overflow checks of the package a function is written in", append("Cargo.toml", "\n[profile.dev.package.kdep]\noverflow-checks = false\n"), "checks"),
    ("overflow checks of a package that calls generic code", append("Cargo.toml", "\n[profile.dev.package.klib]\noverflow-checks = false\n"), "checks"),
    ("overflow checks of the package of the program", append("Cargo.toml", "\n[profile.dev.package.kapp]\noverflow-checks = false\n"), "checks"),
    ("overflow checks of one package in release", both(append("Cargo.toml", "\n[profile.release.package.kdep]\noverflow-checks = true\n"), arg("--release")), "checks"),
    ("overflow checks of the program alone in release", both(append("Cargo.toml", "\n[profile.release.package.kapp]\noverflow-checks = true\n"), arg("--release")), "checks"),
    ("overflow checks of all but the package a small function is written in, in release", both(append("Cargo.toml", "\n[profile.release]\noverflow-checks = true\n[profile.release.package.kdep]\noverflow-checks = false\n"), arg("--release")), "checks"),
    ("overflow checks of all but the package whose copy of generic code the program uses", append("Cargo.toml", "\n[profile.dev]\noverflow-checks = false\n[profile.dev.package.klib]\noverflow-checks = true\n"), "checks"),
    ("debug assertions of one package", append("Cargo.toml", "\n[profile.dev.package.klib]\ndebug-assertions = false\n"), "assertions"),
    ("a constant of a dependency", replace("kdep/src/lib.rs", "SCALE: u32 = 3", "SCALE: u32 = 4"), "scaled"),
    ("an inlined function of a dependency", replace("kdep/src/lib.rs", "x + 1", "x + 2"), "scaled"),
    ("the layout of a type of a dependency", replace("kdep/src/lib.rs", "pub side: u32,", "pub side: u32,\n    pub other: u64,"), "shape"),
    ("a generic function of a dependency", replace("kdep/src/lib.rs", '"{:?} {}"', '"{:?} of {}"'), "described"),
]


def size(directory):
    return sum(os.path.getsize(os.path.join(directory, name)) for name in os.listdir(directory))


def build(ws, env, args):
    """What cargo's program prints and what rustd's does, and the functions that were left to rustc."""
    saved = dict(os.environ)
    os.environ.update(env)
    try:
        fx = Fixture(ws, ["kapp", "klib", "kdep"], ["-p", "kapp", *args])
        fx.rustd_args = list(args)
        fx.rustc_build()
        fx.rustd_build()
        skipped = [row for rows in fx.reports.values() for row in rows if row[0] == "skipped" and "no rustc symbol" not in row[2]]
        return fx.behaviour(fx.reference), fx.behaviour(fx.binary), skipped
    finally:
        os.environ.clear()
        os.environ.update(saved)
        shutil.rmtree(fx.work, ignore_errors=True)


def case(index, mode, at):
    """One case built in a process of its own, since `build` sets the environment: what it
    prints, whether it is wrong, whether an open case is right now, and the functions refused."""
    name, change, line = CASES[index]
    lines = []
    store, first = os.path.join(at, "store"), os.path.join(at, "first")
    os.makedirs(store)
    shutil.copytree(os.path.join(HERE, "keys"), first, ignore=shutil.ignore_patterns("target"))
    env, args = {"RUSTD_CACHE": store}, []
    want, got, _ = build(first, env, args)
    problems = [] if want == got else ["the first build differs"]
    filled = size(store)
    second = first
    if mode == "elsewhere":
        second = os.path.join(at, "second")
        shutil.copytree(first, second, ignore=shutil.ignore_patterns("target"))
    before = want
    change(second, env, args)
    want, got, left = build(second, env, args)
    if want != got:
        problems.append("the second build differs")
    if line and before == want:
        problems.append("cargo's program is the same after the change")
    # Where the crates differ in overflow checks, rustd leaves to rustc a function that
    # calls a copy it cannot tell the checks of. The function the case is about has to
    # be rustd's all the same, or the case shows nothing.
    refused = [row for row in left if REFUSED in row[2] and row[1].split("::")[-1] != line]
    if len(left) > len(refused):
        problems.append(f"{len(left) - len(refused)} functions left to rustc")
    known = name in OPEN
    lines.append(f"{'same     ' if not problems else 'open     ' if known else 'DIFFERENT'} {mode:9} {name}: store {filled} bytes, {size(store) - filled} more")
    lines += [f"    {problem}" for problem in problems]
    lines += [f"    refused {row[1]}: {row[2][:160]}" for row in refused]
    if want != got:
        ours, theirs = (it[1].decode(errors="replace").splitlines() for it in (got, want))
        for a, b in zip(theirs, ours):
            if a != b:
                lines.append(f"    rustc: {a}\n    rustd: {b}")
        if len(ours) != len(theirs):
            lines.append(f"    rustd: status {got[0]}, {len(ours)} lines of {len(theirs)}; {got[2].decode(errors='replace').strip()[-300:]}")
    return "\n".join(lines), bool(problems) and not known, known and not problems, len(refused)


def main():
    work = os.path.realpath(tempfile.mkdtemp(prefix="rustd-keys-"))
    chosen = sys.argv[1:]
    runs = [
        (index, mode)
        for index, (name, _, _) in enumerate(CASES)
        if not chosen or any(it in name for it in chosen)
        for mode in ("again", "elsewhere")
    ]
    total = len(runs)
    wrong = fixed = refusals = 0
    # Each case has a store and checkouts of its own, and its builds use a few cores.
    jobs = max(1, (os.cpu_count() or 2) // 2)
    with ProcessPoolExecutor(jobs) as pool:
        ats = [os.path.join(work, str(n)) for n in range(1, total + 1)]
        for said, bad, mended, refused in pool.map(case, *zip(*runs), ats) if runs else []:
            print(said, flush=True)
            wrong += bad
            fixed += mended
            refusals += refused
    still = sum(2 for name, _, _ in CASES if name in OPEN and (not chosen or any(it in name for it in chosen))) - fixed
    print(f"{total - wrong - still} of {total - still} right, {still} open, {refusals} functions refused; {work}")
    if fixed:
        print(f"{fixed} of the open cases are the same now: take them out of OPEN")
    sys.exit(1 if wrong or fixed else 0)


if __name__ == "__main__":
    main()
