#!/usr/bin/env python3
"""worktrees.py: several checkouts of one workspace built by one daemon.

The stress workspace is copied COUNT times. The daemon is started in the first copy with the
others as `--also`; each step edits files of some checkouts and asks for the program of some by
`rustd sync SOCKET --project ...`. Every program asked for is run and compared with what
`cargo build` of that checkout prints.

With `--join` the daemon is started in the first copy alone, and the others join it when they
are first asked for. With `--together` the programs of a step are asked for at once.
"""
import os, shlex, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import linkline
from difftest import Fixture, RUSTD, sysroot_rlibs, RUNNER, TARGET_ARGS, built

COUNT = 3
MID, APP = "mid/src/lib.rs", "app/src/main.rs"
AREA = "sbase::square!(self.side)"
SUM = "items.iter().sum()"
# Not the same in any two checkouts from the start.
NOTE = "app/src/note.txt"
MORE = "app/src/more.rs"
# Of the workspace and of no package.
SHARED = "shared.txt"
# Not the same in any two runs either: with `RUSTD_CACHE` a run has what the last one compiled.
RUN = os.getpid()
# (what the step is, [(checkout, file, old or None to write it, new or None to remove it)], checkouts asked for in order, the ones cargo rejects)
STEPS = [
    ("nothing edited, the others asked for the first time", [], [1, 2, 0], []),
    ("nothing edited, all again", [], [0, 1, 2], []),
    ("one checkout edited", [(0, MID, AREA, AREA + " + 1")], [0, 1, 2], []),
    ("the same edit in another", [(1, MID, AREA, AREA + " + 1")], [1, 0, 2], []),
    ("a different edit to the same code in the third", [(2, MID, AREA, AREA + " + 7")], [2, 1, 0], []),
    ("two checkouts edited before either is asked",
     [(0, MID, AREA + " + 1", AREA + " + 2"), (1, APP, SUM, "items.iter().sum::<u32>() + 1")], [1, 0, 2], []),
    ("one checkout broken", [(1, MID, AREA + " + 1", AREA + ' + "x"')], [1, 0, 2, 1], [1]),
    ("another edited while it is broken", [(2, APP, SUM, "items.iter().sum::<u32>() + 5")], [2, 1, 0], [1]),
    ("mended", [(1, MID, AREA + ' + "x"', AREA + " + 4")], [0, 1, 2], []),
    ("a function added in one",
     [(2, APP, "fn main() {", "fn extra() -> u32 {\n    41\n}\n\nfn main() {\n    println!(\"extra {}\", extra());")],
     [2, 0, 1], []),
    ("one put back as another is", [(2, MID, AREA + " + 7", AREA + " + 2")], [2, 0], []),
    ("a file that is included edited in one", [(1, NOTE, "note of 1", "another note")], [0, 1, 2], []),
    ("a module with its file added in one",
     [(1, MORE, None, "pub fn more() -> u32 {\n    5\n}\n"),
      (1, APP, "fn main() {", "mod more;\n\nfn main() {\n    println!(\"more {}\", more::more());")],
     [1, 0, 2], []),
    ("the file edited", [(1, MORE, "5", "6")], [0, 1, 2], []),
    ("the file removed", [(1, MORE, "", None)], [1, 0, 2], [1]),
    ("and the module with it",
     [(1, APP, "mod more;\n\nfn main() {\n    println!(\"more {}\", more::more());", "fn main() {")],
     [1, 0, 2], []),
    ("a place asked for in one, by a crate that had not",
     [(1, MID, "pub fn seeded() -> u32 {",
       "pub fn here() -> &'static str {\n    env!(\"CARGO_MANIFEST_DIR\")\n}\n\npub fn seeded() -> u32 {"),
      (1, APP, 'println!("{}", HERE);', 'println!("{} {}", HERE, smid::here());')],
     [1, 0, 2, 1], []),
    ("that file edited in one", [(2, SHARED, f"shared of 2 in {RUN}", "shared anew")], [0, 2, 1], []),
    ("and made what another has", [(2, SHARED, "shared anew", f"shared of 0 in {RUN}")], [2, 1, 0], []),
    # The checkout is loaded again, and the others are left as they are.
    ("the manifest of one changed in what no crate reads",
     [(0, "app/Cargo.toml", "[package]", "[package.metadata]\nnote = 1\n\n[package]")], [1, 2, 0, 1], []),
]
# Cargo may build that checkout another way now, so it can't be read as the first any more. A
# checkout that is loaded is turned down for it.
if "--overlay" in sys.argv:
    STEPS += [
        ("a manifest edited in one",
         [(2, "mid/Cargo.toml", "[dependencies]", "[features]\nmore = []\n\n[dependencies]")], [2, 0, 1], []),
        ("that one edited", [(2, MID, AREA + " + 2", AREA + " + 9")], [0, 2, 1], []),
        ("and another", [(0, MID, AREA + " + 2", AREA + " + 3")], [0, 2, 1], []),
    ]


# With `--overlay` the others are not loaded at all: each is read as the first with other files.
OVERLAY = "--overlay" in sys.argv
# With `--split` the others join the first and share the packages that are the same in both.
SPLIT = "--split" in sys.argv
# With `--thin` the checkouts start out with the same included file, so that the others are
# read as the first with other files from their first build on.
THIN = "--thin" in sys.argv
# With `--slow` every build of a checkout read as another counts as a long one, so that the
# daemon gives up on reading them so and loads them.
if "--slow" in sys.argv:
    os.environ["RUSTD_SLOW_SWITCH_MS"] = "0"
JOIN = "--join" in sys.argv or SPLIT or THIN


def splice(program):
    """Edits are added to the linked binary where that can be done; RUSTD_SPLICE=0 links each in full."""
    return ["--binary", program["bin"]]


def main():
    # cargo names a checkout by its real path, and the temporary directory of macOS is a link.
    work = os.path.realpath(tempfile.mkdtemp(prefix="rustd-worktrees-"))
    socket, log_path = os.path.join(work, "rustd.sock"), os.path.join(work, "daemon.log")
    crates = ["sapp", "sbase", "smid"]
    checkouts = []
    for at in range(COUNT):
        ws = os.path.join(work, f"checkout{at}")
        shutil.copytree(os.path.join(HERE, "stress"), ws, ignore=shutil.ignore_patterns("target"))
        open(os.path.join(ws, NOTE), "w").write(f"note of {1 if THIN else at}\n")
        main_rs = os.path.join(ws, APP)
        text = open(main_rs).read()
        assert "fn main() {" in text
        text += '\nconst HERE: &str = env!("CARGO_MANIFEST_DIR");\n'
        open(main_rs, "w").write(text.replace("fn main() {", 'fn main() {\n    print!("{}", include_str!("note.txt"));\n    println!("{}", HERE);\n    println!("shared {}", smid::shared());', 1))
        # A crate no step edits includes a file of the workspace that is outside its package.
        open(os.path.join(ws, SHARED), "w").write(f"shared of {at} in {RUN}")
        mid_rs = os.path.join(ws, MID)
        text = open(mid_rs).read()
        assert "pub fn seeded() -> u32 {" in text
        open(mid_rs, "w").write(text.replace("pub fn seeded() -> u32 {", "pub fn shared() -> &'static str {\n    include_str!(\"../../shared.txt\")\n}\n\npub fn seeded() -> u32 {", 1))
        # A checkout read as the first one links what rustc built of the first.
        if not (OVERLAY and checkouts):
            fx = Fixture(ws, crates, ["-p", "sapp"])
            fx.rustc_build()
        obj, patch, binary = (os.path.join(work, f"sapp{at}.{n}") for n in ("o", "patch.o", "bin"))
        link = list(fx.link_args)
        link = linkline.with_output(linkline.ahead(link, [patch, obj], RUSTD), binary)
        symbols = [x for rlib in fx.rlibs + sysroot_rlibs() for x in ("--symbols", rlib)]
        checkouts.append({"ws": ws, "obj": obj, "patch": patch, "bin": binary, "link": linkline.join(link),
                          "symbols": symbols, "reference": os.path.join(work, f"reference{at}")})
    first = checkouts[0]
    out = open(log_path, "a")
    daemon = subprocess.Popen(
        [RUSTD, first["ws"], *TARGET_ARGS, *[x for c in crates for x in ("--crate", c)], "--out", first["obj"], "--socket", socket,
         "--patch", first["patch"], "--link-cmd", first["link"], *splice(first), *first["symbols"],
         *[x for other in checkouts[1:] if not JOIN and not OVERLAY for x in ("--also", other["ws"])]],
        stderr=out, stdout=out,
        env={**os.environ, **({"RUSTD_OVERLAY": "1"} if OVERLAY else {}), "RUSTD_SPLIT": "1" if SPLIT else "0"})
    while "watching" not in open(log_path).read():
        if daemon.poll() is not None:
            raise SystemExit(f"the daemon did not start: {log_path}")
        time.sleep(0.05)

    def run(path):
        try:
            ran = subprocess.run([*RUNNER, path], capture_output=True, text=True, timeout=30)
        except Exception as error:
            return f"did not run: {error}"
        return ran.stdout + (f"[exit {ran.returncode}]" if ran.returncode else "")

    wrong = asked = 0
    for what, edits, order, broken in STEPS:
        for at, path, old, new in edits:
            path = os.path.join(checkouts[at]["ws"], path)
            if old is None:
                open(path, "w").write(new)
                continue
            if new is None:
                os.remove(path)
                continue
            text = open(path).read()
            assert old in text, (what, old)
            open(path, "w").write(text.replace(old, new, 1))
        time.sleep(0.02)
        print(what, flush=True)
        together = "--together" in sys.argv

        def ask(at):
            checkout = checkouts[at]
            return time.time(), subprocess.Popen(
                [RUSTD, "sync", socket, "--project", checkout["ws"], "--crate", "sapp", "--out", checkout["obj"],
                 "--patch", checkout["patch"], "--link-cmd", checkout["link"], *splice(checkout), *checkout["symbols"]],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

        # A program asked for twice in a step is asked for the second time after the others.
        asking = {at: ask(at) for at in dict.fromkeys(order)} if together else {}
        for at in order:
            checkout = checkouts[at]
            began, reply = asking.pop(at, None) or ask(at)
            try:
                reply = reply.communicate(timeout=120)[0].strip()
            except subprocess.TimeoutExpired:
                reply.kill()
                print(open(log_path, errors="replace").read()[-6000:], flush=True)
                reply = "no answer in 120 s"
            took = (time.time() - began) * 1000
            outputs = None
            cargo = subprocess.run(["cargo", "build", "-q", "-p", "sapp", *TARGET_ARGS], cwd=checkout["ws"], capture_output=True,
                                   text=True, env={**os.environ, "CARGO_TARGET_DIR": checkout["reference"]})
            assert (cargo.returncode != 0) == (at in broken), cargo.stderr[-2000:]
            if daemon.poll() is not None:
                verdict = "DAEMON DIED"
            elif reply.startswith("no answer"):
                verdict = "NO ANSWER"
            elif at in broken:
                verdict = "refused" if not reply.startswith("ok") else "ANSWERED OK"
            elif not reply.startswith("ok"):
                verdict = "REFUSED"
            else:
                outputs = run(checkout["bin"]), run(built(checkout["reference"], "sapp"))
                verdict = "same" if outputs[0] == outputs[1] else "DIFFERENT OUTPUT"
            asked += 1
            wrong += verdict.isupper()
            print(f"    checkout {at} {verdict:16} {took:6.0f} ms  {reply[:90]}", flush=True)
            if verdict == "DIFFERENT OUTPUT":
                print(f"      rustd: {outputs[0]!r}\n      cargo: {outputs[1]!r}", flush=True)
            if daemon.poll() is not None:
                print(open(log_path, errors="replace").read()[-6000:], flush=True)
                raise SystemExit(f"the daemon died: {log_path}")
    daemon.kill()
    print(f"{asked - wrong} of {asked} right; log {log_path}")
    sys.exit(1 if wrong else 0)


if __name__ == "__main__":
    main()
