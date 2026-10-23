#!/usr/bin/env python3
"""Edit latency by phase on programs of different sizes, one daemon per program.

usage: scaling.py OUT.json name=WORKSPACE:PACKAGE:CRATE[,CRATE...][:RUN_ARG] ...

For each program: builds it with cargo, starts the daemon on the crates with a patch object and a
link command, and throws the same edits at it SCALING_REPEAT times each (default 5), every one
followed by its revert. Edits are made to the file holding `fn main`. The edit that prints is
checked by running the program. Appends one record per program to OUT.json.

SCALING_LD: a directory holding the `ld` to link with. SCALING_FIXTURE_<name>: a JSON file with
the `link_args` of a build made elsewhere, with SCALING_SYMBOLS_<name> the symbol arguments.
"""
import json, os, re, shlex, statistics, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
os.environ.setdefault("RUSTUP_TOOLCHAIN", open(os.path.join(HERE, "toolchain")).read().strip())
os.environ["RUSTD_STATS"] = "1"
import linkline
from difftest import Fixture, RUSTD, sysroot_rlibs

MARK = "rustd-scaling-edit"
MAIN = re.compile(r"fn main\(\)[^{;]*\{\n")
NEW_FN = "\nfn rustd_new_item(x: u32) -> u32 { x + 1 }\n"
EDITS = [
    ("blank line at top", lambda t: "\n" + t),
    ("comment appended", lambda t: t + "// edit\n"),
    ("new private fn", lambda t: t + NEW_FN),
    ("body: unused let", lambda t: MAIN.sub(lambda m: m[0] + "let _rustd_edit = 1u32;\n", t, 1)),
    ("body: println", lambda t: MAIN.sub(lambda m: m[0] + f'println!("{MARK}");\n', t, 1)),
]
# The first function in a file that is written plainly: an edit to its body is seen by nothing else.
PLAIN_FN = re.compile(r"^ *(?:pub(?:\([a-z]+\))? )?fn \w+\([^)]*\)[^{;]*\{\n", re.M)
ELSEWHERE = [
    ("comment appended", lambda t: t + "// edit\n"),
    ("new private fn", lambda t: t + NEW_FN),
    ("body: unused let", lambda t: PLAIN_FN.sub(lambda m: m[0] + "let _rustd_edit = 1u32;\n", t, 1)),
]
BUILD = re.compile(
    r"edit \(apply (\S+)\): compiled (\d+) of (\d+) fns \(\+(\d+) instances\) in (\S+) .*\n(?:  .*\n)*"
    r"stats: (\d+) of (\d+) functions compiled.*\n(?:(?:no )?patch: .*\n)?.*\n(?:link: .*\n)?"
    r"(?:timeline-us: (.*)\n)?(?:asked: .*\n)?edit-to-binary: (\S+)")


def measure(name, spec, repeat):
    ws, package, crates, *run_arg = spec.split(":")
    crates = crates.split(",")
    fx = Fixture(ws, crates, ["-p", package])
    meta = json.loads(subprocess.check_output(["cargo", "metadata", "--format-version", "1", "--no-deps"], cwd=fx.ws))
    fx.target_args += ["--bin", next(t["name"] for p in meta["packages"] if p["name"] == package
                                     for t in p["targets"] if "bin" in t["kind"])]
    if fixture := os.environ.get(f"SCALING_FIXTURE_{name}"):
        fx.link_args = json.load(open(fixture))["link_args"]
        symbols = open(os.environ[f"SCALING_SYMBOLS_{name}"]).read().split()
    else:
        fx.rustc_build()
        symbols = [x for rlib in fx.rlibs + sysroot_rlibs() for x in ("--symbols", rlib)]
    link = list(fx.link_args)
    obj, patch, binary = (os.path.join(fx.work, n) for n in ("rustd.o", "rustd.patch.o", "bin-rustd"))
    link = linkline.ahead(link, [patch, obj], RUSTD)
    link[link.index("-o") + 1] = binary
    if (ld := os.environ.get("SCALING_LD")) and "-fuse-ld=lld" in link:
        link = [a for a in link if not (a.startswith("-B") and "gcc-ld" in a)]
        link[link.index("-fuse-ld=lld")] = "-B" + ld
    # SCALING_SYNC: each build is asked for once the file is written, as `rustd sync` does.
    socket = os.path.join(fx.work, "rustd.sock") if os.environ.get("SCALING_SYNC") else None
    trigger = ["--socket", socket] if socket else ["--watch"]
    # SCALING_SPLICE: edits are added to the linked binary where that can be done.
    splice = ["--splice", binary] if os.environ.get("SCALING_SPLICE") else []
    log_path = os.path.join(fx.work, "daemon.log")
    out, log = open(log_path, "a"), open(log_path)
    start = time.time()
    daemon = subprocess.Popen(
        [RUSTD, os.path.dirname(fx.touch) if fixture else fx.ws, *[x for c in crates for x in ("--crate", c)],
         "--out", obj, *trigger, "--patch", patch, "--link-cmd", shlex.join(link), *splice, *symbols],
        stderr=out, stdout=out)

    def wait(pattern, seen):
        while True:
            log.seek(0)
            found = re.findall(pattern, log.read())
            if len(found) > seen:
                return found
            if daemon.poll() is not None:
                log.seek(0)
                raise SystemExit(f"{name}: daemon died:\n{log.read()[-3000:]}")
            time.sleep(0.01)

    original = open(fx.touch).read()
    # What to write for each edit: the file with `fn main`, then SCALING_FILES (paths in the
    # workspace) one at a time, then a body in each of them at once.
    jobs = [(kind, fx.touch, {fx.touch: (apply(original), original)}) for kind, apply in EDITS]
    others = [os.path.join(fx.ws, f) for f in os.environ.get("SCALING_FILES", "").split(",") if f]
    texts = {path: open(path).read() for path in others}
    for path in others:
        jobs += [(kind, path, {path: (apply(texts[path]), texts[path])}) for kind, apply in ELSEWHERE]
    if others:
        body = ELSEWHERE[-1][1]
        jobs.append(("body: unused let", "all", {path: (body(texts[path]), texts[path]) for path in others}))
    # SCALING_KEEP: instead, this many body edits that stay, each in another function, going
    # round the files: what an edit costs with the earlier ones still in the patch.
    keep = int(os.environ.get("SCALING_KEEP", "0"))
    if keep:
        jobs, now = [], dict(texts)
        spots = {path: [m.end() for m in PLAIN_FN.finditer(text)] for path, text in texts.items()}
        for k in range(keep):
            path = others[k % len(others)]
            nth = k // len(others)
            if nth >= len(spots[path]):
                continue
            # Earlier edits to the file sit above this one or below it: count those above.
            at = spots[path][nth] + sum(len(f"let _rustd_edit = {j}u32;\n") for j in range(k) if others[j % len(others)] == path and j // len(others) < nth)
            new = now[path][:at] + f"let _rustd_edit = {k}u32;\n" + now[path][at:]
            jobs.append((f"kept body edit {k}", path, {path: (new, now[path])}))
            now[path] = new
        repeat = 1
    samples, done, wrong = [], 0, []
    try:
        wait(r"watching \d+ files", 0)
        warmup = time.time() - start
        log.seek(0)
        text = log.read()
        cold = re.search(r"cold: compiled (\d+) of (\d+) fns \(\+(\d+) instances\)", text)
        rounds = re.search(r"(\d+) rounds", text)
        print(f"{name}: warm in {warmup:.1f}s, {cold[1]} of {cold[2]} fns, {cold[3]} instances", flush=True)
        for turn in range(repeat):
            for kind, where, writes in jobs:
                assert all(new != old for new, old in writes.values()), (name, kind, where)
                for revert in (False,) if keep else (False, True):
                    time.sleep(0.3)
                    for path, texts_ in writes.items():
                        open(path, "w").write(texts_[revert])
                    if socket:
                        reply = subprocess.check_output([RUSTD, os.environ.get("SCALING_REQUEST", "sync"), socket], text=True)
                        assert reply.startswith(("ok patch=" + patch, "ok object=" + obj)), reply
                    found = wait(BUILD.pattern, done)
                    done = len(found)
                    b = found[-1]
                    patched = "\npatch: " in log_tail(log)
                    steps = {k: int(v) / 1000 for k, v in (kv.split("=") for kv in b[7].split(";", 1)[0].split())}
                    samples.append({"edit": kind, "file": os.path.relpath(where, fx.ws) if where != "all" else where, "revert": revert, "turn": turn, "steps_ms": steps,
                                    "recompiled": int(b[5]), "cached": int(b[6]), "patched": patched})
                    if kind == "body: println" and where == fx.touch:
                        ran = subprocess.run([binary, *run_arg], capture_output=True, text=True, timeout=60)
                        if (MARK in ran.stdout) == revert:
                            wrong.append((turn, revert, ran.stdout[:200]))
        rss = int(subprocess.check_output(["ps", "-o", "rss=", "-p", str(daemon.pid)])) // 1024
    finally:
        daemon.kill()
        open(fx.touch, "w").write(original)
        for path, text in texts.items():
            open(path, "w").write(text)
    record = {"name": name, "fns": int(cold[1]), "of": int(cold[2]), "instances": int(cold[3]),
              "rounds": int(rounds[1]) if rounds else None, "warmup_s": warmup, "rss_mb": rss,
              "cached": samples[-1]["cached"], "wrong": wrong, "samples": samples, "log": log_path}
    edits = [s for s in samples if not s["revert"]]
    ours = [sum(v for k, v in s["steps_ms"].items() if k != "link") for s in edits]
    print(f"{name}: cached {record['cached']}, non-link median {statistics.median(ours):.0f} ms, "
          f"link median {statistics.median(s['steps_ms'].get('link', 0) for s in edits):.0f} ms, "
          f"patched {sum(s['patched'] for s in samples)}/{len(samples)}, wrong output {len(wrong)}", flush=True)
    return record


def log_tail(log):
    log.seek(0)
    text = log.read()
    return text[text.rfind("\nedit (apply"):]


def main():
    out, repeat = sys.argv[1], int(os.environ.get("SCALING_REPEAT", "5"))
    records = json.load(open(out)) if os.path.exists(out) else []
    for arg in sys.argv[2:]:
        name, spec = arg.split("=", 1)
        records = [r for r in records if r["name"] != name] + [measure(name, spec, repeat)]
        json.dump(records, open(out, "w"), indent=1)


main()
