#!/usr/bin/env python3
"""Edit latency of the daemon on crates of a dioxus checkout.

usage: dxedits.py CHECKOUT crate[,crate...] SYMBOLS_FILE

Starts the daemon on the crates, waits for the first build, applies each edit and reports the
time the daemon took to rebuild and how many functions it compiled again.
"""
import json, os, re, shlex, subprocess, sys, tempfile, time
import linkline

HERE = os.path.dirname(os.path.abspath(__file__))
os.environ.setdefault("RUSTUP_TOOLCHAIN", open(os.path.join(HERE, "toolchain")).read().strip())
os.environ["RUSTD_STATS"] = "1"
RUSTD = os.environ.get("RUSTD_BIN") or os.path.join(HERE, "../target/release/rustd")
BODY = "let _rustd_edit = 1u32;"
ASYNC_MAIN = "async fn main() -> ExitCode {\n"
NEW_FN = "\nfn rustd_new_item(x: u32) -> u32 { x + 1 }\n"
# The first function in a file that is written plainly.
PLAIN_FN = re.compile(r"^ *(?:pub(?:\([a-z]+\))? )?fn \w+\([^)]*\)[^{;]*\{\n", re.M)


def main():
    root, crates, symbols = sys.argv[1], sys.argv[2].split(","), open(sys.argv[3]).read().split()
    core = os.path.join(root, "packages/core/src")
    edits = [
        ("blank line at top", f"{core}/virtual_dom.rs", lambda t: "\n" + t),
        ("comment appended", f"{core}/virtual_dom.rs", lambda t: t + "// edit\n"),
        ("1 function body (mark_dirty)", f"{core}/virtual_dom.rs",
         lambda t: t.replace("pub fn mark_dirty(&mut self, id: ScopeId) {\n", "pub fn mark_dirty(&mut self, id: ScopeId) {\n" + BODY + "\n", 1)),
        ("1 function body (rebuild, generic)", f"{core}/virtual_dom.rs",
         lambda t: t.replace("pub fn rebuild(&mut self, to: &mut impl crate::MultiWriter) {\n", "pub fn rebuild(&mut self, to: &mut impl crate::MultiWriter) {\n" + BODY + "\n", 1)),
        ("new private fn", f"{core}/virtual_dom.rs", lambda t: t + NEW_FN),
        ("new private fn in lib.rs", f"{core}/lib.rs", lambda t: t + NEW_FN),
    ]
    if "dx" in crates:
        cli = os.path.join(root, "packages/cli/src")
        wrap = "pub fn is_wrapping_rustc() -> bool {\n"
        edits = [
            ("blank line at top", f"{cli}/rustcwrapper.rs", lambda t: "\n" + t),
            ("comment appended", f"{cli}/build/builder.rs", lambda t: t + "// edit\n"),
            ("1 function body (is_wrapping_rustc)", f"{cli}/rustcwrapper.rs", lambda t: t.replace(wrap, wrap + BODY + "\n", 1)),
            ("new private fn", f"{cli}/build/builder.rs", lambda t: t + NEW_FN),
            ("new private fn in main.rs", f"{cli}/main.rs", lambda t: t + NEW_FN),
            ("what `dx doctor --help` prints", f"{cli}/cli/mod.rs", lambda t: t.replace("/// Diagnose installed", "/// Diagnose (edited) installed", 1)),
            ("a static's value", f"{cli}/cli/create.rs", lambda t: t.replace('"gh:dioxuslabs/dioxus-template"', '"gh:dioxuslabs/edited-template"', 1)),
            # `main` is an `async fn`: tokio's functions are instantiated with its future.
            ("async main: a statement", f"{cli}/main.rs", lambda t: t.replace(ASYNC_MAIN, ASYNC_MAIN + "    std::hint::black_box(1u32);\n", 1)),
            ("async main: a local", f"{cli}/main.rs", lambda t: t.replace(ASYNC_MAIN, ASYNC_MAIN + "    " + BODY + "\n", 1)),
        ]
    if "dx" in crates and len(crates) > 1:
        # The crates of the workspace that dx is built from: edits far from the program's top.
        def body(t):
            return PLAIN_FN.sub(lambda m: m[0] + BODY + "\n", t, 1)
        packages = os.path.join(root, "packages")
        elsewhere = [("core", f"{core}/virtual_dom.rs"), ("rsx", f"{packages}/rsx/src/element.rs"),
                     ("autofmt", f"{packages}/autofmt/src/writer.rs"), ("generational-box", f"{packages}/generational-box/src/lib.rs"),
                     ("html", f"{packages}/html/src/events/mod.rs")]
        for crate, path in elsewhere:
            edits.append((f"{crate}: 1 function body", path, body))
            edits.append((f"{crate}: new private fn", path, lambda t: t + NEW_FN))
        edits.append(("5 crates and dx: 1 function body each", [path for _, path in elsewhere] + [f"{cli}/rustcwrapper.rs"], body))
    work = os.path.join(root, "work")
    log_path = os.path.join(work, "dxedits.log")
    open(log_path, "w").close()
    out = open(log_path, "a")
    log = open(log_path)
    args = [x for c in crates for x in ("--crate", c)]
    # DXEDITS_PATCH: the daemon links after each build, with a patch object ahead of the first one.
    binary = os.path.join(work, "dx-rustd-bin")
    if os.environ.get("DXEDITS_PATCH"):
        link = list(json.load(open(os.path.join(work, "fixture.json")))["link_args"])
        patch = os.path.join(work, "dx.patch.o")
        link = linkline.ahead(link, [patch, os.path.join(work, "dx.o")], RUSTD)
        link[link.index("-o") + 1] = binary
        # DXEDITS_LD: a directory holding the `ld` to link with, instead of rustc's lld.
        if ld := os.environ.get("DXEDITS_LD"):
            link = [a for a in link if not (a.startswith("-B") and "gcc-ld" in a)]
            link[link.index("-fuse-ld=lld")] = "-B" + ld
        args += ["--patch", patch, "--link-cmd", shlex.join(link)]
        # Edits are added to the linked binary where that can be done; RUSTD_SPLICE=0 links each in full.
        args += ["--binary", binary]
    # DXEDITS_REQUEST: `sync` or `patch`; each build is then asked for once the file is written.
    request = os.environ.get("DXEDITS_REQUEST")
    socket = os.path.join(work, "rustd.sock")
    trigger = ["--socket", socket] if request else ["--watch"]
    start = time.time()
    daemon = subprocess.Popen([RUSTD, os.path.join(root, "packages/cli"), *args, "--out", os.path.join(work, "dx.o"), *trigger, *symbols],
                              stderr=out, stdout=out)

    def wait(pattern, seen):
        while True:
            log.seek(0)
            found = re.findall(pattern, log.read())
            if len(found) > seen:
                return found
            if daemon.poll() is not None:
                log.seek(0)
                raise SystemExit(f"daemon died:\n{log.read()[-3000:]}")
            time.sleep(0.01)

    done = 0
    try:
        wait(r"watching \d+ files", 0)
        rss = int(re.search(r"VmRSS:\s+(\d+)", open(f"/proc/{daemon.pid}/status").read())[1]) // 1024
        print(f"warmup: {time.time() - start:.1f}s, {rss} MB")
        log.seek(0)
        print(re.search(r"cold: .*", log.read())[0])
        only = os.environ.get("DXEDITS_ONLY")
        # DXEDITS_PERF: a directory that gets one profile of the daemon and its linker per edit.
        perf_dir = os.environ.get("DXEDITS_PERF")
        repeat = int(os.environ.get("DXEDITS_REPEAT", "1"))
        samples = []
        # DXEDITS_PERF_WHOLE: one profile of the daemon over every edit, at this path.
        whole = None
        if whole_path := os.environ.get("DXEDITS_PERF_WHOLE"):
            whole = subprocess.Popen(["perf", "record", "-F", "4999", "-g", "-o", whole_path, "-p", str(daemon.pid)],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            time.sleep(1.5)
        for turn, (name, path, apply) in enumerate(edits * repeat):
            if only and not any(o in name for o in only.split(",")):
                continue
            paths = path if isinstance(path, list) else [path]
            originals = [open(p).read() for p in paths]
            editeds = [apply(o) for o in originals]
            assert all(e != o for e, o in zip(editeds, originals)), name
            for label, texts in ((name, editeds), ("  (revert)", originals)):
                perf = None
                if perf_dir and label == name and turn >= len(edits) * (repeat - 1):
                    slug = re.sub(r"\W+", "-", name).strip("-")
                    perf = subprocess.Popen(["perf", "record", "-F", "1999", "-g", "--inherit", "-o", f"{perf_dir}/{slug}.data", "-p", str(daemon.pid)],
                                            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
                    time.sleep(1.5)
                saved = time.time()
                for p, text in zip(paths, texts):
                    open(p, "w").write(text)
                if request:
                    reply = subprocess.check_output([RUSTD, request, socket], text=True)
                    print(f"    {reply.strip()}  round trip {(time.time() - saved) * 1000:.0f}ms")
                found = wait(r"edit \(apply (\S+)\): compiled (\d+) of (\d+) fns \(\+(\d+) instances\) in (\S+) .*\n(?:  .*\n)*stats: (\d+) of (\d+) functions compiled.*\n(?:(?:no )?patch: .*\n)?.*\n(?:link: .*\n)?(?:timeline-us: (.*)\n)?(?:asked: .*\n)?edit-to-binary: (\S+)", done)
                done = len(found)
                b = found[-1]
                wall = (os.path.getmtime(binary) - saved) * 1000 if "--patch" in args else None
                if perf:
                    perf.send_signal(2)
                    perf.wait()
                print(f"{label:38} {'edit-to-binary' if '--patch' in args else 'edit-to-object'} {b[8]:>8}  recompiled {b[5]:>5} of {b[6]}"
                      + (f"  save-to-binary-on-disk {wall:.0f}ms" if wall else ""), flush=True)
                steps = dict((k, int(v) / 1000) for k, v in (kv.split("=") for kv in b[7].split(";", 1)[0].split()))
                samples.append({"edit": name, "files": len(paths), "revert": label != name, "wall_ms": wall, "steps_ms": steps, "recompiled": int(b[5]), "profiled": perf is not None})
                if "--patch" in args and "doctor" in name:
                    ran = subprocess.run([binary, "doctor", "--help"], capture_output=True, text=True)
                    print("    doctor --help:", ran.returncode, ran.stdout.splitlines()[:1])
                if "--patch" in args and "static" in name:
                    # `dx new` logs the default template, which is the edited static, before it asks anything.
                    with tempfile.TemporaryDirectory() as scratch:
                        ran = subprocess.run(["timeout", "5", "script", "-qc", f"{binary} new app --yes --verbose", "/dev/null"],
                                             capture_output=True, text=True, cwd=scratch)
                    print("    dx new:", re.findall(r'"gh:[^"]*"', ran.stdout)[:1])
        if whole:
            whole.send_signal(2)
            whole.wait()
        rss = int(re.search(r"VmRSS:\s+(\d+)", open(f"/proc/{daemon.pid}/status").read())[1]) // 1024
        print(f"rss after edits: {rss} MB")
        json.dump(samples, open(os.path.join(work, "timeline.json"), "w"), indent=1)
    finally:
        daemon.kill()


main()
