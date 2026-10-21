#!/usr/bin/env python3
"""fuzz.py: generated programs, what rustd's build of each prints against what rustc's prints.

usage: fuzz.py smoke                                   a short run on fixed seeds, for CI
       fuzz.py run --seed S --rounds N [--jobs J]      the long mode: N programs from seed S
       fuzz.py repro SEED-ROUND [CASE ...]             one program again, or only some of its cases
       fuzz.py check [FILE.rs ...] [--jobs J]          reductions under found/, each on its own
       fuzz.py report DIR                              adds up the logs a run left in DIR

A round is one program (`gen.py`) of `--cases` cases, built once by cargo and once by rustd under
each backend in `--backends`, and run. A finding is a case whose output differs, a function left
to rustc, or a build rustd did not finish. Each finding is reduced (the cases, then the lines of
the one case left) and written to `found/` with the seed that makes it again; a cause already
found in the run is counted and not reduced a second time.

RUSTD_BIN names the rustd under test. The exit status is 1 when there is a finding.
"""
import argparse, collections, contextlib, json, multiprocessing, os, re, shutil, subprocess, sys, tempfile, time

try:
    import resource
except ImportError:  # Windows: a generated program is held to its time alone.
    resource = None

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)
import gen
from difftest import Fixture, RUNNER, bucket, minimize

FOUND = os.path.join(HERE, "found")
SMOKE = {"seed": "smoke", "rounds": 2, "cases": 25}
# What `--backends` can name. `llvm` is the pair the other harnesses run; the two after it are
# the other ends: no passes, and the passes with LLVM's own instruction selection.
BACKENDS = {
    "cranelift": {"RUSTD_BACKEND": "cranelift"},
    "llvm": {"RUSTD_BACKEND": "llvm", "RUSTD_OPT": "2", "RUSTD_EMIT": "fast"},
    "llvm-O0": {"RUSTD_BACKEND": "llvm", "RUSTD_OPT": "0", "RUSTD_EMIT": "fast"},
    "llvm-full": {"RUSTD_BACKEND": "llvm", "RUSTD_OPT": "2", "RUSTD_EMIT": "optimized"},
}
MANIFEST = """[package]
name = "fz"
version = "0.0.0"
edition = "{edition}"

[profile.dev]
debug = 0
"""
# Seconds a generated program may run, and bytes it may map, before it is the generator's fault.
RUN_SECONDS, RUN_BYTES = 120, 8 << 30


class Finding:
    """One way a build went wrong: what kind, in which case, and a key that names its cause."""

    def __init__(self, kind, case, key, detail):
        self.kind, self.case, self.key, self.detail = kind, case, key, detail

    def record(self):
        return {"kind": self.kind, "case": self.case, "key": self.key, "detail": self.detail[:2000]}


class Project:
    """A one-crate cargo project that programs are written into and built from, by both compilers."""

    def __init__(self, directory):
        self.dir = directory
        os.makedirs(os.path.join(directory, "src"), exist_ok=True)
        self.main = os.path.join(directory, "src", "main.rs")
        self.fx = None
        self.edition = None

    def write(self, modules, edition):
        if edition != self.edition:
            open(os.path.join(self.dir, "Cargo.toml"), "w").write(MANIFEST.format(edition=edition))
            self.edition = edition
        open(self.main, "w", encoding="utf-8").write(gen.render(modules))
        if self.fx is None:
            self.fx = Fixture(self.dir, ["fz"], ["-p", "fz"], touch=self.main)
            self.fx.rustd_timeout = 600

    def reference(self, modules, edition):
        """Builds with cargo and runs. Returns what rustc said when it turned the program down."""
        self.write(modules, edition)
        try:
            self.fx.rustc_build()
        except SystemExit as error:
            return str(error)
        self.expected = run(self.fx.reference)
        return None

    def rustd(self, backend):
        """Builds with rustd under a backend and compares. Returns the findings and the functions compiled."""
        os.environ.update(BACKENDS[backend])
        # rustd appends the layouts of every build to this, and nothing here reads it.
        with contextlib.suppress(FileNotFoundError):
            os.remove(self.fx.layout_log)
        try:
            self.fx.rustd_build()
        except SystemExit as error:
            text = str(error)
            return [Finding("crash", None, crash_key(text), text[-3000:])], 0
        rows = [row for rows in self.fx.reports.values() for row in rows]
        findings = [Finding("left", case_of(row[1]), bucket(row[2]), f"{row[1]}: {row[2]}")
                    for row in rows if row[0] == "skipped" and "no rustc symbol" not in row[2]]
        findings += differences(self.expected, run(self.fx.binary))
        return findings, sum(row[0] == "compiled" for row in rows)


def run(binary):
    """What a program prints and how it ends, within the limits a generated program has."""
    limit = (lambda: resource.setrlimit(resource.RLIMIT_AS, (RUN_BYTES, RUN_BYTES))) if resource else None
    try:
        done = subprocess.run([*RUNNER, binary], capture_output=True, timeout=RUN_SECONDS, preexec_fn=limit)
    except subprocess.TimeoutExpired:
        return "timeout", "", ""
    return done.returncode, done.stdout.decode(errors="replace"), done.stderr.decode(errors="replace")


def per_case(stdout):
    """The output split by case: what each printed, up to and including its checksum line."""
    cases, lines = {}, []
    for line in stdout.splitlines():
        lines.append(line)
        found = re.fullmatch(r"(c\d+) [0-9a-f]{16} (ok|panic)", line)
        if found:
            cases[found.group(1)] = "\n".join(lines)
            lines = []
    return cases, "\n".join(lines)


def differences(expected, got):
    """A finding per case whose output is not what rustc's program printed."""
    if expected == got:
        return []
    want, _ = per_case(expected[1])
    have, rest = per_case(got[1])
    findings = []
    for name, text in want.items():
        if name not in have:
            # The program died in the first case it did not finish.
            detail = f"rustd's program ended with status {got[0]} in this case\n{rest[-600:]}\n{got[2][-600:]}"
            findings.append(Finding("differs", name, "died", detail))
            break
        if have[name] != text:
            findings.append(Finding("differs", name, difference_key(text, have[name]), f"rustc:\n{text}\nrustd:\n{have[name]}"))
    if not findings:
        findings.append(Finding("differs", None, "status", f"rustc: status {expected[0]} {expected[2][-300:]}\nrustd: status {got[0]} {got[2][-300:]}"))
    return findings


def difference_key(want, have):
    """What kind of difference two outputs of a case have: enough to tell causes apart roughly."""
    a, b = want.splitlines(), have.splitlines()
    for x, y in zip(a, b):
        if x != y:
            if x.startswith("panic: panicked at") and y.startswith("panic: panicked at"):
                return "panic location"
            if x.startswith("panic:") != y.startswith("panic:"):
                return "panics differ"
            return "panic message" if len(a) > 1 and x is not a[-1] else "checksum"
    return "panics differ"


def crash_key(text):
    """The line of a failed build that says why, without what changes from program to program."""
    lines = [line for line in text.splitlines() if line.strip()]
    said = next((line for line in lines if "panicked at" in line or line.startswith("error")), lines[-1] if lines else "")
    said = re.sub(r"\bc\d+::|\b[a-zA-Z]\d+\b|0x[0-9a-f]+|\d+", "_", said)
    return said.strip()[:160]


def case_of(function):
    found = re.search(r"\bc\d+\b", function)
    return found.group(0) if found else None


def edition_of(seed):
    """Half of the programs are built as 2021 and half as 2024: drop order differs between them."""
    return "2021" if sum(seed.encode()) % 2 else "2024"


# ---- reduction ------------------------------------------------------------------------------


class Reducer:
    """Makes a program smaller while one backend still shows a finding of the same kind and key."""

    def __init__(self, project, edition, backend, finding, budget):
        self.project, self.edition, self.backend, self.finding = project, edition, backend, finding
        self.deadline = time.time() + budget
        self.tests, self.shown = 0, finding

    def shows(self, modules):
        """Whether the program is still accepted by rustc and still shows the finding."""
        if not modules or time.time() > self.deadline:
            return False
        self.tests += 1
        if self.project.reference(modules, self.edition) is not None:
            return False
        if self.project.expected[0] != 0:
            return False
        findings, _ = self.project.rustd(self.backend)
        same = [f for f in findings if f.kind == self.finding.kind and f.key == self.finding.key]
        # What the smaller program shows is what gets filed with it.
        self.shown = same[0] if same else self.shown
        return bool(same)

    def reduce(self, modules):
        modules = self.fewer_cases(modules)
        if len(modules) == 1:
            name, lines = modules[0]
            modules = [(name, self.fewer_lines(name, lines))]
        return modules

    def fewer_cases(self, modules):
        alone = [m for m in modules if m[0] == self.finding.case]
        if alone and self.shows(alone):
            return alone
        return minimize(modules, self.shows)

    def fewer_lines(self, name, lines):
        """Removes items and statements, outermost first, until a pass removes nothing."""
        while True:
            before = len(lines)
            lines = self.pass_over(name, lines, 0, len(lines))
            if len(lines) == before or time.time() > self.deadline:
                return lines

    def pass_over(self, name, lines, start, end):
        """Tries to drop each unit of `lines[start:end]`, last first, then looks inside those that stay."""
        for first, last in reversed(units(lines, start, end)):
            without = lines[:first] + lines[last + 1:]
            if self.shows([(name, without)]):
                lines = without
                continue
            if last > first:
                # A block that cannot go may still give up its braces, or what is inside them.
                bare = lines[:first] + lines[first + 1:last] + lines[last + 1:]
                if opens_scope(lines[first]) and self.shows([(name, bare)]):
                    lines = bare
                    continue
                lines = self.pass_over(name, lines, first + 1, last)
        return lines


def units(lines, start, end):
    """The statements and items of a range of lines: single lines, and blocks from `{` to its `}`."""
    found, depth, first = [], 0, None
    for at in range(start, end):
        text = lines[at]
        opened, closed = text.count("{"), text.count("}")
        if depth == 0 and first is None:
            first = at
        # A line like `} else {` continues the unit it closes, and an attribute belongs to what follows it.
        depth = max(0, depth + opened - closed)
        if depth == 0 and not text.strip().startswith("#["):
            found.append((first, at))
            first = None
    return found


def opens_scope(line):
    """Whether a block's first line only opens a scope, so that its body can stand without it."""
    text = line.strip()
    return text == "{" or text.startswith(("if ", "'l")) and "let " not in text


# ---- a round ----------------------------------------------------------------------------------


def write_found(seed, edition, backend, finding, modules, tests):
    """Files a reduction: the case's module, under a comment that says how it was found."""
    os.makedirs(FOUND, exist_ok=True)
    slug = re.sub(r"[^a-z0-9]+", "-", f"{finding.kind}-{finding.key}".lower()).strip("-")[:60]
    path = os.path.join(FOUND, f"{slug}-{seed}-{finding.case or 'all'}.rs")
    head = [f"// Found by fuzz.py: seed {seed}, case {finding.case}, edition {edition}, backend {backend}.",
            f"// {finding.kind}: {finding.key}", f"// Reduced in {tests} builds. Again: fuzz.py check {os.path.basename(path)}"]
    head += ["// " + line for line in finding.detail.splitlines()[:12]]
    open(path, "w", encoding="utf-8").write("\n".join(head) + "\n" + "\n\n".join(gen.module(name, lines) for name, lines in modules) + "\n")
    return path


def read_found(path):
    """The modules of a file under found/ and the edition it was found with."""
    text = open(path, encoding="utf-8").read()
    edition = re.search(r"edition (\d+)", text).group(1)
    modules = []
    for name, body in re.findall(r"^mod (c\d+) \{\n    use super::\*;\n(.*?)^\}$", text, re.M | re.S):
        modules.append((name, body.rstrip("\n").split("\n")))
    return modules, edition


def round_of(project, seed, cases, backends, seen, budget, only=()):
    """One program through both compilers. Returns the record of the round for the log."""
    began = time.time()
    modules, functions, coverage = gen.program(seed, cases)
    if only:
        modules = [m for m in modules if m[0] in only]
    edition = edition_of(seed)
    record = {"seed": seed, "cases": len(modules), "generated_functions": functions, "coverage": coverage, "backends": {}}
    rejected = project.reference(modules, edition)
    if rejected is not None:
        record["rejected"] = rejected[-1500:]
        return record
    if project.expected[0] != 0:
        record["reference_failed"] = str(project.expected[0])
        return record
    results = {backend: project.rustd(backend) for backend in backends}
    for backend, (findings, compiled) in results.items():
        entry = record["backends"][backend] = {"compiled": compiled, "findings": [f.record() for f in findings]}
        for finding in findings:
            print(f"  {seed} {backend}: {finding.kind} in {finding.case}: {finding.key}", flush=True)
            cause = (finding.kind, finding.key)
            if cause in seen or budget <= 0:
                continue
            seen.add(cause)
            reducer = Reducer(project, edition, backend, finding, budget)
            reduced = reducer.reduce(modules)
            reducer.deadline += 120
            if reducer.tests and reducer.shows(reduced):
                path = write_found(seed, edition, backend, reducer.shown, reduced, reducer.tests)
                entry.setdefault("reduced", []).append(os.path.basename(path))
                print(f"    reduced to {sum(len(lines) for _, lines in reduced)} lines in {reducer.tests} builds: {path}", flush=True)
    record["seconds"] = round(time.time() - began, 1)
    return record


def worker(args, index):
    """Runs every round that is this worker's and appends each record to its log."""
    project = Project(os.path.join(args.work, f"worker{index}"))
    seen = set()
    log = open(os.path.join(args.out, f"rounds{index}.jsonl"), "a")
    for number in range(args.first + index, args.first + args.rounds, args.jobs):
        record = round_of(project, f"{args.seed}-{number}", args.cases, args.backends, seen, args.reduce)
        log.write(json.dumps(record) + "\n")
        log.flush()
        state = "rejected by rustc" if "rejected" in record else ", ".join(
            f"{b} {e['compiled']} functions {len(e['findings'])} findings" for b, e in record["backends"].items())
        print(f"{record['seed']}: {state}", flush=True)


def report(directory, coverage_table=False):
    """Adds up the rounds logged in a directory and prints the counts. Returns the number of findings."""
    records = [json.loads(line) for name in sorted(os.listdir(directory)) if name.startswith("rounds")
               for line in open(os.path.join(directory, name))]
    built = [r for r in records if r["backends"]]
    print(f"programs: {len(records)} generated, {len(records) - len(built)} not accepted by rustc or not run")
    print(f"cases: {sum(r['cases'] for r in built)}; functions generated: {sum(r['generated_functions'] for r in built)}")
    total = 0
    for backend in BACKENDS:
        entries = [r["backends"][backend] for r in built if backend in r["backends"]]
        if not entries:
            continue
        kinds = collections.Counter((f["kind"], f["key"]) for e in entries for f in e["findings"])
        total += sum(kinds.values())
        by_kind = collections.Counter(f["kind"] for e in entries for f in e["findings"])
        print(f"{backend}: {len(entries)} programs, {sum(e['compiled'] for e in entries)} functions compiled by rustd, "
              f"{by_kind['differs']} differences, {by_kind['crash']} crashes, {by_kind['left']} left to rustc")
        for (kind, key), count in kinds.most_common():
            print(f"    {count:6} {kind}: {key}")
    if coverage_table:
        coverage = collections.Counter()
        for r in built:
            coverage.update(r["coverage"])
        for name, count in sorted(coverage.items()):
            print(f"    {name:32} {count}")
    return total


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=["smoke", "run", "repro", "check", "report"])
    ap.add_argument("targets", nargs="*")
    ap.add_argument("--seed", default="0")
    ap.add_argument("--first", type=int, default=0, help="the number of the first round")
    ap.add_argument("--rounds", type=int, default=10)
    ap.add_argument("--cases", type=int, default=30, help="cases in a program")
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--backends", default="cranelift,llvm")
    ap.add_argument("--reduce", type=int, default=900, help="seconds a reduction may take; 0 to only count")
    ap.add_argument("--out", help="where the logs of the rounds go")
    ap.add_argument("--work", help="where the programs are built")
    ap.add_argument("--coverage", action="store_true", help="print how often each construct was generated")
    args = ap.parse_args()
    args.backends = args.backends.split(",")
    args.work = args.work or tempfile.mkdtemp(prefix="rustd-fuzz-")
    if args.mode == "report":
        sys.exit(1 if report(args.targets[0], args.coverage) else 0)
    if args.mode == "check":
        sys.exit(check(args))
    if args.mode == "repro":
        seed, only = args.targets[0], args.targets[1:]
        record = round_of(Project(os.path.join(args.work, "repro")), seed, args.cases, args.backends, set(), args.reduce, only)
        print(json.dumps({k: v for k, v in record.items() if k != "coverage"}, indent=1))
        sys.exit(1 if any(e["findings"] for e in record["backends"].values()) or not record["backends"] else 0)
    if args.mode == "smoke":
        args.seed, args.rounds, args.cases, args.first = SMOKE["seed"], SMOKE["rounds"], SMOKE["cases"], 0
    args.out = args.out or tempfile.mkdtemp(prefix="rustd-fuzz-out-")
    os.makedirs(args.out, exist_ok=True)
    args.jobs = max(1, min(args.jobs, args.rounds))
    children = [subprocess.Popen([sys.executable, os.path.abspath(__file__), "worker", str(index), json.dumps(vars(args))])
                for index in range(args.jobs)] if args.jobs > 1 else []
    if not children:
        worker(args, 0)
    failed = [child.wait() for child in children]
    findings = report(args.out, args.coverage)
    print(f"logs: {args.out}")
    sys.exit(1 if findings or any(failed) else 0)


def check(args):
    """Each reduction given, or all of found/: whether rustd's build still differs from rustc's."""
    paths = args.targets or sorted(os.path.join(FOUND, name) for name in os.listdir(FOUND) if name.endswith(".rs"))
    paths = [path if os.path.exists(path) else os.path.join(FOUND, path) for path in paths]
    jobs = max(1, min(args.jobs, len(paths)))
    with multiprocessing.get_context("fork" if hasattr(os, "fork") else "spawn").Pool(jobs, check_start, (args,)) as pool:
        wrong = 0
        for lines, bad in pool.imap(check_one, paths):
            print("\n".join(lines), flush=True)
            wrong += bad
    return 1 if wrong else 0


def check_start(args):
    global checking
    checking = args, Project(os.path.join(args.work, f"check-{os.getpid()}"))


def check_one(path):
    """The lines `check` prints for one reduction, and how many of them differ."""
    args, project = checking
    name = os.path.basename(path)
    modules, edition = read_found(path)
    rejected = project.reference(modules, edition)
    if rejected is not None:
        return [f"REJECTED  {name}: {rejected[-300:]}"], 1
    lines, wrong = [], 0
    for backend in args.backends:
        findings, _ = project.rustd(backend)
        wrong += bool(findings)
        said = "; ".join(f"{f.kind}: {f.key}" for f in findings)
        lines.append(f"{'DIFFERENT' if findings else 'same     '} {name} ({backend}) {said}")
    return lines, wrong


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "worker":
        worker(argparse.Namespace(**json.loads(sys.argv[3])), int(sys.argv[2]))
    else:
        main()
