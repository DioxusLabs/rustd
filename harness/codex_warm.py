"""Prime Codex, then measure five alternating features.rs edits (on|off).

RUSTD_BENCH_WORKSPACE, RUSTD_BENCH_REPORTS, RUSTD_BENCH_RUN, RUSTD_BENCH_BIN
and RUSTD_BENCH_STORE override the local workspace, output and cache locations.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import threading
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from warmstats import summarize

repo = Path(__file__).resolve().parent.parent
workspace = Path(os.environ.get('RUSTD_BENCH_WORKSPACE', str(Path.home() / 'codex/codex-rs')))
reports = Path(os.environ.get('RUSTD_BENCH_REPORTS', str(Path.home() / 'bench/profile7')))
mode = sys.argv[1]
assert mode in ('on', 'off', 'local', 'cli')
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo).strip()
diff = subprocess.check_output(['git', 'diff'], cwd=repo)
root = reports / os.environ.get('RUSTD_BENCH_RUN', 'sharing-perf-' + mode)
root.mkdir()
(root / 'measured.patch').write_bytes(diff)
home, store = root / 'daemon', root / 'store'
store = Path(os.environ.get('RUSTD_BENCH_STORE', str(store)))
binary = Path(os.environ.get('RUSTD_BENCH_BIN', str(repo / 'target/release/rustd')))
env = dict(os.environ, PATH=str(binary.parent) + os.pathsep + os.environ['PATH'],
           RUSTUP_TOOLCHAIN='1.99.0', RUSTD_HOME=str(home), RUSTD_CACHE=str(store),
           RUSTD_STATS='1', RUSTD_CFG_SHARING='local' if mode == 'local' else ('0' if mode == 'off' else '1'),
           CARGO_PROFILE_DEV_SPLIT_DEBUGINFO='unpacked',
           CARGO_PROFILE_TEST_SPLIT_DEBUGINFO='unpacked', TMPDIR='/home/ubuntu/b')
for key in list(env):
    if key.endswith('API_KEY') or key in ('_RJEM_MALLOC_CONF', 'RUSTD_MEMORY',
                                        'RUSTD_CFG_TWINS', 'RUSTD_CFG_ANALYSIS_TRACE'):
        env.pop(key)
command = (['cargo', 'rustd', 'build', '--bin', 'codex'] if mode == 'cli' else
           ['cargo', 'rustd', 'test', '-p', 'codex-core', '--no-run'])
(root / 'command.json').write_text(json.dumps(dict(command=command,
    commit=head.decode(), mode=mode, split_debuginfo='unpacked', tmpdir=env['TMPDIR']), indent=2))
offsets = {}
edits = []

def run(label):
    perf = None
    if label.startswith('edit') and os.environ.get('RUSTD_BENCH_PERF') == '1':
        pids = []
        for proc in Path('/proc').iterdir():
            if not proc.name.isdigit():
                continue
            try:
                args = (proc / 'cmdline').read_bytes().split(b'\0')
            except OSError:
                continue
            if any(str(home).encode() in arg for arg in args) and (b'--socket' in args or b'--spare' in args):
                pids.append(proc.name)
        assert pids
        perf_log = (root / (label + '.perf.log')).open('w')
        perf = subprocess.Popen(['sudo', '-n', 'perf', 'record', '-F', '199',
            '--call-graph', 'dwarf,8192', '-p', ','.join(pids),
            '-o', str(root / (label + '.perf.data'))], stdout=perf_log, stderr=subprocess.STDOUT)
    start = time.monotonic()
    peak, total_peak = 0, 0
    with (root / (label + '.command.log')).open('w') as log, \
         (root / (label + '.samples.jsonl')).open('w') as samples:
        child = subprocess.Popen(command, cwd=workspace, env=env, stdout=log, stderr=subprocess.STDOUT)
        done = threading.Event()
        finished = []
        def wait_child():
            child.wait()
            finished.append(time.monotonic())
            done.set()
        waiter = threading.Thread(target=wait_child)
        waiter.start()
        while True:
            workers = []
            for proc in Path('/proc').iterdir():
                if not proc.name.isdigit():
                    continue
                try:
                    args = (proc / 'cmdline').read_bytes().split(b'\0')
                    if not any(str(home).encode() in arg for arg in args):
                        continue
                    if not (b'--socket' in args or b'--spare' in args):
                        continue
                    status = dict(line.split(':', 1) for line in
                                  (proc / 'status').read_text().splitlines() if ':' in line)
                    workers.append(dict(pid=proc.name, rss_kib=int(status['VmRSS'].split()[0])))
                except (OSError, KeyError, ValueError):
                    continue
            peak = max(peak, max((w['rss_kib'] for w in workers), default=0))
            total_peak = max(total_peak, sum(w['rss_kib'] for w in workers))
            samples.write(json.dumps(dict(seconds=time.monotonic() - start, workers=workers)) + '\n')
            samples.flush()
            if done.wait(1):
                break
        waiter.join()
    result = dict(wall_seconds=finished[0] - start, exit_code=child.returncode,
                  worker_peak_rss_kib=peak, total_peak_rss_kib=total_peak)
    (root / (label + '.summary.json')).write_text(json.dumps(result, indent=2))
    logs = []
    for path in sorted(home.rglob('log')):
        data = path.read_text(errors='replace')
        logs.append(f'\n=== {path} ===\n' + data[offsets.get(str(path), 0):])
        offsets[str(path)] = len(data)
    worker_log = ''.join(logs)
    (root / (label + '.worker.log')).write_text(worker_log)
    if label.startswith('edit'):
        edits.append(dict(result, log=worker_log))
    print(mode, label, json.dumps(result), flush=True)
    if perf:
        pending, targets = [perf.pid], []
        while pending:
            pid = pending.pop()
            proc = Path('/proc') / str(pid)
            try:
                if (proc / 'comm').read_text().strip() == 'perf':
                    targets.append(str(pid))
                else:
                    pending.extend(map(int, (proc / 'task' / str(pid) / 'children').read_text().split()))
            except FileNotFoundError:
                pass
        if targets:
            subprocess.run(['sudo', '-n', 'kill', '-TERM', *targets], check=True)
        perf.wait(timeout=120)
        perf_log.close()
    assert child.returncode == 0, (mode, label, child.returncode)

source = workspace / 'core/src/features.rs'
original = source.read_bytes()
old, new = b'        self.enabled.contains(&f)', b'        !self.enabled.contains(&f)'
assert original.count(old) == 1
(root / 'features.rs.before').write_bytes(original)
try:
    run('prime')
    if mode != 'cli' and os.environ.get('RUSTD_BENCH_SAVE_TEST_BINARIES') == '1':
        programs = [p for state in home.glob('states/*.json') if '.kept.' not in state.name
                    for p in json.loads(state.read_text()).get('programs', [])]
        for name in ('codex_core',):
            matches = [p for p in programs if p['name'] == name and p['test']]
            assert len(matches) == 1, (name, matches)
            target = root / (name + '.bin')
            shutil.copy2(matches[0]['executable'], target)
            (root / (name + '.origin.json')).write_text(json.dumps(matches[0], indent=2))
    for repeat in range(5):
        source.write_bytes(original.replace(old, new) if repeat % 2 == 0 else original)
        run('edit' if repeat == 0 else 'edit-' + str(repeat + 1))
    summary = summarize(edits)
    (root / 'five-edits.summary.json').write_text(json.dumps(summary, indent=2))
    print(mode, 'five-edits', json.dumps(summary), flush=True)
    if os.environ.get('RUSTD_BENCH_REFERENCE_EDIT') == '1':
        source.write_bytes(original)
        run('restore-before-reference')
        replacement = b'        self.enabled.contains(&f) && !f.key().is_empty()'
        source.write_bytes(original.replace(old, replacement))
        (root / 'reference-edit.patch').write_text(
            '- ' + old.decode() + '\n+ ' + replacement.decode() + '\n')
        run('reference-edit')
finally:
    source.write_bytes(original)
    assert source.read_bytes() == original
    print('features.rs restored byte-identically:', hashlib.sha256(original).hexdigest(), flush=True)
    with (root / 'stop.log').open('w') as log:
        subprocess.run([str(binary), 'stop'], cwd=workspace, env=env, stdout=log, stderr=subprocess.STDOUT)
