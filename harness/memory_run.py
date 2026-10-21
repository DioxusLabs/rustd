#!/usr/bin/env python3
"""Linux RSS guard: memory_run.py LABEL -- COMMAND [ARGS...].

Set RUSTD_HOME to a private daemon home and optionally RUSTD_REPORTS to the output
parent (~/bench/out by default). Keep RUSTD_MEMORY fixed across a cold/warm/edit
cycle: it is visible to tests and therefore part of their result cache key.
Reports are copied into each step's output without changing that environment.
"""
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

label, *command = sys.argv[1:] or ['']
if command and command[0] == '--':
    command.pop(0)
if not command or not re.fullmatch(r'[A-Za-z0-9_.-]+', label) or not os.environ.get('RUSTD_HOME'):
    raise SystemExit('usage: RUSTD_HOME=PRIVATE_HOME memory_run.py LABEL -- COMMAND [ARGS...]')
out = Path(os.environ.get('RUSTD_REPORTS', Path.home() / 'bench/out')) / label
out.mkdir(exist_ok=False)
env = os.environ.copy()
home = Path(env['RUSTD_HOME'])
env.setdefault('RUSTD_MEMORY', str(home / 'memory'))
env.update(CARGO_PROFILE_DEV_SPLIT_DEBUGINFO='unpacked',
           CARGO_PROFILE_TEST_SPLIT_DEBUGINFO='unpacked', RUSTD_STATS='1')
for key in ('OPENAI_API_KEY', 'AZURE_OPENAI_API_KEY'):
    env.pop(key, None)
start = time.monotonic()
positions = {}
peaks = {}
maximum = 0
aborted = False

def logs(events, initial=False):
    for path in home.rglob('log'):
        try:
            stat = path.stat()
            inode, offset = positions.get(str(path), (stat.st_ino, 0))
            if initial:
                positions[str(path)] = (stat.st_ino, stat.st_size)
                continue
            if inode != stat.st_ino or offset > stat.st_size:
                offset = 0
            with path.open('rb') as source:
                source.seek(offset)
                data = source.read()
            positions[str(path)] = (stat.st_ino, stat.st_size)
            if data:
                name = '__'.join(path.relative_to(home).parts)
                with (out / name).open('ab') as copied:
                    copied.write(data)
                events.write(json.dumps({'elapsed_s': time.monotonic() - start,
                                         'path': str(path), 'lines': data.decode(errors='replace')}) + '\n')
        except OSError:
            continue

def sample():
    rows = []
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit():
            continue
        try:
            args = proc.joinpath('cmdline').read_bytes().decode().split('\0')
            if Path(args[0]).name != 'rustd':
                continue
            status = proc.joinpath('status').read_text()
            fields = {key: int(value) for key, value in re.findall(r'^(VmRSS|RssAnon|RssFile|RssShmem|VmHWM|PPid|Threads):\s+(\d+)', status, re.M)}
            own = f"RUSTD_HOME={env['RUSTD_HOME']}\0".encode() in proc.joinpath('environ').read_bytes()
            row = dict(pid=int(proc.name), args=[arg for arg in args if arg], own=own, **fields)
            row['cwd'] = str(proc.joinpath('cwd').resolve())
            rows.append(row)
            pid = proc.name
            prior = peaks.setdefault(pid, dict(row))
            if fields.get('VmRSS', 0) >= prior.get('VmRSS', 0):
                peaks[pid] = row
        except (OSError, IndexError, UnicodeError):
            continue
    return rows

with (out / 'command.log').open('w') as output, (out / 'rss.jsonl').open('w') as rss, (out / 'events.jsonl').open('w') as events:
    logs(events, initial=True)
    child = subprocess.Popen(command, env=env, stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
    while True:
        rows = sample()
        total = sum(row.get('VmRSS', 0) for row in rows)
        maximum = max(maximum, total)
        elapsed = time.monotonic() - start
        available = next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
        rss.write(json.dumps(dict(elapsed_s=elapsed, sum_rss_kib=total, available_kib=available, processes=rows)) + '\n')
        rss.flush()
        logs(events)
        events.flush()
        if not aborted and (total >= 26 * 1024 * 1024 or available < 4 * 1024 * 1024 or elapsed > 1000):
            aborted = True
            output.flush()
            print(f'GUARD ABORT at {elapsed:.3f}s: {total / 1024:.1f} MiB total RSS, {available / 1024:.1f} MiB available', flush=True)
            for row in sorted(rows, key=lambda row: row.get('VmRSS', 0), reverse=True):
                if row['own']:
                    try:
                        os.kill(row['pid'], signal.SIGKILL)
                    except ProcessLookupError:
                        pass
        if child.poll() is not None:
            break
        time.sleep(0.25)
    logs(events)
summary = dict(command=command, wall_s=time.monotonic() - start,
               exit_code=child.returncode, guard_aborted=aborted,
               peak_sum_rss_kib=maximum, processes=peaks,
               memory_dir=env['RUSTD_MEMORY'])
(out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
reports = Path(env['RUSTD_MEMORY'])
if env['RUSTD_MEMORY'] and reports.is_dir():
    shutil.copytree(reports, out / 'ingredients')
print(json.dumps(summary, indent=2), flush=True)
raise SystemExit(2 if aborted else child.returncode)
