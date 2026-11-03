"""Summarize overlapping worker phases without summing concurrent programs."""
import re
import statistics


def distribution(values):
    return dict(median=statistics.median(values), min=min(values), max=max(values))


def timelines(log):
    rows = []
    for line in log.splitlines():
        if not line.startswith("timeline-us: "):
            continue
        phases = {name: int(value) / 1_000_000
                  for name, value in re.findall(r"([\w-]+)=(\d+)", line)}
        program = re.search(r"; program=(.*)$", line)
        rows.append((program[1] if program else None, phases))
    return rows


def summarize(edits):
    assert len(edits) == 5, len(edits)
    assert all(edit["exit_code"] == 0 for edit in edits)
    rows = [timelines(edit["log"]) for edit in edits]
    assert all(row for row in rows), "missing worker timelines"
    assert len({len(row) for row in rows}) == 1, "program count changed"
    phases = set.intersection(*(set(p) for row in rows for _, p in row))
    result = dict(edits=5, wall_seconds=distribution([e["wall_seconds"] for e in edits]),
                  longest_program_phase_seconds={
                      phase: distribution([max(p[phase] for _, p in row) for row in rows])
                      for phase in sorted(phases)})
    programs = [{name for name, _ in row} for row in rows]
    if None not in programs[0] and all(names == programs[0] for names in programs):
        assert all(len(names) == len(row) for names, row in zip(programs, rows))
        result["program_phase_seconds"] = {
            name: {phase: distribution([dict(row)[name][phase] for row in rows])
                   for phase in sorted(phases)} for name in sorted(programs[0])}
    else:
        result["program_phase_seconds"] = None
    return result
