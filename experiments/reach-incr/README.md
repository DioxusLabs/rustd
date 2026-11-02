# Incremental reach benchmark

Run with Rust 1.99.0 from this directory:

```sh
cargo run --release -- --variant salsa --scale small
cargo run --release -- --variant salsa-tiers --scale mid
cargo run --release -- --variant push --signal edit --scale mid
cargo run --release -- --variant reactive --signal edit --scale small
cargo test
```

`--help` lists the size overrides. Presets contain 5,000 / 30,000 / 120,000
functions, 20 / 60 / 100 crates and 50 / 200 / 731 roots respectively. Roots
are spread through the hottest crate (or `--hot-crates` crates). Seeded call
graphs have same-crate clusters with back edges, edges to earlier clusters,
and dependencies on lower crates. Signature dependencies are seeded separately.

Each edit kind starts with a fresh database and the same source model. Twenty
edits repeatedly change one reachable function in one hot file. Edge edits
alternate adding and removing a callee. The tiers variant starts files at
MEDIUM and resets the edited file at LOW; its first edit therefore invalidates
MEDIUM, while subsequent edits invalidate LOW. Metadata stays HIGH.

`edge` adds/removes an edge to the first available node. `edge-cycle` chooses
an ancestor outside the edited node's SCC, so every insertion creates a cycle
and every removal breaks it. With twenty edits this gives ten merges and ten
splits; five edits give three merges and two splits. Selection is outside timing.
`--edit edge` or `--edit edge-cycle` runs just that kind; the default is all four.

The table reports cold query time, warm median and nearest-rank p90, first-edit
time, subsequent-edit median, total event counts across all edits, and RSS
immediately after the cold query. Query timing includes event-counter overhead
but excludes input mutation, reporting, and correctness checking. Per-edit
times and per-ingredient execution/validation counts are on stderr, with
first-edit and subsequent-edit count summaries. RSS is process-wide; allocator
retention can affect subsequent rows.

After the cold build and every edit, all root prints must match an independent
plain-Rust traversal over freshly computed code hashes. This traversal does not
use Salsa, SCCs, interned components, or incremental caches. A mismatch panics.

## Native push reach

`push` uses the MEDIUM-to-LOW semantic layer; `push-low` uses all LOW inputs.
Neither uses any Salsa reach query. The native graph caches codegen results,
forward/reverse node edges, SCC membership, forward/reverse condensation edges,
component prints, root prints and per-component root-reachability bitsets. Own
print deltas update the roots in those bitsets. Edge changes pull new nodes and
update the condensation locally. Additions search forward from the target;
cycles merge the intersection with the source's reverse closure. Internal edge
removals run Tarjan only on that SCC and split it when necessary. Incident
condensation edges are deduplicated from member edges, so parallel supporting
node edges are preserved correctly. Retired component slots are reused.

Root bitsets are recomputed from reverse condensation edges with a change-driven
worklist, updating root prints only when membership changes. This avoids a full
per-root graph traversal. Searches are not topological-order bounded; a large
affected closure or SCC can still require linear work. Cold construction still
uses full Tarjan. `--topology full` retains a full-rebuild comparison path;
`--topology incremental` is the default.

`--signal all` verifies every cached graph node via an individual codegen query.
`--signal edit` checks the edited files' item trees, verifies only those files'
functions when signatures are unchanged, and falls back to all cached nodes if
any item tree changes. Each signature fallback is reported on stderr and counted
in the table. Files have a fixed function inventory in this model.

Per-edit stderr output splits total time into time inside Salsa calls and the
remaining native work, including the separately timed topology update. The
summary reports the medians of these times, total codegen calls across edits,
fallback/topology edit counts, merge/split counts, internal-removal split checks,
and estimated persistent native-layer bytes after
the final edit. Bytes include vector backing capacities, nested vector headers,
reverse edges and cached item trees; they exclude allocator metadata, temporary
worklists and Salsa's own storage. Baseline variants report zero native bytes
and zero explicit per-node calls (they invoke the program-wide Salsa query).

## Reactive reach

`reactive` uses standalone `reactive_graph` 0.2.16 with the tiers semantic layer
and the same change signal and native SCC updates as push. `ArcRwSignal` and
`ArcMemo` are reference-counted; root pulls use synchronous `get_untracked`, with
no external Owner, executor, effects, or Leptos. Native root-print propagation
is disabled for this variant. Only changed codegen own prints set signals.

There is one signal per function, one Memo per active condensation component,
and one Memo per root. Component Memos read members' signals and successor Memos.
Their values contain persistent `im::HashMap` contribution maps plus a sum, so
shared descendants in diamonds are counted exactly once. This representation
has additional time and memory costs beyond the reactive library itself.
Every topology change discards and rebuilds all Memos, retaining input signals.
The topology column includes native updates and Memo rebuilding/root pulls.

Closures count component and root Memo executions with relaxed atomic counters.
Per-edit counts and cold node counts are printed on stderr; their medians are
in the table. The library does not expose aggregate validation-only counts.
RSS is sampled after native cold construction and again after reactive cold
construction/root pulling; their difference estimates the reactive allocation
delta. Peak sampled RSS includes the whole process and retained allocator memory.
Use one `--edit` kind per process for meaningful RSS comparisons. `native bytes`
excludes reactive storage, which is represented by the RSS columns instead.
Cold timing and correctness are logged before warm edits. Reactive runs stop
with exit 2 after a matching cold result if cold exceeds 60 seconds or process
RSS exceeds 1 GiB, rather than attempting warm edits beyond that resource budget.
