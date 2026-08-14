# SQLeanite vs C SQLite: measured timings

Same machine, same SQL, same on-disk format. C SQLite is `/usr/bin/sqlite3`;
SQLeanite is `--verified-file`. Times are wall clock for the whole process,
which is the honest unit here because both are invoked as a CLI.

Rows are `(INTEGER PRIMARY KEY, TEXT)` with ~15-byte payloads.

## Summary

| Workload | Rows | SQLeanite | C SQLite | Ratio |
|---|---:|---:|---:|---:|
| Bulk insert, one transaction | 1,000 | 215 ms | 30 ms | **7×** |
| Bulk insert, one transaction | 10,000 | 2,783 ms | 48 ms | **58×** |
| 100 single-row autocommit inserts | 100 | 2,700 ms | 1,136 ms | **2.3×** |
| Open + 1 point query | 1,000 | 51 ms | 5 ms | **10×** |
| Open + 1 point query | 10,000 | 573 ms | 5 ms | **115×** |
| Open + 100 point queries | 10,000 | 616 ms | 6 ms | **103×** |
| Range query (`id > 9990`) | 10,000 | 570 ms | 4 ms | **142×** |
| `ORDER BY id LIMIT 50` | 10,000 | **582 ms** | 4 ms | **146×** |
| Empty database, 1 query | 0 | 40 ms | 4 ms | **10×** |

## What the numbers actually say

**The floor is ~10×, and it is process startup.** On an empty database the gap
is 40 ms vs 4 ms. That is Lean binary startup, not database work.

**Opening is O(database size).** 40 ms empty, 51 ms at 1k rows, 573 ms at 10k.
SQLeanite decodes and validates the *entire file* on open; C SQLite opens
lazily and touches only the pages a query needs. This single design choice
explains most of the read-side gap.

**Queries are nearly free once open.** 100 point queries cost 616 ms against
578 ms for one — about 0.4 ms per additional query. The 115× point-query ratio
is almost entirely the one-time decode, not per-query work. A long-lived
connection would look far better than these CLI numbers.

**`ORDER BY` was quadratic; it is now free.** Sorting 10,000 rows used to cost
~3.1 s on top of the 570 ms open. All three query paths now use a stable
`List.mergeSort` over the same order, and sorting is no longer measurable:
582 ms with `ORDER BY` against 578 ms without. **6.2× on that workload.**

**Writes are the closest race.** 100 autocommit inserts is only 2.3× — the one
workload where C SQLite is also doing expensive work (an fsync per commit).
SQLeanite is slow here for a different reason: it rewrites the whole file per
statement. Batching into one transaction turns 252 s into 0.33 s for 2,000 rows
(see `TCB.md`), so the advice is the same as for real SQLite, just louder.

## Where the gap comes from, ranked

1. **Whole-file decode on open** — linear in database size, vs lazy paging.
2. **Quadratic `ORDER BY`** — insertion sort.
3. **Whole-file rewrite per autocommit statement** — mitigated by transactions.
4. **Rebuild-on-insert in the paged tree** — `Tree.insert` re-paginates
   everything; invisible below a few thousand rows, dominant by 30,000.
5. **Process startup** — ~36 ms of fixed overhead.

None of these are consequences of verification. They are consequences of
choosing the simplest correct implementation at each step: full decode rather
than lazy paging, insertion sort rather than merge sort, rebuild rather than
in-place mutation. Each has a standard fix that does not weaken any theorem,
because every proof is stated against an abstraction function (`toList`) rather
than against a representation.

## Honest caveats

- CLI process timing flatters neither system, but it penalises SQLeanite less
  than a server benchmark would, since C SQLite's startup is also included.
- SQLeanite supports INTEGER/TEXT/NULL only, single-column indexes, and no
  aggregates; these workloads were chosen to be expressible in both.
- SELECT now uses indexes via `Table.plannedRows`, proved semantics-preserving,
  but `indexedCandidates` filters the in-memory row list rather than descending
  the persisted index B-tree, so it does not change asymptotic complexity. The
  reads above are still linear in table size.
- Numbers are single runs on a loaded developer machine; treat them as orders
  of magnitude, not benchmarks of record.

## Scaling curves

Regenerate with `scripts/run-scaling.sh`.

| Rows | Bulk insert (1 txn) | Open + point query | Open + `ORDER BY` | Pages |
|---:|---:|---:|---:|---:|
| 250 | 154 ms / 31 ms | 44 ms / 7 ms | 43 ms / 7 ms | 4 |
| 1,000 | 187 ms / 32 ms | 53 ms / 7 ms | 52 ms / 7 ms | 8 |
| 5,000 | 835 ms / 41 ms | 194 ms / 6 ms | 185 ms / 7 ms | 32 |
| 20,000 | 10,874 ms / 70 ms | 2,352 ms / 8 ms | 2,311 ms / 8 ms | 123 |

(SQLeanite / C SQLite.)

Two things the curve shows. **`ORDER BY` now tracks the point query at every
size** — 43 vs 44 ms at 250 rows, 2,311 vs 2,352 ms at 20,000 — so the sort has
stopped being a cost centre. And **open time grows faster than linearly** (44 →
2,352 ms for an 80× row increase), because opening decodes and validates the
whole file. That is now the dominant read cost and the clear next target: lazy
paging would flatten this curve.

Capacity ceiling is unchanged: 60,000 rows over 313 pages verified, ~100,000
refused cleanly at the two-level interior fanout limit.

### Localized point-update scaling

`scripts/run-localized-update-scaling.sh` opens before starting its timer, updates
one middle row by INTEGER PRIMARY KEY, and reports the best of three real page
mutations. `CHECK_FLAT=1` enables a deliberately generous regression envelope.

| Rows | Commit | Database pages |
|---:|---:|---:|
| 250 | 18 ms | 27 |
| 500 | 19 ms | 58 |
| 1,000 | 22 ms | 120 |
| 2,000 | 25 ms | 244 |
| 4,000 | 30 ms | 493 |

This was 63 / 90 / 160 / 332 / 610 ms before persistent page deltas.  A later
logical-tree migration briefly regressed the curve to 38 / 81 / 243 ms at
250 / 1,000 / 4,000 rows because `patchRows` rebuilt the new primary tree.
Primary-key equality UPDATE now uses proved routed lookup plus local upsert, so
the acceptance curve is flat again.

An independent CLI decomposition measured read-only open at 19 / 31 / 56 /
106 / 211 ms and open-plus-update at 39 / 50 / 77 / 126 / 235 ms. Their
difference is 20 / 19 / 21 / 20 / 24 ms, corroborating the direct timer. It
also isolates the successor bottleneck: fresh open is linear and accounts for
90% of the 4,000-row CLI update invocation.

### Cold primary-key scaling

`scripts/run-cold-primary-scaling.sh` starts a fresh process for each query and
times both a successful primary-key lookup and a missing key in a stamped
Lean-generated image. `CHECK_FLAT=1` rejects the former full-decode slope.

| Rows | Hit | Miss | Database pages |
|---:|---:|---:|---:|
| 250 | 9 ms | 9 ms | 27 |
| 500 | 9 ms | 8 ms | 58 |
| 1,000 | 9 ms | 9 ms | 120 |
| 2,000 | 8 ms | 9 ms | 244 |
| 4,000 | 8 ms | 9 ms | 493 |

Both paths acquire the catalog and one root-to-leaf path. General, malformed,
or C-modified files retain the validating full-open fallback.

### Cold generated-index scaling

`scripts/run-cold-index-scaling.sh` performs the analogous fresh-process test for
a generated INTEGER secondary index. The exact catalog marker and generated
header stamp admit the proved directed traversal; every matching rowid is then
resolved through a primary-tree path. Positional reads are essential because
index roots follow the table pages physically.

| Rows | Hit | Miss | Database pages |
|---:|---:|---:|---:|
| 250 | 10 ms | 9 ms | 30 |
| 500 | 11 ms | 9 ms | 62 |
| 1,000 | 11 ms | 8 ms | 129 |
| 2,000 | 11 ms | 9 ms | 262 |
| 4,000 | 11 ms | 10 ms | 527 |

The curve is flat across 16x more rows. Before switching the routed source
from cursor-skipping reads to `pread`, the same proof-local lookup measured
12 / 14 / 19 / 29 / 49 ms for hits because reaching the late index root still
read every preceding page.

## Maintenance cost

Regenerate with `scripts/run-proof-latency.sh`. The deployed-systems survey lists
this as a first-class metric.

| Scenario | Elapsed |
|---|---:|
| No-op rebuild | 147 ms |
| Edit `CellPagination.lean`, rebuild | 17.2 s |
| Edit `CoreEngine.lean`, rebuild | 17.0 s |
| Edit `GrowableStorage.lean`, rebuild | 24.8 s |
| Full rebuild from clean | 147 s |

A typical single-module change costs under 25 seconds to re-verify, which is
the number that matters for whether proofs survive ongoing development.

## Reproducing everything

`scripts/reproduce-all.sh` runs build, tests, the verification audit, the live-path
check, the manifest, both differential arms, both mutation arms, crash
injection, and the scaling curves. `QUICK=1` skips the slow sweeps.

## Twelve realistic workloads

`ROWS=2000 scripts/run-workload-benchmark.sh`. The workload SQL lives in
`tests/sql/workloads/`, one reviewable file per case, alongside the differential
corpus. Every workload stays inside what
both engines can run (the Core subset has no aggregates, subqueries or
multi-column indexes). **Outputs are compared on every case** — a timing means
nothing if the two engines did different work.

| # | Workload | SQLeanite | C SQLite | Ratio | Outputs |
|---|---|---:|---:|---:|---|
| 1 | Bulk load, 2,000 rows, one txn | 804 ms | 58 ms | 13.9× | same |
| 2 | Autocommit inserts (100) | 2,645 ms | 1,154 ms | **2.3×** | same |
| 3 | Point lookup by primary key | 98 ms | 7 ms | 14.0× | same |
| 4 | Indexed lookup (secondary index) | 99 ms | 8 ms | 12.4× | same |
| 5 | Range scan + predicate | 97 ms | 7 ms | 13.9× | same |
| 6 | `ORDER BY` + `LIMIT 20` | 97 ms | 8 ms | 12.1× | same |
| 7 | Bulk `UPDATE` by predicate | 504 ms | 20 ms | 25.2× | same |
| 8 | Bulk `DELETE` by predicate | 350 ms | 20 ms | — | **unsupported** |
| 9 | Inner join, two tables | 107 ms | 8 ms | 13.4× | same (row order differs) |
| 10 | Read-modify-write transaction | 503 ms | 19 ms | 26.5× | same |
| 11 | Cold open + one read | 98 ms | 8 ms | 12.2× | same |
| 12 | Mixed read/write session | 900 ms | 31 ms | 29.0× | same |

### Reading these numbers

**The honest headline is 12–15× on reads and 25–30× on writes**, not the larger
figures in the older table above — those were measured before the merge-sort fix
and at a larger scale where the open cost dominates.

**Reads cluster at ~97 ms regardless of what they do.** Point lookup, indexed
lookup, range scan, sort-and-limit and cold-open-plus-one-read are all within
3 ms of each other. That is the whole-file decode on open; the query itself is
noise. Lazy paging is the single change that would move every read row.

**Writes are 25–30× because each statement rewrites the whole database.**
Workload 10 does one small `UPDATE` and costs 503 ms.

**Workload 2 is the closest race at 2.3×**, and it is the one where C SQLite is
also doing real work: an `fsync` per autocommit. It is the only row where
SQLeanite is within an order of magnitude, which tells you the gap is
implementation overhead, not durability work.

**Workload 9's row order differs.** SQL does not fix order without `ORDER BY`;
contents are identical, and the harness reports ordering separately from a real
mismatch rather than conflating them.

### Workload 8 found a real gap

`DELETE` of 300 rows from a 2,000-row table fails on the Core path:

```
uncaught exception: general MVP physical shrink awaits freelist encoding
```

Removing enough rows shrinks the file below its current page count, and freelist
encoding is not wired into the general multi-page path — it exists only for the
retired fixed-schema codec. Small deletes that do not free a page work fine,
which is why the earlier single-page differential cases never caught this.

This is a **capability gap, not a wrong answer**, and it was found only because
the harness compares outputs instead of just timing. It is the most concrete
missing piece on the storage side after physical index traversal.
