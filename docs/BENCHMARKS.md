# Current benchmark snapshot

Measured on 2026-08-13 in the standalone repository with 2,000 rows. Both
programs receive equivalent SQL and every result is compared; unordered join
output is normalized. Times are whole CLI wall-clock milliseconds, best used
as an order-of-magnitude snapshot rather than a cross-machine record.

```sh
ROWS=2000 scripts/run-workload-benchmark.sh
```

The checked-in regression floor is `scripts/performance-baseline.tsv`.
`scripts/run-benchmark-regression.sh` compares three-run medians against it;
`FAST=1 RUNS=1` selects six representative workloads for routine commits.

> **Two rows below are stale as of 2026-08-16.** Bulk `UPDATE` and bulk `DELETE`
> now measure 120 ms and 140 ms rather than 79 ms and 101 ms. The cause is
> identified and is a deliberate trade, not a performance bug: indexed mutations
> pay an O(index) decode-and-compare per commit
> (`CoreFileAdapter.certifyDecodedIndex?`) to admit a page-directed index write
> with an exact decoded post-state certificate, which is what replaced an opaque
> post-image premise. Ten deleted rows cost 38 ms of index work at 1,000 entries
> and 158 ms at 8,000. That attribution is real but incomplete: as of 2026-08-17
> the same per-commit growth is measured on a table with **no secondary index**, so
> index certification is one term and not the dominant one. See "Single-row write
> cost is linear in database size" below.
> Bulk load and secondary-index lookup are correspondingly
> *faster* than the floor. Measurements, the A/B that rules out the gap-closing
> work, and the lemma that would remove the cost are in
> [BENCHMARK_HISTORY.md](BENCHMARK_HISTORY.md#2026-08-16-two-workloads-no-longer-meet-the-frozen-floor-and-it-is-not-new).
> The YCSB numbers further down this file were re-measured on 2026-08-16 and are
> current.

| Workload | SQLeanite | C SQLite | Ratio |
|---|---:|---:|---:|
| Bulk load, one transaction | 296 ms | 62 ms | 4.8× |
| 100 autocommit inserts | 1,848 ms | 1,182 ms | 1.6× |
| Primary-key lookup | 10 ms | 7 ms | 1.4× |
| Secondary-index lookup | 19 ms | 7 ms | 2.7× |
| Range scan + predicate | 11 ms | 6 ms | 1.8× |
| `ORDER BY` + `LIMIT 20` | 29 ms | 7 ms | 4.1× |
| Bulk `UPDATE` | 79 ms | 21 ms | 3.8× |
| Bulk `DELETE` | 101 ms | 20 ms | 5.0× |
| Inner join | 11 ms | 8 ms | 1.4× |
| Read-modify-write transaction | 65 ms | 19 ms | 3.4× |
| Cold open + one read | 9 ms | 7 ms | 1.3× |
| Mixed read/write session | 103 ms | 30 ms | 3.4× |

The certified page-directed read shapes are close to C SQLite. Bulk mutation
now remains at or below roughly 5× as well: validated write-open reads pages
directly from the file buffer, and indexed deletion splits canonical cells in
one pass while retaining its exact decoded post-state certificate. Remaining
costs are concentrated in sorting/materialization and fixed Lean runtime/CLI
overhead. These measurements do not include the much broader test-only SQL
interpreter.

## YCSB-shaped scale and latency

The literal VeriBetrKV/YCSB schema
`usertable(ycsb_key TEXT PRIMARY KEY, field0 TEXT)`, one 512-byte field, and the
workload set VeriBetrKV actually runs. Re-measured 2026-08-17 with
`RECORDS=1000 OPS=100 RUNS=3 scripts/run-ycsb-benchmark.sh`; all six workloads
produced run-phase output identical to C SQLite, which is the harness's
precondition for reporting a timing at all.

**All six workloads, not just the read-only ones.** Load and run phases are
separate because VeriBetrKV's insertion claim is the load phase alone.

| Workload | Load ratio | Run ratio | SQLeanite p50 | SQLeanite p99 |
|---|---:|---:|---:|---:|
| A (50/50 read-update) | 5.6× | **9.3×** | 1.85 ms | 130.43 ms |
| B (95/5 read-update) | 5.6× | **12.9×** | 0.65 ms | 158.47 ms |
| C (read only, Zipfian) | 4.9× | 4.3× | 0.04 ms | 0.10 ms |
| D (read latest) | 5.7× | 4.0× | 0.65 ms | 46.04 ms |
| F (read-modify-write) | 5.6× | **10.1×** | 1.44 ms | 115.02 ms |
| Cuniform (read only, uniform) | 5.5× | 4.0× | 0.04 ms | 0.10 ms |

The write-heavy workloads A, B and F run **9.3× to 12.9× C SQLite and are the
weakest numbers in this project.** Read-only C and Cuniform are 4.0–4.3× at
0.04 ms p50. Run-to-run spread on the tails is wide: an independent run of the
same harness reported 9.7×/13.6×/10.0× for A/B/F and 17.96 ms rather than
46.04 ms for D's p99, so treat the tail figures as order-of-magnitude.
[RESULTS.md](RESULTS.md) carries that second run.

**The A/B/F cost is the median update, not a tail event.** Decomposing workload A
per statement at 1,000 records gives a **SELECT median of 1.26 ms and an UPDATE
median of 111.77 ms**. Workload A is 51 reads and 49 updates, so its 1.85 ms p50
describes the read population only, and its p99 is close to the *typical* update
rather than an outlier. Roughly half of every operation in A and F costs about
112 ms. Reporting the mixed p50 alone would misdescribe this.

That per-update cost is not constant in database size: see
"Single-row write cost is linear in database size" below.

Two figures previously stated here were wrong and are withdrawn. Durable
single-row inserts are **not** flat at 18.324 ms / 19.997 ms across 1.27 MB and
10.03 MB. Measured 2026-08-17 with open and decode excluded, on the YCSB schema
at 4,000 records (615 pages, 2.5 MB), a single-row `INSERT` costs 59 ms and a
single-row `UPDATE` by primary key costs 452 ms. On the
`t(id INTEGER PRIMARY KEY, payload)` schema at 275 pages an appending `INSERT`
costs 373 ms, statistically the same as the 369 ms `UPDATE`. So inserts are
cheaper than updates on one schema and not on the other, and no flat-insert claim
is currently supportable. The asymmetry is measured but not diagnosed.

## Single-row write cost is linear in database size

`scripts/run-localized-update-scaling.sh` updates one row by INTEGER PRIMARY KEY
with open, decode and proof-state reconstruction outside the timed region, so it
measures the commit alone. Measured 2026-08-17, best of three per point:

| Rows | Pages | Commit | Per page |
|---:|---:|---:|---:|
| 250 | 4 | 15 ms | 3.75 ms |
| 500 | 5 | 16 ms | 3.20 ms |
| 1,000 | 7 | 17 ms | 2.43 ms |
| 2,000 | 12 | 24 ms | 2.00 ms |
| 4,000 | 22 | 34 ms | 1.55 ms |
| 20,000 | 111 | 146 ms | 1.32 ms |
| 50,000 | 275 | 368 ms | 1.34 ms |

The commit is **linear in total database pages**, about `10 ms + 1.3 ms/page`,
converging to a stable per-page cost. It is not constant time, and the earlier
claim that it was is corrected in
[BENCHMARK_HISTORY.md](BENCHMARK_HISTORY.md#localized-point-update-scaling)
together with the measurement that made it look flat.

The cost is independent of *where* the change lands, which is the part that rules
out a locality explanation. At 50,000 rows and 275 pages: mid-table `UPDATE`
369 ms, tail `UPDATE` 372 ms, first-row `UPDATE` 372 ms, appending `INSERT`
373 ms, single-row `DELETE` 670 ms. It is also not specific to index
maintenance: a table with **no secondary index** shows the same growth, 17 / 28 /
103 / 261 ms at 1,000 / 4,000 / 20,000 / 50,000 rows.

C SQLite on the same YCSB workload is flat over the same range — 11.5 / 12.0 /
11.5 ms at 250 / 1,000 / 4,000 records — so the YCSB ratios above are specific to
1,000 records and degrade as the database grows. At 4,000 records the per-update
comparison is roughly 415 ms against 11.5 ms.

The exact one-million-row, 512-byte-field load completes in 220.76 seconds and
emits 625,565,696 bytes versus C SQLite's 622,739,456 bytes (1.0045×). C
SQLite reports `integrity_check=ok`, one million rows, and 512-byte minimum and
maximum payloads. Peak RSS was 44.2 GiB, so memory consumption remains an
important engineering limitation even though the former stack and file-size
ceilings are closed.

The historical curves and the representation changes that moved these numbers
are retained in [BENCHMARK_HISTORY.md](BENCHMARK_HISTORY.md).
