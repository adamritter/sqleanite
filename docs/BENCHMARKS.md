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

The final 2026-08-16 measurements use the literal VeriBetrKV/YCSB schema
`usertable(ycsb_key TEXT PRIMARY KEY, field0 TEXT)`. At 1,000 records, three-run
read medians are 4.0× C SQLite for workload C and 3.2× for Cuniform, with
0.04 ms p50 and 0.10 ms p99 SQLeanite operation latency. At 2,000 records,
workload D reports 0.88 ms p50 and 17.52 ms p99; durable single-row inserts are
flat at 18.324 ms in a 1.27 MB database and 19.997 ms in a 10.03 MB database.

The exact one-million-row, 512-byte-field load completes in 220.76 seconds and
emits 625,565,696 bytes versus C SQLite's 622,739,456 bytes (1.0045×). C
SQLite reports `integrity_check=ok`, one million rows, and 512-byte minimum and
maximum payloads. Peak RSS was 44.2 GiB, so memory consumption remains an
important engineering limitation even though the former stack and file-size
ceilings are closed.

The historical curves and the representation changes that moved these numbers
are retained in [BENCHMARK_HISTORY.md](BENCHMARK_HISTORY.md).
