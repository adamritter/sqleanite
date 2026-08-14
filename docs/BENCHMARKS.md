# Current benchmark snapshot

Measured on 2026-08-13 in the standalone repository with 2,000 rows. Both
programs receive equivalent SQL and every result is compared; unordered join
output is normalized. Times are whole CLI wall-clock milliseconds, best used
as an order-of-magnitude snapshot rather than a cross-machine record.

```sh
ROWS=2000 scripts/run-workload-benchmark.sh
```

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

The historical curves and the representation changes that moved these numbers
are retained in [BENCHMARK_HISTORY.md](BENCHMARK_HISTORY.md).
