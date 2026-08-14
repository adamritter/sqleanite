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
| Bulk load, one transaction | 303 ms | 58 ms | 5.2× |
| 100 autocommit inserts | 1,902 ms | 1,210 ms | 1.6× |
| Primary-key lookup | 9 ms | 8 ms | 1.1× |
| Secondary-index lookup | 19 ms | 7 ms | 2.7× |
| Range scan + predicate | 13 ms | 7 ms | 1.9× |
| `ORDER BY` + `LIMIT 20` | 30 ms | 8 ms | 3.8× |
| Bulk `UPDATE` | 101 ms | 21 ms | 4.8× |
| Bulk `DELETE` | 144 ms | 21 ms | 6.9× |
| Inner join | 11 ms | 8 ms | 1.4× |
| Read-modify-write transaction | 91 ms | 20 ms | 4.5× |
| Cold open + one read | 9 ms | 8 ms | 1.1× |
| Mixed read/write session | 132 ms | 31 ms | 4.3× |

The certified page-directed read shapes are close to C SQLite. Remaining costs
are concentrated in bulk mutation, sorting/materialization, and fixed Lean
runtime/CLI overhead. These measurements do not include the much broader
test-only SQL interpreter.

The historical curves and the representation changes that moved these numbers
are retained in [BENCHMARK_HISTORY.md](BENCHMARK_HISTORY.md).

