# Workload benchmark corpus

One SQL file per workload, run by `scripts/run-workload-benchmark.sh` against both
SQLeanite and C SQLite. Kept here rather than generated inside the script so
each workload is reviewable and version-controlled, the same way
`tests/sql/core_differential` holds the differential corpus.

Every file must stay inside the subset both engines implement: INTEGER / TEXT /
NULL, single-column indexes, no aggregates, no subqueries. `count(*)` in
particular is not available, so row counts are checked by selecting ids.

Files ending in `.sql.in` are templates. The runner replaces their named
threshold placeholders from `ROWS`; supported runs require `ROWS >= 2000`.

Outputs are compared between engines on every run. A workload whose rows come
back in a different order is reported as `same (unordered)` rather than a
mismatch, because SQL fixes no row order without `ORDER BY`.
