# Upstream-adapted SQL corpus

Scenarios adapted from named upstream SQLite Tcl test files into plain SQL that
stays inside the subset the verified core implements. Run with:

```sh
scripts/run-upstream-adapted.sh
```

C SQLite is the oracle: no expected values are hard-coded, both engines run the
same file against their own database, and the outputs must match byte for byte.

| File | Adapted from | Covers |
|---|---|---|
| `01_select1.sql` | `test/select1.test` | basic SELECT forms and column order |
| `02_insert.sql` | `test/insert.test` | named columns, reordered columns, NULL, multi-row VALUES |
| `03_delete.sql` | `test/delete.test` | predicate delete, no-match delete, delete-all |
| `04_update.sql` | `test/update.test` | single and multi-column update, update to NULL |
| `05_where.sql` | `test/where.test` | AND, OR, NOT, ranges, `<>` |
| `06_index.sql` | `test/index.test` | index creation, lookup, duplicate keys, delete through index |
| `07_trans.sql` | `test/trans.test` | COMMIT and ROLLBACK visibility |
| `08_null.sql` | `test/null.test` | three-valued logic |
| `09_sort.sql` | `test/sort.test` | ORDER BY asc/desc and multi-key |
| `10_limit.sql` | `test/limit.test` | LIMIT 0, partial, oversized, with DESC |

**These are adaptations, not the upstream suite.** The real Tcl tests are driven
by `scripts/run-focused-upstream.sh` through `tests/sql/tester.tcl`.

Cases that do not yet run are kept in `../upstream_unsupported/` with the reason.
