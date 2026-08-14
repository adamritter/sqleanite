# Upstream-adapted cases the Core path cannot run yet

Split out of `tests/sql/upstream/` so the passing corpus stays green while the
gaps stay visible, rather than being deleted or quietly edited away.

- `08_null_column_compare.sql` — `WHERE b=c`, comparing two columns. The Core
  predicate surface only admits `column <op> literal`, so this is rejected with
  a misleading message borrowed from the INSERT path
  (`non-literal INSERT value`). The three-valued-logic semantics itself is
  correct: `b=1`, `b<>1`, `NOT (b=1)`, `b IS NULL`, and the AND/OR combinations
  all match C SQLite exactly, including excluding NULL rows from `NOT (b=1)`.
