#!/bin/sh
# Run the upstream-adapted SQL corpus against SQLeanite and C SQLite.
#
# These are scenarios adapted from named upstream Tcl test files into plain SQL
# inside the subset the verified core implements. C SQLite is the oracle, so no
# expected values are hard-coded here.
#
# This is NOT the upstream Tcl suite. scripts/run-focused-upstream.sh runs the
# real thing through tests/sql/tester.tcl.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
csql=${SQLITE3_BIN:-/usr/bin/sqlite3}
corpus=$root/tests/sql/upstream
work=$(mktemp -d); trap 'rm -r -- "$work"' EXIT

ms() { s=$(date +%s%N); "$@" >/dev/null 2>&1 || true; e=$(date +%s%N); echo $(( (e - s) / 1000000 )); }

passed=0; failed=0
printf '%-26s %9s %9s %8s  %s\n' "test" "lean_ms" "sqlite_ms" "ratio" "result"
printf '%s\n' "---------------------------------------------------------------"
for sql in "$corpus"/*.sql; do
  name=$(basename "$sql")
  ldb=$work/l.db; sdb=$work/s.db
  rm -f "$ldb" "$ldb-journal" "$ldb-wal" "$sdb" "$sdb-journal" "$sdb-wal"
  lt=$(ms "$lean" --verified-file "$ldb" "$sql")
  rm -f "$ldb" "$ldb-journal" "$ldb-wal"
  st=$(ms sh -c "$csql '$sdb' < '$sql'")
  rm -f "$sdb" "$sdb-journal" "$sdb-wal"
  "$lean" --verified-file "$ldb" "$sql" > "$work/l.out" 2>&1 || true
  "$csql" -batch -noheader "$sdb" < "$sql" > "$work/s.out" 2>&1 || true
  if [ "$st" -eq 0 ]; then ratio="-"; else ratio=$(awk -v a="$lt" -v b="$st" 'BEGIN{printf "%.1fx", a/b}'); fi
  if cmp -s "$work/l.out" "$work/s.out"; then
    printf '%-26s %9s %9s %8s  ok\n' "$name" "$lt" "$st" "$ratio"; passed=$((passed+1))
  else
    printf '%-26s %9s %9s %8s  FAIL\n' "$name" "$lt" "$st" "$ratio"; failed=$((failed+1))
    diff "$work/s.out" "$work/l.out" | head -6 | sed 's/^/       /'
  fi
done
printf '\n%s passed, %s failed\n' "$passed" "$failed"
[ "$failed" -eq 0 ]
