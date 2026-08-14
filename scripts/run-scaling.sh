#!/bin/sh
# Capacity and performance scaling curves: SQLeanite vs C SQLite.
# Emits TSV on stdout so the numbers in benchmarks.md can be regenerated.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
csqlite=${SQLITE3_BIN:-/usr/bin/sqlite3}
sizes=${SIZES:-"250 1000 5000 20000"}
work=$(mktemp -d)
trap 'rm -r -- "$work"' EXIT

ms() { s=$(date +%s%N); "$@" >/dev/null 2>&1 || true; e=$(date +%s%N); echo $(( (e - s) / 1000000 )); }

printf 'workload\trows\tlean_ms\tsqlite_ms\tpages\n'

for n in $sizes; do
  bulk=$work/bulk-$n.sql
  { echo "CREATE TABLE t(id INTEGER PRIMARY KEY, payload);"
    echo "BEGIN;"
    i=1; while [ "$i" -le "$n" ]; do echo "INSERT INTO t VALUES($i,'payload-row-$i');"; i=$((i+1)); done
    echo "COMMIT;"; } > "$bulk"

  ldb=$work/lean-$n.db; sdb=$work/c-$n.db
  rm -f "$ldb" "$sdb"
  lbulk=$(ms "$lean" --verified-file "$ldb" "$bulk")
  sbulk=$(ms sh -c "$csqlite '$sdb' < '$bulk'")
  pages=$("$csqlite" "$ldb" 'PRAGMA page_count;' 2>/dev/null || echo 0)
  printf 'bulk-insert-txn\t%s\t%s\t%s\t%s\n' "$n" "$lbulk" "$sbulk" "$pages"

  printf 'SELECT payload FROM t WHERE id=%s;\n' "$n" > "$work/point.sql"
  lp=$(ms "$lean" --verified-file "$ldb" "$work/point.sql")
  sp=$(ms sh -c "$csqlite '$sdb' < '$work/point.sql'")
  printf 'open+point-query\t%s\t%s\t%s\t%s\n' "$n" "$lp" "$sp" "$pages"

  printf 'SELECT id,payload FROM t ORDER BY payload LIMIT 50;\n' > "$work/sort.sql"
  lo=$(ms "$lean" --verified-file "$ldb" "$work/sort.sql")
  so=$(ms sh -c "$csqlite '$sdb' < '$work/sort.sql'")
  printf 'open+order-by\t%s\t%s\t%s\t%s\n' "$n" "$lo" "$so" "$pages"
done

# Capacity ceiling: first size that is refused.
printf '\n# capacity probe\n'
for n in $(echo "${CAPACITY-60000 100000}"); do
  cap=$work/cap-$n.sql
  { echo "CREATE TABLE t(id INTEGER PRIMARY KEY, payload);"; echo "BEGIN;"
    i=1; while [ "$i" -le "$n" ]; do echo "INSERT INTO t VALUES($i,'row-$i-pad');"; i=$((i+1)); done
    echo "COMMIT;"; } > "$cap"
  db=$work/cap-$n.db; rm -f "$db"
  if "$lean" --verified-file "$db" "$cap" >/dev/null 2>&1; then
    printf 'capacity\t%s\tok\t-\t%s\n' "$n" "$("$csqlite" "$db" 'PRAGMA page_count;' 2>/dev/null || echo 0)"
  else
    printf 'capacity\t%s\trefused\t-\t-\n' "$n"
  fi
done
