#!/bin/sh
# Falsifiable fresh-process generated INTEGER-index criterion. Equality hits
# and valid misses must read only routed index/primary paths rather than reopen
# and certify every row.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
sizes=${SIZES:-"250 500 1000 2000 4000"}
runs=${RUNS:-3}
check_flat=${CHECK_FLAT:-0}
work=$(mktemp -d)
trap 'rm -r -- "$work"' EXIT HUP INT TERM

timed_query() { # database, SQL file, expected stdout
  database=$1
  query=$2
  expected=$3
  started=$(date +%s%N)
  actual=$($lean --verified-file "$database" "$query")
  ended=$(date +%s%N)
  if [ "$actual" != "$expected" ]; then
    printf 'unexpected cold index output: expected=%s actual=%s\n' \
      "$expected" "$actual" >&2
    exit 1
  fi
  echo $(( (ended - started) / 1000000 ))
}

printf 'rows\thit_ms_best_of_%s\tmiss_ms_best_of_%s\tpages\n' "$runs" "$runs"
smallest=
largest=0
for rows in $sizes; do
  database=$work/cold-index-$rows.db
  seed=$work/seed-$rows.sql
  hit=$work/hit-$rows.sql
  miss=$work/miss-$rows.sql
  {
    echo "CREATE TABLE t(id INTEGER PRIMARY KEY,score INTEGER NOT NULL,payload TEXT NOT NULL);"
    echo "CREATE INDEX t_score ON t(score);"
    echo "BEGIN;"
    i=1
    while [ "$i" -le "$rows" ]; do
      echo "INSERT INTO t VALUES($i,$((i * 10)),'payload-$i');"
      i=$((i + 1))
    done
    echo "COMMIT;"
  } > "$seed"
  target=$((rows / 2 * 10))
  printf 'SELECT id FROM t WHERE score=%s;\n' "$target" > "$hit"
  printf 'SELECT id FROM t WHERE score=%s;\n' "$(((rows + 1) * 10))" > "$miss"
  "$lean" --verified-file "$database" "$seed" >/dev/null

  best_hit=
  best_miss=
  run=1
  while [ "$run" -le "$runs" ]; do
    hit_ms=$(timed_query "$database" "$hit" "$((rows / 2))")
    miss_ms=$(timed_query "$database" "$miss" "")
    if [ -z "$best_hit" ] || [ "$hit_ms" -lt "$best_hit" ]; then
      best_hit=$hit_ms
    fi
    if [ -z "$best_miss" ] || [ "$miss_ms" -lt "$best_miss" ]; then
      best_miss=$miss_ms
    fi
    run=$((run + 1))
  done
  pages=$(/usr/bin/sqlite3 "$database" 'PRAGMA page_count;')
  printf '%s\t%s\t%s\t%s\n' "$rows" "$best_hit" "$best_miss" "$pages"
  for elapsed in "$best_hit" "$best_miss"; do
    if [ -z "$smallest" ] || [ "$elapsed" -lt "$smallest" ]; then
      smallest=$elapsed
    fi
    if [ "$elapsed" -gt "$largest" ]; then largest=$elapsed; fi
  done
done

if [ "$check_flat" -eq 1 ]; then
  limit=$((smallest * 3 + 20))
  if [ "$largest" -gt "$limit" ]; then
    printf 'cold index curve is not sub-linear: min=%s max=%s limit=%s\n' \
      "$smallest" "$largest" "$limit" >&2
    exit 1
  fi
fi
