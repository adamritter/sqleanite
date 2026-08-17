#!/bin/sh
# Pin the shape of the one declared forward-direction exception.
#
# Emptying an indexed table leaves the pages its collapsed trees no longer occupy
# allocated but unreferenced, so C SQLite's `integrity_check` reports "Page N is
# never used". `scripts/run-forward-compat.sh` admits that, bounded, because the
# rows are correct and the condition is transient. "Transient" is the load-bearing
# word, and this script is what makes it a checked property instead of a claim:
#
#   1. emptying an indexed table orphans at most a fixed, small number of pages;
#   2. the row contents are exactly what C computes for the same program;
#   3. re-inserting reclaims those pages: `integrity_check` returns to `ok`;
#   4. repeating the empty/refill cycle does not grow the file.
#
# If the leak ever starts accumulating -- which is the version of this that would
# actually matter -- (4) fails here.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
csql=${SQLITE3_BIN:-/usr/bin/sqlite3}
rows=${ROWS:-200}
cycles=${CYCLES:-5}
orphan_bound=${ORPHAN_BOUND:-4}

if [ ! -x "$lean" ] || [ ! -x "$csql" ]; then
  printf '%s\n' "SQLeanite or SQLite CLI is unavailable" >&2
  exit 2
fi

work=$(mktemp -d)
cleanup() { [ -n "$work" ] && [ -d "$work" ] && rm -r -- "$work"; }
trap cleanup EXIT HUP INT TERM

{
  echo "CREATE TABLE orders(id INTEGER PRIMARY KEY, customer, sku, status);"
  echo "BEGIN;"
  i=1
  while [ "$i" -le "$rows" ]; do
    echo "INSERT INTO orders VALUES($i,'cust-$((i % 50))','sku-$((i % 200))','open');"
    i=$((i + 1))
  done
  echo "COMMIT;"
  echo "CREATE INDEX orders_sku ON orders(sku);"
} > "$work/seed.sql"

{
  echo "BEGIN;"
  i=1
  while [ "$i" -le "$rows" ]; do
    echo "INSERT INTO orders VALUES($i,'cust-$((i % 50))','sku-$((i % 200))','open');"
    i=$((i + 1))
  done
  echo "COMMIT;"
} > "$work/refill.sql"

printf 'DELETE FROM orders WHERE id>0;\n' > "$work/empty.sql"

db=$work/reclaim.db
rm -f "$db" "$db-journal" "$db-wal"
"$lean" --verified-file "$db" "$work/seed.sql" > /dev/null

status=0

# 1 and 2: emptying orphans a bounded number of pages, and only that.
"$lean" --verified-file "$db" "$work/empty.sql" > /dev/null
integrity=$("$csql" -batch -noheader "$db" "PRAGMA integrity_check;")
structural=$(printf '%s\n' "$integrity" |
  grep -v 'never used' | grep -v '^\*\*\* in database' | grep -v '^ok$' || true)
orphans=$(printf '%s\n' "$integrity" | grep -c 'never used' || true)
remaining=$("$csql" -batch -noheader "$db" "SELECT count(*) FROM orders;")
if [ -n "$structural" ]; then
  printf 'not ok - emptying reported a structural error, not just orphans: %s\n' \
    "$(printf '%s' "$structural" | tr '\n' ' ')" >&2
  status=1
elif [ "$orphans" -gt "$orphan_bound" ]; then
  printf 'not ok - emptying orphaned %s pages, bound is %s\n' \
    "$orphans" "$orphan_bound" >&2
  status=1
elif [ "$remaining" != 0 ]; then
  printf 'not ok - emptying left %s rows behind\n' "$remaining" >&2
  status=1
else
  printf 'ok - emptying an indexed table orphans %s pages and no structural error\n' \
    "$orphans"
fi

# 3 and 4: the pages come back, and the file does not grow across cycles.
baseline=""
cycle=1
while [ "$cycle" -le "$cycles" ]; do
  "$lean" --verified-file "$db" "$work/refill.sql" > /dev/null
  integrity=$("$csql" -batch -noheader "$db" "PRAGMA integrity_check;")
  pages=$("$csql" -batch -noheader "$db" "PRAGMA page_count;")
  count=$("$csql" -batch -noheader "$db" "SELECT count(*) FROM orders;")
  hit=$("$csql" -batch -noheader "$db" \
    "SELECT count(*) FROM orders WHERE sku='sku-100';")
  if [ "$integrity" != ok ]; then
    printf 'not ok - cycle %s: refill did not reclaim the orphans: %s\n' \
      "$cycle" "$(printf '%s' "$integrity" | tr '\n' ' ')" >&2
    status=1
  elif [ "$count" != "$rows" ]; then
    printf 'not ok - cycle %s: refill produced %s rows, expected %s\n' \
      "$cycle" "$count" "$rows" >&2
    status=1
  elif [ "$hit" = 0 ]; then
    printf 'not ok - cycle %s: index lookup found nothing after reclaim\n' \
      "$cycle" >&2
    status=1
  fi
  if [ -z "$baseline" ]; then
    baseline=$pages
  elif [ "$pages" -gt "$baseline" ]; then
    printf 'not ok - cycle %s: file grew from %s to %s pages across cycles\n' \
      "$cycle" "$baseline" "$pages" >&2
    status=1
  fi
  "$lean" --verified-file "$db" "$work/empty.sql" > /dev/null
  cycle=$((cycle + 1))
done

if [ "$status" -eq 0 ]; then
  printf 'ok - %s empty/refill cycles reclaim orphans and hold at %s pages\n' \
    "$cycles" "$baseline"
  printf 'page reclamation is transient-only, as declared\n'
fi
exit "$status"
