#!/bin/sh
# Require every indexed empty/refill image to be structurally clean. Repeated
# cycles must preserve row/index contents and stop growing after first refill.
# The historical orphan-page exception is no longer accepted.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
csql=${SQLITE3_BIN:-/usr/bin/sqlite3}
rows=${ROWS:-200}
cycles=${CYCLES:-5}

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

# Emptying must immediately publish every retired page on the freelist.
"$lean" --verified-file "$db" "$work/empty.sql" > /dev/null
integrity=$("$csql" -batch -noheader "$db" "PRAGMA integrity_check;")
remaining=$("$csql" -batch -noheader "$db" "SELECT count(*) FROM orders;")
if [ "$integrity" != ok ] || [ "$remaining" != 0 ]; then
  printf 'not ok - empty indexed table: integrity=%s, rows=%s\n' "$integrity" "$remaining" >&2
  status=1
else
  printf 'ok - empty indexed table has no orphan pages\n'
fi

# Refill reuses allocation; every subsequent empty image is clean too.
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
    printf 'not ok - cycle %s: refill failed integrity_check: %s\n' \
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
  integrity=$("$csql" -batch -noheader "$db" "PRAGMA integrity_check;")
  if [ "$integrity" != ok ]; then
    printf 'not ok - cycle %s: empty image failed integrity_check: %s\n' "$cycle" "$integrity" >&2
    status=1
  fi
  cycle=$((cycle + 1))
done

if [ "$status" -eq 0 ]; then
  printf 'ok - %s empty/refill cycles stay clean and hold at %s pages\n' \
    "$cycles" "$baseline"
  printf 'page reclamation is integrity-check clean after every phase\n'
fi
exit "$status"
