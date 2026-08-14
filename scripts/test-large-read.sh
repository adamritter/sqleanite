#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
case_dir=$(mktemp -d "${TMPDIR:-/tmp}/sqleanite-large-read.XXXXXX")
trap 'rm -r -- "$case_dir"' EXIT HUP INT TERM
database="$case_dir/large.db"

/usr/bin/sqlite3 "$database" "
  CREATE TABLE items(id INTEGER PRIMARY KEY, first TEXT, second TEXT);
  WITH RECURSIVE n(x) AS (
    VALUES(1) UNION ALL SELECT x + 1 FROM n WHERE x < 200000
  )
  INSERT INTO items SELECT x, 'a', 'b' FROM n;"

actual=$(printf '%s\n' 'SELECT count(*) FROM items;' |
  "$root/.lake/build/bin/sqleanite" --verified-file "$database")
test "$actual" = 200000

# Materializing and rendering the complete result used to exhaust the native
# stack near this size. Discarding stdout keeps the regression fast without
# weakening the traversal/rendering workload.
printf '%s\n' 'SELECT * FROM items;' |
  "$root/.lake/build/bin/sqleanite" --verified-file "$database" >/dev/null

printf '%s\n' 'ok - 200000-row read path remains stack-safe'
