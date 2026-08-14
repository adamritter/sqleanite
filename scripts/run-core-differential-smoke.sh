#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
lean_bin=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
sqlite_bin=${SQLITE3_BIN:-/usr/bin/sqlite3}
corpus=$root/tests/sql/core_differential
run_tmp=$(mktemp -d)

cleanup() {
  if [ -n "$run_tmp" ] && [ -d "$run_tmp" ]; then
    rm -r -- "$run_tmp"
  fi
}
trap cleanup EXIT HUP INT TERM

if [ ! -x "$lean_bin" ] || [ ! -x "$sqlite_bin" ]; then
  printf '%s\n' "SQLeanite or SQLite CLI is unavailable" >&2
  exit 2
fi

passed=0
for sql_file in "$corpus"/*.sql; do
  name=$(basename "$sql_file")
  lean_out=$run_tmp/$name.lean.out
  sqlite_out=$run_tmp/$name.sqlite.out
  lean_db=$run_tmp/$name.lean.db
  sqlite_db=$run_tmp/$name.sqlite.db

  "$lean_bin" --verified-file "$lean_db" "$sql_file" >"$lean_out"
  "$sqlite_bin" -batch -noheader "$sqlite_db" <"$sql_file" >"$sqlite_out"
  if ! cmp -s "$lean_out" "$sqlite_out"; then
    printf 'not ok - %s\n' "$name" >&2
    diff -u "$sqlite_out" "$lean_out" || true
    exit 1
  fi
  passed=$((passed + 1))
  printf 'ok - %s\n' "$name"
done

# Reverse interop at the non-default SQLite page sizes scheduled for the MVP.
# These files are created by C SQLite, include a secondary index, and are then
# read independently by both engines.  At 1024 bytes the 200-row table spans
# multiple pages, so this exercises dynamic table and index traversal rather
# than merely accepting the header.
for page_size in 1024 8192 65536; do
  name=page-size-$page_size
  database=$run_tmp/$name.db
  query=$run_tmp/$name.sql
  lean_out=$run_tmp/$name.lean.out
  sqlite_out=$run_tmp/$name.sqlite.out
  "$sqlite_bin" "$database" \
    "PRAGMA page_size=$page_size; VACUUM;
     CREATE TABLE items(id INTEGER PRIMARY KEY, first, second);
     WITH RECURSIVE n(x) AS
       (VALUES(1) UNION ALL SELECT x+1 FROM n WHERE x<200)
       INSERT INTO items SELECT x, printf('value-%04d',x), x%7 FROM n;
     CREATE INDEX items_first ON items(first);"
  printf '%s\n' \
    'SELECT id,first,second FROM items WHERE id>=197 ORDER BY id;' \
    "SELECT id,first FROM items WHERE first='value-0100';" >"$query"
  "$lean_bin" --verified-file "$database" "$query" >"$lean_out"
  "$sqlite_bin" -batch -noheader "$database" <"$query" >"$sqlite_out"
  if ! cmp -s "$lean_out" "$sqlite_out"; then
    printf 'not ok - %s\n' "$name" >&2
    diff -u "$sqlite_out" "$lean_out" || true
    exit 1
  fi
  passed=$((passed + 1))
  printf 'ok - %s\n' "$name"
done

printf '%s Core differential cases passed\n' "$passed"
