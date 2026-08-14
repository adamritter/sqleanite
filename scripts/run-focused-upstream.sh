#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
runner=$root/tests/sql/runner.tcl
sqlite_tests=${SQLITE_TEST_DIR:-}
if [ -z "$sqlite_tests" ] && [ -n "${SQLITE_SOURCE_DIR:-}" ]; then
  sqlite_tests=$SQLITE_SOURCE_DIR/test
fi
if [ -z "$sqlite_tests" ] || [ ! -f "$sqlite_tests/select1.test" ]; then
  printf '%s\n' \
    'set SQLITE_SOURCE_DIR (or SQLITE_TEST_DIR) to an upstream SQLite checkout' >&2
  exit 2
fi
sqlite_tests=$(CDPATH= cd -- "$sqlite_tests" && pwd)
run_tmp=$(mktemp -d)
lake_command=${LAKE_BIN:-lake}

cleanup() {
  if [ -n "$run_tmp" ] && [ -d "$run_tmp" ]; then
    rm -r -- "$run_tmp"
  fi
}
trap cleanup EXIT HUP INT TERM

cd "$root"
"$lake_command" build sqleanite_legacy_server

if [ "$#" -eq 0 ]; then
  set -- select1 insert
fi

cd "$run_tmp"
for test_name in "$@"; do
  printf 'upstream %s.test\n' "$test_name"
  /usr/bin/timeout 120 /usr/bin/tclsh "$runner" "$sqlite_tests" "$test_name"
done
