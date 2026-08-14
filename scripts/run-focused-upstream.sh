#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
runner=$root/tests/sql/runner.tcl
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
  /usr/bin/timeout 120 /usr/bin/tclsh "$runner" "$test_name"
done
