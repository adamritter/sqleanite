#!/bin/sh
# Fast non-regression gate for the POPL'10 + FSCQ paper program.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lake_command=${LAKE_BIN:-lake}

printf '%s\n' '=== build ==='
"$lake_command" build >/dev/null
printf '%s\n' 'ok - build'

printf '%s\n' '=== proof hygiene ==='
scripts/lean-verification-audit.sh

printf '%s\n' '=== live path ==='
scripts/live-path-check.sh

printf '%s\n' '=== tests ==='
"$lake_command" exe sqleanite_tests | tail -1

printf '%s\n' '=== representative performance ==='
FAST=1 RUNS=${RUNS:-1} scripts/run-benchmark-regression.sh
