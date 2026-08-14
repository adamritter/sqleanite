#!/bin/sh
# Reproduce every headline number in the documentation, in order.
#
#   scripts/reproduce-all.sh          full run
#   QUICK=1 scripts/reproduce-all.sh  skip the slow scaling and crash sweeps
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
export LAKE_BIN=${LAKE_BIN:-lake}

step() { printf '\n=== %s ===\n' "$1"; }

step "build"
$LAKE_BIN build

step "unit tests"
$LAKE_BIN exe sqleanite_tests | tail -1

step "verification audit (no sorry/axiom/native_decide/partial def)"
scripts/lean-verification-audit.sh

step "live-path check (the proved code is the code that runs)"
scripts/live-path-check.sh

step "theorem and trust-boundary manifest"
scripts/lean-manifest.sh > manifest.json
python3 -c "import json;d=json.load(open('manifest.json'));print('theorems',d['counts']['theorems'],'headline',d['counts']['headline_theorems'],'hygiene',d['hygiene'])"

scripts/run-core-differential-smoke.sh | tail -1

step "Lean mutation arm"
scripts/run-lean-mutations.sh | tail -3
awk -F'\t' 'NR>1 && $3=="passed"{print "UNDETECTED: "$1}' mutations/results.tsv
printf 'lean mutations: %s registered, all detected unless listed above\n' \
  "$(awk 'NR>1' mutations/registry.tsv | wc -l | tr -d ' ')"

if [ "${QUICK:-0}" = "1" ]; then
  printf '\nQUICK=1: skipping C mutation, scaling and crash sweeps\n'
  exit 0
fi

step "C mutation arm"
if [ -n "${SQLITE_SOURCE_DIR:-}" ]; then
  scripts/run-c-mutation-pilot.sh | tail -8
else
  printf 'skipped: set SQLITE_SOURCE_DIR to a clean SQLite checkout\n'
fi

step "crash fault injection (control: stock SQLite must survive)"
scripts/run-crash-injection.sh /usr/bin/sqlite3 25 | tail -4

step "power-loss injection (stock old-or-new control)"
scripts/run-powerloss-injection.sh /usr/bin/sqlite3 20 | tail -5

step "power-loss mutation (missing journal sync must tear)"
if [ -n "${SQLITE_SOURCE_DIR:-}" ]; then
  scripts/run-powerloss-mutation.sh 20 | tail -6
else
  printf 'skipped: set SQLITE_SOURCE_DIR to a clean SQLite checkout\n'
fi

step "workload benchmark (outputs verified per case)"
ROWS=${ROWS:-2000} scripts/run-workload-benchmark.sh

step "scaling curves"
scripts/run-scaling.sh
CHECK_FLAT=1 scripts/run-cold-primary-scaling.sh
CHECK_FLAT=1 scripts/run-cold-index-scaling.sh

printf '\nall reproduction steps completed\n'
