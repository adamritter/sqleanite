#!/bin/sh
# Compare median workload timings with the checked-in performance floor.
#
#   scripts/run-benchmark-regression.sh          three full runs
#   FAST=1 RUNS=1 scripts/run-benchmark-regression.sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
baseline=${BASELINE:-$root/scripts/performance-baseline.tsv}
runs=${RUNS:-3}
case $runs in *[!0-9]*|'') printf 'RUNS must be a positive integer\n' >&2; exit 2;; esac
if [ "$runs" -eq 0 ]; then
  printf 'RUNS must be a positive integer\n' >&2
  exit 2
fi
work=$(mktemp -d)
trap 'rm -r -- "$work"' EXIT

i=1
while [ "$i" -le "$runs" ]; do
  result=$work/run-$i.tsv
  RESULTS_TSV=$result ROWS=${ROWS:-2000} FAST=${FAST:-0} CASES=${CASES:-} \
    scripts/run-workload-benchmark.sh
  awk -F '\t' 'NR > 1 { print $1 "\t" $3 "\t" $4 }' "$result" >> "$work/all.tsv"
  i=$((i + 1))
done

# Input is tiny (at most twelve workloads times a handful of runs), so a
# portable insertion sort inside awk is clearer than depending on GNU tools.
summary=$work/summary.tsv
if awk -F '\t' -v baseline="$baseline" '
  function median(values, count,    i,j,x) {
    for (i = 2; i <= count; i++) {
      x = values[i]; j = i - 1
      while (j >= 1 && values[j] > x) { values[j + 1] = values[j]; j-- }
      values[j + 1] = x
    }
    if (count % 2) return values[(count + 1) / 2]
    return int((values[count / 2] + values[count / 2 + 1]) / 2)
  }
  BEGIN {
    while ((getline line < baseline) > 0) {
      split(line, field, "\t")
      if (field[1] != "id") {
        baseLean[field[1]] = field[3] + 0
        baseSQLite[field[1]] = field[4] + 0
      }
    }
    close(baseline)
  }
  {
    id = $1; count[id]++
    lean[id, count[id]] = $2 + 0
    sqlite[id, count[id]] = $3 + 0
    seen[id] = 1
  }
  END {
    failed = 0
    for (id in seen) {
      delete lv; delete sv
      for (i = 1; i <= count[id]; i++) {
        lv[i] = lean[id, i]; sv[i] = sqlite[id, i]
      }
      lm = median(lv, count[id]); sm = median(sv, count[id])
      change = (lm - baseLean[id]) / baseLean[id]
      ratio = sm == 0 ? 0 : lm / sm
      limit = baseLean[id] * 1.10
      if (limit < baseLean[id] + 5) limit = baseLean[id] + 5
      ok = lm <= limit && ratio <= 5.25
      printf "%-4s %10d %10d %8.1f%% %8.2fx %s\n", id, lm, baseLean[id], change * 100, ratio, ok ? "ok" : "FAIL"
      if (!ok) failed = 1
    }
    exit failed
  }
' "$work/all.tsv" > "$summary"; then
  regression_status=0
else
  regression_status=$?
fi
printf '%-4s %10s %10s %9s %9s %s\n' \
  id lean_med base_lean change vs_sql gate
sort "$summary"
exit "$regression_status"
