#!/bin/sh
# Falsifiable page-local update criterion. Open/decode is deliberately outside
# the timed region; the result is the SQL update plus journal, page writes,
# durability barriers and delta-scoped read-back.
#
# STATUS 2026-08-17: the criterion is NOT met. The commit is linear in total
# database pages, about 10 ms + 1.3 ms/page, so `CHECK_FLAT=1` passes at the
# default SIZES (250-4,000 rows is only 4-22 pages today) and fails from 20,000
# rows up. Do not widen the envelope to make it pass; the envelope is right and
# the commit is wrong. See docs/BENCHMARK_HISTORY.md#localized-point-update-scaling
# for the ~20x per-page regression this measures and why an unchanged wall clock
# at 4,000 rows concealed it.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
timer=${LOCALIZED_SCALING_BIN:-$root/.lake/build/bin/localized_scaling}
sizes=${SIZES:-"250 500 1000 2000 4000"}
runs=${RUNS:-3}
check_flat=${CHECK_FLAT:-0}
work=$(mktemp -d)
trap 'rm -r -- "$work"' EXIT

printf 'rows\tcommit_ms_best_of_%s\tpages\n' "$runs"
smallest=
largest=0
for rows in $sizes; do
  database=$work/localized-$rows.db
  seed=$work/seed-$rows.sql
  {
    echo "CREATE TABLE t(id INTEGER PRIMARY KEY,payload);"
    echo "BEGIN;"
    i=1
    while [ "$i" -le "$rows" ]; do
      echo "INSERT INTO t VALUES($i,'payload-$i');"
      i=$((i + 1))
    done
    echo "COMMIT;"
  } > "$seed"
  "$lean" --verified-file "$database" "$seed" >/dev/null
  best=
  run=1
  while [ "$run" -le "$runs" ]; do
    # Vary one same-width byte so every repetition is a real page mutation,
    # while taking the minimum rejects unrelated scheduler stalls.
    elapsed=$($timer "$database" $((rows / 2)) "$run")
    if [ -z "$best" ] || [ "$elapsed" -lt "$best" ]; then best=$elapsed; fi
    run=$((run + 1))
  done
  pages=$(/usr/bin/sqlite3 "$database" 'PRAGMA page_count;')
  printf '%s\t%s\t%s\n' "$rows" "$best" "$pages"
  if [ -z "$smallest" ] || [ "$best" -lt "$smallest" ]; then smallest=$best; fi
  if [ "$best" -gt "$largest" ]; then largest=$best; fi
done

if [ "$check_flat" -eq 1 ]; then
  # A generous envelope avoids turning host jitter into a false red build,
  # while still catching the former 20 -> 610 ms rebuild slope.
  limit=$((smallest * 2 + 10))
  if [ "$largest" -gt "$limit" ]; then
    printf 'localized commit curve is not flat: min=%s max=%s limit=%s\n' \
      "$smallest" "$largest" "$limit" >&2
    exit 1
  fi
fi
