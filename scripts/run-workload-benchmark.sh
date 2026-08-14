#!/bin/sh
# Twelve realistic workloads timed on SQLeanite and C SQLite.
#
# Every workload is expressible in both engines and deliberately stays inside
# the supported Core subset. Outputs are compared, and a timing is only reported
# when both engines produced identical results -- otherwise the comparison is
# meaningless.
#
#   ROWS=2000 scripts/run-workload-benchmark.sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
csql=${SQLITE3_BIN:-/usr/bin/sqlite3}
rows=${ROWS:-2000}
results_tsv=${RESULTS_TSV:-}
cases=${CASES:-}
if [ "${FAST:-0}" = 1 ] && [ -z "$cases" ]; then
  cases=01,03,04,07,08,09
fi
case $rows in *[!0-9]*|'') printf 'ROWS must be an integer\n' >&2; exit 2;; esac
if [ "$rows" -lt 2000 ]; then
  printf 'ROWS must be at least 2000\n' >&2
  exit 2
fi
work=$(mktemp -d)
trap 'rm -r -- "$work"' EXIT

if [ -n "$results_tsv" ]; then
  printf 'id\tname\tlean_ms\tsqlite_ms\tratio\toutputs\n' > "$results_tsv"
fi

timed() { # $1 = status file, remaining arguments = command
  status_file=$1; shift
  started=$(date +%s%N)
  if "$@" >/dev/null 2>&1; then command_status=0; else command_status=$?; fi
  ended=$(date +%s%N)
  printf '%s\n' "$command_status" > "$status_file"
  echo $(( (ended - started) / 1000000 ))
}

corpus=$root/tests/sql/workloads

# Seed database, shared starting point for the read/update workloads. Built
# from the versioned template so the workload set stays reviewable.
seed=$work/seed.sql
{ echo "BEGIN;"
  i=1
  while [ "$i" -le "$rows" ]; do
    echo "INSERT INTO orders VALUES($i,'cust-$((i % 50))','sku-$((i % 200))','open');"
    i=$((i + 1))
  done
  j=0
  while [ "$j" -lt 50 ]; do
    echo "INSERT INTO customers VALUES($j,'name-$j','region-$((j % 5))');"
    j=$((j + 1))
  done
  echo "COMMIT;"
} > "$work/rows.sql"
awk -v f="$work/rows.sql" '{ if ($0 == "@ROWS@") { while ((getline l < f) > 0) print l } else print }' \
  "$corpus/00_seed.sql.in" > "$seed"

instantiate() { # $1 = template stem, remaining arguments are sed expressions
  stem=$1; shift
  sed "$@" "$corpus/$stem.sql.in" > "$work/$stem.sql"
}

instantiate 03_point_lookup \
  -e "s/@POINT@/$((rows / 2))/g"
instantiate 05_range_scan \
  -e "s/@RANGE_START@/$((rows - 100))/g"
instantiate 07_bulk_update \
  -e "s/@UPDATE_START@/$((rows - 200))/g"
instantiate 08_bulk_delete \
  -e "s/@DELETE_START@/$((rows - 300))/g" \
  -e "s/@DELETE_CHECK_START@/$((rows - 400))/g"
instantiate 12_mixed_session \
  -e "s/@MIXED_RANGE_START@/$((rows - 20))/g"

printf '%-34s %10s %10s %8s %s\n' "workload" "lean_ms" "sqlite_ms" "ratio" "outputs"
printf '%s\n' "-----------------------------------------------------------------------------"

# Each execution gets a freshly seeded database. Several workloads mutate
# state, so reusing one database across the timing and output runs would
# measure and compare different things.
fresh_lean() { rm -f "$1" "$1-journal" "$1-wal"
  [ "$2" = y ] && "$lean" --verified-file "$1" "$seed" >/dev/null 2>&1; return 0; }
fresh_c() { rm -f "$1" "$1-journal" "$1-wal"
  [ "$2" = y ] && "$csql" "$1" < "$seed" >/dev/null 2>&1; return 0; }

run_case() { # $1 name  $2 sql-file  $3 needs-seed
  name=$1; sql=$2; seeded=$3
  ldb=$work/l.db; sdb=$work/s.db
  fresh_lean "$ldb" "$seeded"
  lt=$(timed "$work/l.status" "$lean" --verified-file "$ldb" "$sql")
  lstatus=$(cat "$work/l.status")
  fresh_c "$sdb" "$seeded"
  ct=$(timed "$work/c.status" sh -c "$csql '$sdb' < '$sql'")
  cstatus=$(cat "$work/c.status")
  fresh_lean "$ldb" "$seeded"
  if "$lean" --verified-file "$ldb" "$sql" > "$work/l.out" 2>&1; then
    loutput_status=0
  else
    loutput_status=$?
  fi
  fresh_c "$sdb" "$seeded"
  if "$csql" -batch -noheader "$sdb" < "$sql" > "$work/s.out" 2>&1; then
    coutput_status=0
  else
    coutput_status=$?
  fi
  if [ "$lstatus" -ne 0 ] || [ "$cstatus" -ne 0 ] ||
      [ "$loutput_status" -ne 0 ] || [ "$coutput_status" -ne 0 ]; then
    printf 'workload failed unexpectedly: %s (timed Lean=%s C=%s; output Lean=%s C=%s)\n' \
      "$name" "$lstatus" "$cstatus" "$loutput_status" "$coutput_status" >&2
    sed -n '1,20p' "$work/l.out" >&2
    sed -n '1,20p' "$work/s.out" >&2
    exit 1
  fi
  # Exact match first. If only the row order differs, say so rather than
  # calling it a difference: SQL does not fix row order without ORDER BY.
  if cmp -s "$work/l.out" "$work/s.out"; then
    match=same
  elif sort "$work/l.out" > "$work/l.sorted" && sort "$work/s.out" > "$work/s.sorted" &&
       cmp -s "$work/l.sorted" "$work/s.sorted"; then
    match="same (unordered)"
  else
    match=DIFFER
  fi
  if [ "$ct" -eq 0 ]; then ratio="-"; else ratio=$(awk -v a="$lt" -v b="$ct" 'BEGIN{printf "%.1fx", a/b}'); fi
  printf '%-34s %10s %10s %8s %s\n' "$name" "$lt" "$ct" "$ratio" "$match"
  if [ -n "$results_tsv" ]; then
    id=${name%% *}
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$id" "$name" "$lt" "$ct" "${ratio%x}" "$match" >> "$results_tsv"
  fi
}

wanted() { # $1 = stable two-digit workload id
  [ -z "$cases" ] || case ",$cases," in *,"$1",*) true;; *) false;; esac
}

run_selected() { # $1 id  $2 name  $3 sql-file  $4 needs-seed
  id=$1; shift
  if wanted "$id"; then run_case "$@"; fi
}

# 1. Bulk load inside one transaction (ETL / import).
cp "$seed" "$work/w01.sql"
run_selected 01 "01 bulk load ($rows rows, 1 txn)" "$work/w01.sql" n

# 2. Row-at-a-time inserts in autocommit (naive application loop).
{ k=1; while [ "$k" -le 100 ]; do echo "INSERT INTO t VALUES($k,'v-$k');"; k=$((k+1)); done
} > "$work/rows02.sql"
awk -v f="$work/rows02.sql" '{ if ($0 == "@ROWS@") { while ((getline l < f) > 0) print l } else print }' \
  "$corpus/02_autocommit_inserts.sql.in" > "$work/w02.sql"
run_selected 02 "02 autocommit inserts (100)" "$work/w02.sql" n

run_selected 03 "03 point lookup by PK" "$work/03_point_lookup.sql" y

run_selected 04 "04 indexed lookup (secondary)" "$corpus/04_indexed_lookup.sql" y

run_selected 05 "05 range scan + predicate" "$work/05_range_scan.sql" y

run_selected 06 "06 ORDER BY + LIMIT 20" "$corpus/06_order_by_limit.sql" y

run_selected 07 "07 bulk UPDATE by predicate" "$work/07_bulk_update.sql" y

run_selected 08 "08 bulk DELETE by predicate" "$work/08_bulk_delete.sql" y

run_selected 09 "09 inner join (2 tables)" "$corpus/09_inner_join.sql" y

run_selected 10 "10 read-modify-write txn" "$corpus/10_read_modify_write.sql" y

run_selected 11 "11 cold open + 1 read" "$corpus/11_cold_open_read.sql" y

run_selected 12 "12 mixed read/write session" "$work/12_mixed_session.sql" y

printf '\nrows=%s   lean=%s   sqlite=%s\n' "$rows" "$lean" "$csql"
