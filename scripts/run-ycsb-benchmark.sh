#!/bin/sh
# YCSB-style workloads timed on SQLeanite and C SQLite.
#
# Parameters follow VeriBetrKV's OSDI'20 artifact rather than stock YCSB, so the
# numbers are comparable to published ones: one 512-byte field, and the workload
# set they actually run (A, B, C, D, F, Cuniform -- not E).
#
# Load and run phases are timed separately, because their headline insertion
# claim (24x BerkeleyDB, 8x slower than RocksDB) is the load phase alone.
#
# A timing is only reported when both engines produced identical output for the
# run phase; otherwise the comparison is meaningless.
#
#   RECORDS=1000 OPS=100 scripts/run-ycsb-benchmark.sh
#   WORKLOADS=A,C RECORDS=100000 OPS=10000 scripts/run-ycsb-benchmark.sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
csql=${SQLITE3_BIN:-/usr/bin/sqlite3}
records=${RECORDS:-1000}
ops=${OPS:-100}
seed=${SEED:-20260814}
runs=${RUNS:-3}
workloads=${WORKLOADS:-A,B,C,D,F,Cuniform}
keep=${KEEP_TRACES:-0}
# 512 matches VeriBetrKV. Lower values are reduced-fidelity triage only.
field=${FIELD_LENGTH:-512}

for value in "$records" "$ops" "$runs"; do
  case $value in *[!0-9]*|'') printf 'RECORDS, OPS and RUNS must be integers\n' >&2; exit 2;; esac
done
[ "$records" -ge 1 ] || { printf 'RECORDS must be at least 1\n' >&2; exit 2; }
[ -x "$lean" ] || { printf 'not executable: %s\n' "$lean" >&2; exit 2; }

work=$(mktemp -d)
if [ "$keep" = 1 ]; then
  printf 'traces kept in %s\n' "$work"
  trap 'rm -f "$work"/*.db "$work"/*.db-journal "$work"/*.db-wal 2>/dev/null || true' EXIT
else
  trap 'rm -r -- "$work"' EXIT
fi

# Milliseconds for one command, or -1 if it failed. Failure is reported by the
# caller rather than silently timed, so a broken run cannot look fast.
timed() {
  started=$(date +%s%N)
  if "$@" >/dev/null 2>&1; then
    ended=$(date +%s%N)
    echo $(( (ended - started) / 1000000 ))
  else
    echo -1
  fi
}

median() { # median of stdin integers
  sort -n | awk '{v[NR]=$1} END {print (NR%2) ? v[(NR+1)/2] : int((v[NR/2]+v[NR/2+1])/2)}'
}

printf 'YCSB-style: records=%s ops=%s runs=%s seed=%s\n' "$records" "$ops" "$runs" "$seed"
printf 'schema: usertable(id INTEGER PRIMARY KEY, ycsb_key TEXT NOT NULL, field0 TEXT NOT NULL) + INDEX(ycsb_key)\n'
if [ "$field" = 512 ]; then
  printf 'field length 512 (matches VeriBetrKV fieldcount=1 fieldlength=512)\n\n'
else
  printf 'field length %s -- REDUCED FIDELITY, not comparable to published numbers\n\n' "$field"
fi
printf '%-10s %9s %9s %7s   %9s %9s %7s  %s\n' \
  workload load_lean load_c ratio run_lean run_c ratio outputs
printf '%s\n' "---------------------------------------------------------------------------------------"

failures=0
oldifs=$IFS
IFS=,
for workload in $workloads; do
  IFS=$oldifs
  trace=$work/$workload
  python3 scripts/ycsb-trace.py --workload "$workload" --records "$records" \
    --ops "$ops" --out "$trace" --seed "$seed" --field-length "$field" >/dev/null

  load_l_samples=$work/ll; load_c_samples=$work/lc
  run_l_samples=$work/rl; run_c_samples=$work/rc
  : > "$load_l_samples"; : > "$load_c_samples"
  : > "$run_l_samples"; : > "$run_c_samples"
  match=unset
  broken=""

  attempt=1
  while [ "$attempt" -le "$runs" ]; do
    ldb=$work/l.db; sdb=$work/s.db
    rm -f "$ldb" "$ldb-journal" "$ldb-wal" "$sdb" "$sdb-journal" "$sdb-wal"

    t=$(timed "$lean" --verified-file "$ldb" "$trace/load.sql")
    [ "$t" = -1 ] && broken="$broken lean-load"; echo "$t" >> "$load_l_samples"
    t=$(timed sh -c "$csql '$sdb' < '$trace/load.sql'")
    [ "$t" = -1 ] && broken="$broken c-load"; echo "$t" >> "$load_c_samples"

    t=$(timed "$lean" --verified-file "$ldb" "$trace/run.sql")
    [ "$t" = -1 ] && broken="$broken lean-run"; echo "$t" >> "$run_l_samples"
    t=$(timed sh -c "$csql '$sdb' < '$trace/run.sql'")
    [ "$t" = -1 ] && broken="$broken c-run"; echo "$t" >> "$run_c_samples"

    # Compare run-phase output once, on a freshly loaded pair. Timing runs
    # mutate state, so output must be captured from its own clean load.
    if [ "$attempt" = 1 ]; then
      rm -f "$ldb" "$ldb-journal" "$ldb-wal" "$sdb" "$sdb-journal" "$sdb-wal"
      "$lean" --verified-file "$ldb" "$trace/load.sql" >/dev/null 2>&1 || true
      "$csql" "$sdb" < "$trace/load.sql" >/dev/null 2>&1 || true
      "$lean" --verified-file "$ldb" "$trace/run.sql" > "$work/l.out" 2>&1 || true
      "$csql" -batch -noheader "$sdb" < "$trace/run.sql" > "$work/s.out" 2>&1 || true
      if cmp -s "$work/l.out" "$work/s.out"; then
        match=same
      elif sort "$work/l.out" > "$work/l.sorted" 2>/dev/null &&
           sort "$work/s.out" > "$work/s.sorted" 2>/dev/null &&
           cmp -s "$work/l.sorted" "$work/s.sorted"; then
        match="same (unordered)"
      else
        match=DIFFER
      fi
    fi
    attempt=$((attempt + 1))
  done

  ll=$(median < "$load_l_samples"); lc=$(median < "$load_c_samples")
  rl=$(median < "$run_l_samples"); rc=$(median < "$run_c_samples")

  ratio() { # $1 lean $2 c
    if [ "$1" -lt 0 ] || [ "$2" -lt 0 ]; then echo "err"
    elif [ "$2" -le 0 ]; then echo "-"
    else awk -v a="$1" -v b="$2" 'BEGIN{printf "%.1fx", a/b}'; fi
  }
  lratio=$(ratio "$ll" "$lc"); rratio=$(ratio "$rl" "$rc")

  note=$match
  if [ -n "$broken" ]; then note="FAILED:$broken"; failures=$((failures + 1)); fi
  if [ "$match" = DIFFER ]; then failures=$((failures + 1)); fi

  printf '%-10s %9s %9s %7s   %9s %9s %7s  %s\n' \
    "$workload" "$ll" "$lc" "$lratio" "$rl" "$rc" "$rratio" "$note"
  IFS=,
done
IFS=$oldifs

printf '\nlean=%s\nsqlite=%s\n' "$lean" "$csql"
printf 'load ratios are the VeriBetrKV insertion comparison; run ratios are the A--F numbers.\n'
if [ "$failures" -gt 0 ]; then
  printf '\n%s workload(s) failed or produced differing output\n' "$failures" >&2
  exit 1
fi
