#!/bin/sh
# Asymptotic regression guard: run the same shapes at several sizes and widths,
# and report the growth factor per doubling.
#
# The twelve public workloads run at one fixed size (2,000 rows) and one narrow
# row (~40 bytes). Two real defects hid in that blind spot:
#
#   * a fixed sixteen-row page chunk made any table with rows over ~130 bytes
#     unloadable at specific row counts -- invisible because the public rows are
#     small;
#   * bulk load is superlinear in row count -- invisible because 2,000 rows is
#     small enough that the growth term barely shows.
#
# A ratio against C SQLite cannot catch either, because both engines are measured
# at the same single point. Only the growth factor across sizes catches them, so
# that is what this reports.
#
# A doubling of input should cost about 2x. Anything at or above the threshold is
# flagged as superlinear.
#
# Covers three shapes per tier: INSERT (bulk load), REPLACE on a hidden-rowid
# table, and UPDATE on one. The mutation shapes exist because the load path and
# the mutation path have had independent asymptotic defects: load was O(n^2) via
# `Table.upsert` rebuilding the declared-key map, and REPLACE/UPDATE on a
# hidden-rowid table still is.
#
#   scripts/run-scale-tiers.sh
#   WIDTHS=40,512 TIERS=1000,2000,4000,8000 scripts/run-scale-tiers.sh
#   SHAPES=replace TIERS=500,1000,2000 scripts/run-scale-tiers.sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
csql=${SQLITE3_BIN:-/usr/bin/sqlite3}
tiers=${TIERS:-1000,2000,4000,8000}
widths=${WIDTHS:-40,512}
# insert = bulk load; replace/update = mutation on a TEXT-PRIMARY-KEY table,
# which is the hidden-rowid path through `Table.upsert`.
shapes=${SHAPES:-insert,replace,update}
# Growth factor per doubling above which a shape is called superlinear. 2.0 is
# ideal; 2.4 leaves room for cache effects and page-boundary steps without
# masking a genuine n^1.5 or worse.
threshold=${THRESHOLD:-24}
# Space amplification ceiling, in tenths, of our file size over C SQLite's for
# identical data. Exceeding it fails the run. This column exists because the
# byte-aware page chunking that fixed a hard encode error was measured only for
# time, and silently cost 4.5x on disk: a leaf budget divided by two to cover the
# worst case left pages about half empty. Time-only guards do not catch that.
amp_ceiling=${AMP_CEILING:-15}
[ -x "$lean" ] || { printf 'not executable: %s\n' "$lean" >&2; exit 2; }

work=$(mktemp -d)
trap 'rm -r -- "$work"' EXIT

emit() { # $1 rows  $2 width  $3 shape  -> script on stdout
  python3 - "$1" "$2" "$3" <<'PYTHON'
import sys
rows, width, shape = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
value = 'v' * width
if shape == "insert":
    print("CREATE TABLE t(id INTEGER PRIMARY KEY, k TEXT NOT NULL, v TEXT NOT NULL);")
    print("CREATE INDEX ik ON t(k);")
    print("BEGIN;")
    for i in range(rows):
        print("INSERT INTO t VALUES(%d,'key%08d','%s');" % (i + 1, i, value))
    print("COMMIT;")
else:
    # A TEXT PRIMARY KEY is a rowid table with a hidden rowid, so REPLACE and
    # UPDATE here go through `Table.upsert`'s hidden-rowid branch. The load is
    # included in the timing for both shapes so the tiers stay comparable; the
    # load itself is linear, so any superlinear growth reported here is the
    # mutation.
    # Exact YCSB-shaped schema: TEXT primary key, one value field, implicit
    # primary index. No surrogate key, no explicit index, no NOT NULL.
    print("CREATE TABLE p (k TEXT PRIMARY KEY, v TEXT);")
    print("BEGIN;")
    for i in range(rows):
        print("INSERT INTO p VALUES('key%08d','%s');" % (i, value))
    print("COMMIT;")
    print("BEGIN;")
    if shape == "replace":
        for i in range(rows):
            print("REPLACE INTO p VALUES('key%08d','%s');" % (i, 'w' * width))
    else:
        for i in range(rows):
            print("UPDATE p SET v='%s' WHERE k='key%08d';" % ('w' * width, i))
    print("COMMIT;")
PYTHON
}

# Best of three, resetting the target database before every sample. Without the
# reset, re-running a load against an already-populated file fails on duplicate
# primary keys and returns almost immediately, so the minimum would be the cost
# of a failed insert rather than of the load. That mistake reads as perfectly
# linear scaling and is why the reset is inside the loop.
best_of_three() { # $1 = database file to remove, remaining arguments = command
  target=$1; shift
  best=99999999
  for _ in 1 2 3; do
    rm -f "$target" "$target-journal" "$target-wal"
    started=$(date +%s%N)
    "$@" >/dev/null 2>&1 || true
    ended=$(date +%s%N)
    sample=$(( (ended - started) / 1000000 ))
    [ "$sample" -lt "$best" ] && best=$sample
  done
  echo "$best"
}

failures=0
# Comma lists become space lists once, so the nested loops need no IFS juggling.
# Doing it with IFS inside three levels of loop is how the width list previously
# arrived as the single string "40,512".
shape_list=$(printf '%s' "$shapes" | tr ',' ' ')
width_list=$(printf '%s' "$widths" | tr ',' ' ')
tier_list=$(printf '%s' "$tiers" | tr ',' ' ')

for shape in $shape_list; do
for width in $width_list; do
  printf '\n=== %s, row width %s bytes ===\n' "$shape" "$width"
  printf '%-8s %10s %10s %8s %8s %8s %8s %8s\n' \
    rows lean_ms c_ms ratio growth read_ms lean_MB amp
  printf '%s\n' "-------------------------------------------------------------------------------"
  previous=""
  previous_read=""
  for rows in $tier_list; do
    emit "$rows" "$width" "$shape" > "$work/load.sql"
    # A single point read, repeated, so the read column is per-statement cost
    # plus one open rather than a whole-file scan.
    python3 - "$rows" "$shape" > "$work/read.sql" <<'PYTHON'
import sys
rows, shape = int(sys.argv[1]), sys.argv[2]
table = "t" if shape == "insert" else "p"
for i in range(20):
    print("SELECT k,v FROM %s WHERE k='key%08d';" % (table, (i * 7919) % rows))
PYTHON

    load=$(best_of_three "$work/l.db" \
      "$lean" --verified-file "$work/l.db" "$work/load.sql")
    cload=$(best_of_three "$work/s.db" \
      sh -c "$csql '$work/s.db' < '$work/load.sql'")
    # Reads need a populated database, and must not be reset between samples.
    rm -f "$work/l.db" "$work/l.db-journal"
    "$lean" --verified-file "$work/l.db" "$work/load.sql" >/dev/null 2>&1 || true
    best=99999999
    for _ in 1 2 3; do
      started=$(date +%s%N)
      "$lean" --verified-file "$work/l.db" "$work/read.sql" >/dev/null 2>&1 || true
      ended=$(date +%s%N)
      sample=$(( (ended - started) / 1000000 ))
      [ "$sample" -lt "$best" ] && best=$sample
    done
    read_ms=$best

    if [ "$cload" -le 0 ]; then ratio="-"; else
      ratio=$(awk -v a="$load" -v b="$cload" 'BEGIN{printf "%.0fx", a/b}'); fi

    # Both databases hold identical logical data at this point, so their sizes
    # are directly comparable.
    lean_bytes=$(stat -c%s "$work/l.db" 2>/dev/null || echo 0)
    c_bytes=$(stat -c%s "$work/s.db" 2>/dev/null || echo 0)
    lean_mb=$(awk -v b="$lean_bytes" 'BEGIN{printf "%.1f", b/1048576}')
    amp="-"
    if [ "$c_bytes" -gt 0 ] && [ "$lean_bytes" -gt 0 ]; then
      amp_tenths=$(awk -v a="$lean_bytes" -v b="$c_bytes" 'BEGIN{printf "%d", (a/b)*10}')
      amp=$(awk -v v="$amp_tenths" 'BEGIN{printf "%.1fx", v/10}')
      if [ "$amp_tenths" -ge "$amp_ceiling" ]; then
        amp="$amp!"
        failures=$((failures + 1))
      fi
    fi

    growth="-"
    if [ -n "$previous" ] && [ "$previous" -gt 0 ]; then
      scaled=$(awk -v a="$load" -v b="$previous" 'BEGIN{printf "%d", (a/b)*10}')
      growth=$(awk -v v="$scaled" 'BEGIN{printf "%.1fx", v/10}')
      if [ "$scaled" -ge "$threshold" ]; then
        growth="$growth!"
        failures=$((failures + 1))
      fi
    fi

    printf '%-8s %10s %10s %8s %8s %8s %8s %8s\n' \
      "$rows" "$load" "$cload" "$ratio" "$growth" "$read_ms" "$lean_mb" "$amp"
    previous=$load
    previous_read=$read_ms
  done
done
done

printf '\nlean=%s\nsqlite=%s\n' "$lean" "$csql"
printf 'growth is load time relative to the previous tier, which is half the rows.\n'
printf 'a growth factor marked ! is at or above %s.%s x and indicates superlinear scaling.\n' \
  "$((threshold / 10))" "$((threshold % 10))"
printf 'amp is our file size over C SQLite for identical data; ! is at or above %s.%sx.\n' \
  "$((amp_ceiling / 10))" "$((amp_ceiling % 10))"
if [ "$failures" -gt 0 ]; then
  printf '\n%s check(s) failed: superlinear growth or space amplification\n' "$failures" >&2
  exit 1
fi
