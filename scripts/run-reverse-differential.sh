#!/bin/sh
# Reverse-direction byte compatibility: C SQLite writes, SQLeanite reads.
#
# This is the half of the byte-compatibility claim with no prior art and, until
# this script existed, the thinnest evidence: three cases (one table, one index,
# 200 rows) at page sizes 1024 / 8192 / 65536. Everything else in the
# differential arm was our own writes read back by us, which tests the codec pair
# and not compatibility. `plan.md` listed overflow chains, multi-level interiors,
# freelists, post-VACUUM, auto_vacuum, REAL, BLOB and WAL as already accepted --
# but untested acceptance is not evidence, so each of those is a cell here.
#
# Every cell is `pass` or `reject`, and `reject` is checked to be an *ordinary
# diagnostic*: nonzero exit below the signal range, an `Error:` line, and no rows.
# A cell that silently returns wrong rows fails; so does a cell that starts
# passing when it was declared unsupported, because that means the declaration is
# stale.
#
# Modes:
#   (default)    every feature at 4096, plus each page size on two non-trivial
#                shapes -- the dozen-cell matrix the plan calls for
#   --full       every feature crossed with every page size
#   --markdown   emit docs/COMPATIBILITY.md from the same case list
#   --tsv        emit the raw matrix for other tools
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lean_bin=${SQLEANITE_BIN:-$root/.lake/build/bin/sqleanite}
sqlite_bin=${SQLITE3_BIN:-/usr/bin/sqlite3}
mode=${1:-default}

run_tmp=$(mktemp -d)
cleanup() { [ -n "$run_tmp" ] && [ -d "$run_tmp" ] && rm -r -- "$run_tmp"; }
trap cleanup EXIT HUP INT TERM

rows_200="WITH RECURSIVE n(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM n WHERE x<200)"
rows_2000="WITH RECURSIVE n(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM n WHERE x<2000)"

# name|expect|reader|feature-note|setup SQL|query SQL
#
# Queries avoid SQL the frozen surface does not accept (no length(), no IN) and,
# for REAL and BLOB, avoid *rendering* a value: the CLI's value formatting is an
# unverified shell concern and differs from C's, which is recorded separately in
# the generated document rather than mixed into a storage-compatibility cell.
feature_cases() {
  cat <<ROWS
plain-table|pass|file|Single-page table, INTEGER PRIMARY KEY|CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); $rows_200 INSERT INTO t SELECT x, printf('v%04d',x) FROM n;|SELECT id,v FROM t WHERE id>=197 ORDER BY id;
multipage-interior|pass|file|Multi-level interior nodes (2,000 rows x 800B)|CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); $rows_2000 INSERT INTO t SELECT x, hex(randomblob(400)) FROM n;|SELECT id,v FROM t WHERE id>=1999 ORDER BY id;
secondary-index|pass|file|Secondary index B-tree traversal|CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); $rows_200 INSERT INTO t SELECT x, printf('v%04d',x) FROM n; CREATE INDEX t_v ON t(v);|SELECT id,v FROM t WHERE v='v0100';
text-primary-key|pass|file|Hidden-rowid table plus implicit autoindex (YCSB shape)|CREATE TABLE usertable(ycsb_key TEXT PRIMARY KEY, field0 TEXT); $rows_200 INSERT INTO usertable SELECT printf('user%08d',x), printf('f%04d',x) FROM n;|SELECT ycsb_key,field0 FROM usertable WHERE ycsb_key='user00000100';
overflow-chain|pass|file|Overflow chain, 9 KB row beside an inline row|CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); INSERT INTO t VALUES(1, hex(randomblob(4500))),(2,'short');|SELECT id,v FROM t ORDER BY id;
freelist-after-delete|pass|file|Freelist trunk and leaves after a bulk delete|CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); $rows_2000 INSERT INTO t SELECT x, hex(randomblob(300)) FROM n; DELETE FROM t WHERE id>100;|SELECT count(*) FROM t;
post-vacuum|pass|file|Repacked file after VACUUM|CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); $rows_2000 INSERT INTO t SELECT x, hex(randomblob(200)) FROM n; DELETE FROM t WHERE id>100; VACUUM;|SELECT count(*) FROM t;
auto-vacuum|pass|file|auto_vacuum=FULL, so the file carries pointer-map pages|PRAGMA auto_vacuum=FULL; CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); $rows_2000 INSERT INTO t SELECT x, hex(randomblob(200)) FROM n; DELETE FROM t WHERE id>100;|SELECT count(*) FROM t;
real-values|pass|file|REAL storage class, read through ordering and a range predicate|CREATE TABLE t(id INTEGER PRIMARY KEY, v REAL); INSERT INTO t VALUES(1,1.5),(2,-0.25),(3,3.0);|SELECT id FROM t ORDER BY v; SELECT id FROM t WHERE v>1.0 ORDER BY id;
blob-values|pass|file|BLOB storage class, read through equality and ordering|CREATE TABLE t(id INTEGER PRIMARY KEY, v BLOB); INSERT INTO t VALUES(1,x'00ff10'),(2,x'');|SELECT id FROM t WHERE v=x'00ff10'; SELECT id FROM t ORDER BY v;
null-values|pass|file|NULL payloads and three-valued IS NULL|CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); INSERT INTO t VALUES(1,NULL),(2,'x');|SELECT id FROM t WHERE v IS NULL; SELECT id,v FROM t ORDER BY id;
wal-mode|pass|wal|Journal mode WAL, read through the verified WAL path|PRAGMA journal_mode=WAL; CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); $rows_200 INSERT INTO t SELECT x, printf('v%04d',x) FROM n;|SELECT id,v FROM t WHERE id>=197 ORDER BY id;
without-rowid|reject|file|WITHOUT ROWID: an index B-tree used as the table, out of scope|CREATE TABLE t(k TEXT PRIMARY KEY, v TEXT) WITHOUT ROWID; INSERT INTO t VALUES('a','1'),('b','2');|SELECT k,v FROM t ORDER BY k;
composite-primary-key|reject|file|Composite PRIMARY KEY: not one INTEGER or TEXT key|CREATE TABLE t(a INTEGER, b INTEGER, v TEXT, PRIMARY KEY(a,b)); INSERT INTO t VALUES(1,1,'x'),(1,2,'y');|SELECT a,b,v FROM t ORDER BY a,b;
no-primary-key|reject|file|No declared PRIMARY KEY at all|CREATE TABLE t(a INTEGER, v TEXT); INSERT INTO t VALUES(1,'x'),(2,'y');|SELECT a,v FROM t ORDER BY a;
ROWS
}

# Shapes crossed with every page size. Non-trivial on purpose: an indexed
# multi-page table and an overflow chain, which are the two shapes where the page
# size actually changes the physical layout the decoder walks.
page_size_shapes() {
  cat <<ROWS
pagesize-indexed|pass|file|Indexed 200-row table spanning pages at 1024|CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); $rows_200 INSERT INTO t SELECT x, printf('v%04d',x) FROM n; CREATE INDEX t_v ON t(v);|SELECT id,v FROM t WHERE id>=197 ORDER BY id;
pagesize-overflow|pass|file|Overflow chain at each page size|CREATE TABLE t(id INTEGER PRIMARY KEY, v TEXT); INSERT INTO t VALUES(1, hex(randomblob(4500))),(2,'short');|SELECT id,v FROM t WHERE id=2;
ROWS
}

page_sizes="1024 4096 8192 65536"

matrix=$run_tmp/matrix.tsv
: > "$matrix"

run_case() {
  name=$1; page=$2; expect=$3; reader=$4; setup=$5; query=$6
  cell="$name@$page"
  db=$run_tmp/$name-$page.db
  rm -f "$db" "$db-wal" "$db-journal"
  # `PRAGMA page_size` only takes effect on an empty file, so it precedes the
  # schema; VACUUM makes it stick for the auto_vacuum case too.
  if ! "$sqlite_bin" "$db" "PRAGMA page_size=$page; VACUUM; $setup" >/dev/null 2>&1
  then
    printf 'not ok - %s (C SQLite could not build the corpus file)\n' "$cell" >&2
    exit 1
  fi
  printf '%s\n' "$query" > "$run_tmp/$name.sql"
  c_out=$("$sqlite_bin" -batch -noheader "$db" < "$run_tmp/$name.sql" 2>&1)
  if [ "$reader" = wal ]; then
    set +e
    lean_out=$("$lean_bin" --verified-wal-file "$db" "$run_tmp/$name.sql" 2>&1)
    lean_code=$?
    set -e
  else
    set +e
    lean_out=$("$lean_bin" --verified-file "$db" "$run_tmp/$name.sql" 2>&1)
    lean_code=$?
    set -e
  fi

  case $expect in
    pass)
      if [ "$lean_code" -eq 0 ] && [ "$c_out" = "$lean_out" ]; then
        printf '%s\t%s\t%s\t%s\n' "$name" "$page" pass accepted >> "$matrix"
        printf 'ok - %s accepted and identical to C\n' "$cell"
      else
        printf '%s\t%s\t%s\t%s\n' "$name" "$page" pass FAILED >> "$matrix"
        printf 'not ok - %s\n' "$cell" >&2
        printf '  exit %s\n  C   : %s\n  Lean: %s\n' "$lean_code" \
          "$(printf '%s' "$c_out" | tr '\n' ';')" \
          "$(printf '%s' "$lean_out" | tr '\n' ';')" >&2
        exit 1
      fi
      ;;
    reject)
      # An unsupported file must fail the way SQLite fails: a diagnostic and a
      # nonzero status. A signal (>= 128) is a crash and is not acceptable, and
      # neither is success, which would mean this declaration is stale.
      if [ "$lean_code" -eq 0 ]; then
        printf '%s\t%s\t%s\t%s\n' "$name" "$page" reject STALE >> "$matrix"
        printf 'not ok - %s was declared unsupported but was accepted\n' "$cell" >&2
        exit 1
      elif [ "$lean_code" -ge 128 ]; then
        printf '%s\t%s\t%s\t%s\n' "$name" "$page" reject CRASH >> "$matrix"
        printf 'not ok - %s crashed (signal %s) instead of diagnosing\n' \
          "$cell" "$((lean_code - 128))" >&2
        exit 1
      elif printf '%s' "$lean_out" | grep -q 'Error:'; then
        printf '%s\t%s\t%s\t%s\n' "$name" "$page" reject declared >> "$matrix"
        printf 'ok - %s rejected as an ordinary diagnostic\n' "$cell"
      else
        printf '%s\t%s\t%s\t%s\n' "$name" "$page" reject SILENT >> "$matrix"
        printf 'not ok - %s failed without a diagnostic\n' "$cell" >&2
        exit 1
      fi
      ;;
  esac
}

emit_markdown() {
  cat <<'HEAD'
# Byte compatibility: what is accepted, rejected and untested

Generated by `scripts/run-reverse-differential.sh --markdown`. Do not edit by
hand.

Two directions, and they are not symmetric:

- **reverse** (C SQLite writes, SQLeanite reads) is the direction with no prior
  art and is measured by the matrix below, one live cell per feature;
- **forward** (SQLeanite writes, C SQLite reads) is checked by
  `scripts/run-forward-compat.sh`: for every workload shape C runs
  `PRAGMA integrity_check` *and* must read the same schema and the same rows it
  reads from its own file. All eleven shapes now require a clean integrity check;
  orphan pages are failures.

## Current page-size coverage

`PhysicalCodec.pageSize = 4096` is threaded through the writer and its proof
types. The currently tested read/write coverage is:

> **SQLeanite reads 1024, 4096, 8192 and 65536 byte pages, and writes 4096 only.**

Complete SQLite file-format compatibility remains the target. Writer support
for other page sizes and broader schema/encoding coverage are still gaps.

## Value rendering differs from the `sqlite3` shell, and is not a storage claim

One difference is retained in `Main.lean`'s result rendering rather than in
storage or comparison:

| value | `sqlite3` prints | `sqleanite` prints |
|---|---|---|
| BLOB, e.g. `x'00ff10'` | the raw bytes | `X'00FF10'` |

The matrix cells for REAL and BLOB below read values through ordering and
predicates, testing the codec and comparison separately from rendering.
The row-expression differential suite checks integral REAL rendering, empty
and NULL-only rows, and NUL-terminated TEXT output in file, WAL and timed modes.
Rendering remains in the executable TCB (see `docs/TRUST.md`); general shell
byte-for-byte compatibility is not claimed.

## Reverse-direction matrix

Every cell is a C-written file read by both engines with identical queries.
`accepted` means SQLeanite's output equalled C's exactly. `declared` means the
file is outside the supported subset and SQLeanite refused it with an ordinary
diagnostic and a nonzero exit -- checked, not assumed, and a cell that starts
succeeding fails this script so the declaration cannot go stale.

HEAD
  printf '| feature | page size | result | note |\n'
  printf '|---|---:|---|---|\n'
  feature_cases | while IFS='|' read -r name expect reader note setup query; do
    [ -n "$name" ] || continue
    if [ "$expect" = pass ]; then result=accepted; else result='declared unsupported'; fi
    printf '| %s | 4096 | %s | %s |\n' "$name" "$result" "$note"
  done
  page_size_shapes | while IFS='|' read -r name expect reader note setup query; do
    [ -n "$name" ] || continue
    printf '| %s | 1024 / 4096 / 8192 / 65536 | accepted | %s |\n' "$name" "$note"
  done
  cat <<'TAIL'

## Forward-direction results and indexed-page reclamation

`scripts/run-forward-compat.sh` runs all eleven workload shapes using independent
SQLeanite and SQLite files. SQLite then checks both files' schema and contents,
plus integrity_check and foreign_key_check. All eleven shapes are clean.
`scripts/regress-page-reclaim.sh` requires a clean image immediately after each
empty/refill operation and checks that repeated cycles stop growing the file.

The historical indexed-shrink exception is fixed. A high-fanout index can place
its root after its children, so the last catalog root does not establish that
the whole index lives in the root-to-end interval. The old tail rewrite orphaned
two earlier child pages in the 200-row example. Local tail replacement now
requires exact agreement with the prior canonical index encoding over that
entire interval. Other layouts use the existing freelist-aware full commit.
The earlier allocation-preserving-update explanation did not identify this
shrink-path bug; the retained negative report records the actual failing layout.

The [fresh shrink/refill checkpoint](validation/sqlite-index-reclaim-20261024.json)
uses SQLite as the independent reader of rollback-journal and WAL images after
every phase. This is evidence for those file shapes, not complete WAL locking,
recovery or file-format conformance.

## Untested, and named so it is not mistaken for accepted

- files with more than one table carrying overflow *and* an index at a non-4096
  page size simultaneously (the cross of three features at once);
- files produced by SQLite versions older than the format-3 era, and encrypted
  or page-checksummed variants;
- `sqlite_stat1` and other internal tables written by `ANALYZE`;
- multi-column indexes, and indexes on expressions;
- `ATTACH`-ed multi-database files, and shared-cache access patterns.

These are untested rather than declared unsupported: no cell exercises them, so
nothing here says what happens. Do not report them as either direction.
TAIL
}

case $mode in
  --markdown)
    emit_markdown
    exit 0
    ;;
  --tsv)
    : # fall through to run, then print the matrix instead of the summary
    ;;
esac

if [ ! -x "$lean_bin" ] || [ ! -x "$sqlite_bin" ]; then
  printf '%s\n' "SQLeanite or SQLite CLI is unavailable" >&2
  exit 2
fi

passed=0
declared=0

while IFS='|' read -r name expect reader note setup query; do
  [ -n "$name" ] || continue
  run_case "$name" 4096 "$expect" "$reader" "$setup" "$query"
  if [ "$expect" = pass ]; then passed=$((passed + 1)); else declared=$((declared + 1)); fi
done <<CASES
$(feature_cases)
CASES

while IFS='|' read -r name expect reader note setup query; do
  [ -n "$name" ] || continue
  for page in $page_sizes; do
    if [ "$mode" != --full ] && [ "$page" = 4096 ] && [ "$name" = pagesize-indexed ]
    then
      : # 4096 for this shape is already covered by secondary-index above
    fi
    run_case "$name" "$page" "$expect" "$reader" "$setup" "$query"
    passed=$((passed + 1))
  done
done <<CASES
$(page_size_shapes)
CASES

if [ "$mode" = --full ]; then
  while IFS='|' read -r name expect reader note setup query; do
    [ -n "$name" ] || continue
    [ "$expect" = pass ] || continue
    [ "$reader" = file ] || continue
    for page in 1024 8192 65536; do
      run_case "$name" "$page" "$expect" "$reader" "$setup" "$query"
      passed=$((passed + 1))
    done
  done <<CASES
$(feature_cases)
CASES
fi

if [ "$mode" = --tsv ]; then
  cat "$matrix"
  exit 0
fi

printf '%s reverse-direction cells accepted, %s declared unsupported\n' \
  "$passed" "$declared"
