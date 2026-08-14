#!/bin/sh
# Deterministic device-level power-loss injection for rollback-journal commits.
#
# Unlike SIGKILL, the powerloss VFS never sends unsynced writes to the host
# filesystem until a modeled crash chooses them. At the first main-file xSync,
# it persists an arbitrary seeded subset of all pending cross-file writes and
# exits. A correct journal-first protocol must always reopen as old or new.
#
# Usage: scripts/run-powerloss-injection.sh [sqlite3-binary] [rounds]
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
binary=${1:-/usr/bin/sqlite3}
rounds=${2:-20}
compiler=${CC:-cc}
work=$(mktemp -d)
trap 'rm -r -- "$work"' EXIT HUP INT TERM

extension=$work/powerloss-vfs.so
if [ -n "${SQLITE_INCLUDE_DIR:-}" ]; then
  "$compiler" -O2 -fPIC -shared -I"$SQLITE_INCLUDE_DIR" \
    native/powerloss-vfs.c -o "$extension"
else
  "$compiler" -O2 -fPIC -shared native/powerloss-vfs.c -o "$extension"
fi

old_or_new=0
partial=0
corrupt=0
not_crashed=0

for round in $(seq 1 "$rounds"); do
  db=$work/powerloss-$round.db
  "$binary" -batch "$db" "
    PRAGMA journal_mode=DELETE;
    CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL);
    WITH RECURSIVE c(i) AS (
      SELECT 1 UNION ALL SELECT i+1 FROM c WHERE i<2000
    ) INSERT INTO t SELECT i,printf('old-%05d',i) FROM c;
  " >/dev/null

  set +e
  "$binary" -batch <<EOF >/dev/null 2>&1
.load $extension
SELECT powerloss_config(1,'$db',$round);
ATTACH 'file:$db?vfs=powerloss' AS p;
PRAGMA p.journal_mode=DELETE;
PRAGMA p.cache_size=10;
BEGIN;
UPDATE p.t SET v=printf('new-%05d',id);
COMMIT;
EOF
  child_status=$?
  set -e

  if [ "$child_status" -ne 99 ]; then
    not_crashed=$((not_crashed + 1))
    printf 'NO-CRASH round %s: child status %s\n' "$round" "$child_status"
    continue
  fi

  check=$("$binary" -batch -noheader "$db" \
    "PRAGMA integrity_check;" 2>&1 | sed -n '1p' || true)
  stats=$("$binary" -batch -noheader "$db" \
    "SELECT count(*),sum(v LIKE 'old-%'),sum(v LIKE 'new-%') FROM t;" \
    2>/dev/null | sed -n '1p' || true)
  if [ "$check" != ok ]; then
    corrupt=$((corrupt + 1))
    printf 'CORRUPT round %s: %s\n' "$round" "$check"
  elif [ "$stats" = '2000|2000|0' ] || [ "$stats" = '2000|0|2000' ]; then
    old_or_new=$((old_or_new + 1))
  else
    partial=$((partial + 1))
    printf 'PARTIAL round %s: %s\n' "$round" "$stats"
  fi
done

printf '\npower-loss injection: %s rounds against %s\n' "$rounds" "$binary"
printf '  recovered old-or-new : %s\n' "$old_or_new"
printf '  partial (torn commit): %s\n' "$partial"
printf '  corrupt              : %s\n' "$corrupt"
printf '  crash point not hit  : %s\n' "$not_crashed"

if [ "$partial" -gt 0 ] || [ "$corrupt" -gt 0 ] || \
   [ "$not_crashed" -gt 0 ]; then
  exit 1
fi
