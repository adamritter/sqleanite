#!/bin/sh
# Crash fault injection against the live C SQLite executable.
#
# Kills the writer partway through a transaction, reopens the database, and
# checks that recovery produced a consistent state. This is the only way to
# observe durability-ordering faults: every completing run of such a mutant is
# correct, so an ordinary witness query can never distinguish it.
#
# Usage: scripts/run-crash-injection.sh [binary] [rounds]
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
binary=${1:-/usr/bin/sqlite3}
rounds=${2:-40}
work=$(mktemp -d)
trap 'rm -r -- "$work"' EXIT

# A writer that does enough page work for a kill to land mid-transaction.
cat > "$work/write.sql" <<'SQL'
PRAGMA journal_mode=DELETE;
CREATE TABLE IF NOT EXISTS t(a INTEGER PRIMARY KEY, b);
BEGIN;
WITH RECURSIVE c(i) AS (SELECT 1 UNION ALL SELECT i+1 FROM c WHERE i<4000)
  INSERT INTO t SELECT i,'payload-row-'||i FROM c;
COMMIT;
SQL

survived=0
corrupt=0
partial=0
for round in $(seq 1 "$rounds"); do
  db=$work/crash-$round.db
  rm -f "$db" "$db-journal" "$db-wal"
  # Seed a committed baseline so recovery has a defined old state.
  "$binary" -batch "$db" "CREATE TABLE t(a INTEGER PRIMARY KEY, b); INSERT INTO t VALUES(0,'seed');" \
    >/dev/null 2>&1 || true

  # Start the writer and kill it after a randomised sub-second delay so the
  # kill lands at many different points in the commit sequence.
  "$binary" -batch "$db" < "$work/write.sql" >/dev/null 2>&1 &
  writer=$!
  # 3..40 ms, varied per round without needing $RANDOM
  delay=$(awk -v r="$round" 'BEGIN{printf "0.%03d", (r*7919)%38+3}')
  sleep "$delay"
  kill -9 "$writer" 2>/dev/null || true
  wait "$writer" 2>/dev/null || true

  # Reopen and judge the recovered state.
  check=$("$binary" -batch -noheader "$db" "PRAGMA integrity_check;" 2>&1 | head -1)
  count=$("$binary" -batch -noheader "$db" "SELECT count(*) FROM t;" 2>&1 | head -1)
  case "$check" in
    ok)
      # Old-or-new: either only the seed row, or the whole batch.
      if [ "$count" = "1" ] || [ "$count" = "4001" ]; then
        survived=$((survived + 1))
      else
        partial=$((partial + 1))
        printf 'PARTIAL round %s: integrity ok but %s rows (expected 1 or 4001)\n' "$round" "$count"
      fi
      ;;
    *)
      corrupt=$((corrupt + 1))
      printf 'CORRUPT round %s: %s\n' "$round" "$check"
      ;;
  esac
done

printf '\ncrash injection: %s rounds against %s\n' "$rounds" "$binary"
printf '  recovered old-or-new : %s\n' "$survived"
printf '  partial (torn commit): %s\n' "$partial"
printf '  corrupt              : %s\n' "$corrupt"

# A partial or corrupt recovery is exactly the failure the P4 theorems forbid.
if [ "$corrupt" -gt 0 ] || [ "$partial" -gt 0 ]; then
  exit 1
fi
