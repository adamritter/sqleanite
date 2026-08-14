#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
sqlite_source=${SQLITE_SOURCE_DIR:-}

if [ -z "$sqlite_source" ] || [ ! -d "$sqlite_source/.git" ] || \
   [ ! -f "$sqlite_source/src/sqliteInt.h" ]; then
  printf '%s\n' \
    'set SQLITE_SOURCE_DIR to a clean SQLite source checkout' >&2
  exit 2
fi
sqlite_source=$(CDPATH= cd -- "$sqlite_source" && pwd)

if ! git -C "$sqlite_source" diff --quiet || \
   ! git -C "$sqlite_source" diff --cached --quiet; then
  printf '%s\n' 'C mutation pilot requires a clean SQLite worktree' >&2
  exit 2
fi

registry=$root/mutations/c-registry.tsv
results=$root/mutations/c-results.tsv
logs=$root/mutations/c-logs
sqlite_reference=${SQLITE3_BIN:-/usr/bin/sqlite3}
mkdir -p "$logs"
temporary=$(mktemp)
run_tmp=$(mktemp -d)
active_patch=

# Restore exactly the files a patch names. Reversing with `patch -R` matches
# context with fuzz and can land on the wrong block, silently leaving a defect
# in the tree; that happened in the Lean harness. `git checkout --` is exact.
restore_patch() {
  files=$(sed -n 's|^+++ b/||p' "$1")
  if [ -n "$files" ]; then
    # shellcheck disable=SC2086
    git -C "$sqlite_source" checkout -- $files
  fi
}

cleanup() {
  if [ -n "$active_patch" ]; then
    restore_patch "$active_patch" || true
  fi
  rm -f "$temporary"
  rm -r -- "$run_tmp"
}
trap cleanup EXIT HUP INT TERM

printf 'id\tproperty\tcompile_status\twitness_status\telapsed_ms\tqueries_before_detection\tlog\n' > "$temporary"
first_row=true
while IFS="$(printf '\t')" read -r id property patch_name witness_name bug_class; do
  if [ "$first_row" = true ]; then
    first_row=false
    continue
  fi
  patch_path=$root/mutations/$patch_name
  witness_path=$root/mutations/$witness_name
  log_path=$logs/$id.log
  reference_out=$run_tmp/$id.reference
  mutant_out=$run_tmp/$id.mutant

  # Run against a real file, then REOPEN it. ":memory:" has no pager, journal
  # or WAL, so recovery and WAL mutations were never executed at all and could
  # only ever be recorded as "missed".
  ref_db=$run_tmp/$id.ref.db
  rm -f "$ref_db" "$ref_db-journal" "$ref_db-wal"
  "$sqlite_reference" -batch -noheader "$ref_db" < "$witness_path" > "$reference_out"
  printf 'PRAGMA integrity_check;\n' | "$sqlite_reference" -batch -noheader "$ref_db" \
    >> "$reference_out" 2>&1 || true
  ls -l "$ref_db" | awk '{print "dbsize", $5}' >> "$reference_out"
  patch --dry-run --silent -d "$sqlite_source" -p1 < "$patch_path"
  patch --silent --batch --forward --no-backup-if-mismatch \
    -d "$sqlite_source" -p1 < "$patch_path"
  active_patch=$patch_path
  start=$(date +%s%N)
  if make -C "$sqlite_source" -f Makefile.linux-generic -j2 sqlite3 SHELL_OPT= \
      LDFLAGS.readline= > "$log_path" 2>&1; then
    compile_status=passed
    mut_db=$run_tmp/$id.mut.db
    rm -f "$mut_db" "$mut_db-journal" "$mut_db-wal"
    "$sqlite_source/sqlite3" -batch -noheader "$mut_db" < "$witness_path" \
      > "$mutant_out" 2>> "$log_path" || true
    printf 'PRAGMA integrity_check;\n' | "$sqlite_source/sqlite3" -batch -noheader "$mut_db" \
      >> "$mutant_out" 2>&1 || true
    ls -l "$mut_db" 2>/dev/null | awk '{print "dbsize", $5}' >> "$mutant_out"
    if cmp -s "$reference_out" "$mutant_out"; then
      witness_status=missed
      queries=1
    else
      witness_status=detected
      queries=1
    fi
  else
    compile_status=failed
    witness_status=not-run
    queries=0
  fi
  finish=$(date +%s%N)
  elapsed_ms=$(((finish - start) / 1000000))
  restore_patch "$patch_path"
  active_patch=
  # Only the patched sources must be back at the index. The build regenerates
  # tracked artifacts (sqlite3.c, tsrc/, the sqlite3 binary), which is expected.
  # shellcheck disable=SC2046
  if ! git -C "$sqlite_source" diff --quiet -- \
      $(sed -n 's|^+++ b/||p' "$patch_path"); then
    printf 'C mutation %s did not restore cleanly; aborting\n' "$id" >&2
    exit 3
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$id" "$property" "$compile_status" "$witness_status" "$elapsed_ms" \
    "$queries" "$log_path" >> "$temporary"
  printf '%-24s compile=%s witness=%s %sms\n' \
    "$id" "$compile_status" "$witness_status" "$elapsed_ms"
done < "$registry"

mv "$temporary" "$results"
trap - EXIT HUP INT TERM
rm -r -- "$run_tmp"
