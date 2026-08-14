#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

if ! git diff --quiet || ! git diff --cached --quiet; then
  printf '%s\n' 'mutation harness requires a clean tracked worktree' >&2
  exit 2
fi

registry=mutations/registry.tsv
results=mutations/results.tsv
logs=mutations/logs
lake_command=${LAKE_BIN:-lake}
mkdir -p "$logs"
temporary=$(mktemp)

# Files a patch touches, taken from its `+++ b/...` headers.
patched_files() {
  sed -n 's|^+++ b/||p' "$1"
}

# Restore exactly the files a patch touches, from the index.
#
# Reversing with `patch -R` is UNSAFE here: GNU patch matches context with fuzz
# and offset, so when a mutation makes two blocks textually identical it can
# reverse the wrong one and silently leave a semantic defect in the tree. That
# is what happened with p4-commit-without-delete-sync, whose target differs
# from the neighbouring `journalDeleted` case only by a trailing `.syncJournal`:
# the reversal re-added `.syncJournal` to `journalDeleted` instead of to
# `committed`. `git checkout --` is exact and cannot misapply.
restore_patch() {
  files=$(patched_files "$1")
  if [ -n "$files" ]; then
    # shellcheck disable=SC2086
    git checkout -- $files
  fi
}

active_patch=

cleanup() {
  if [ -n "$active_patch" ]; then
    restore_patch "$active_patch" || true
  fi
  rm -f "$temporary"
}
trap cleanup EXIT HUP INT TERM

printf 'id\tproperty\tbuild_status\telapsed_ms\tlog\n' > "$temporary"
first_row=true
while IFS="$(printf '\t')" read -r id property target patch defect witness; do
  if [ "$first_row" = true ]; then
    first_row=false
    continue
  fi
  patch_path="mutations/$patch"
  log_path="$logs/$id.log"
  patch --dry-run --silent -p1 < "$patch_path"
  patch --silent --batch --forward --no-backup-if-mismatch -p1 < "$patch_path"
  active_patch=$patch_path
  start=$(date +%s%N)
  if "$lake_command" build > "$log_path" 2>&1; then
    status=passed
  else
    status=failed
  fi
  finish=$(date +%s%N)
  elapsed_ms=$(((finish - start) / 1000000))
  restore_patch "$patch_path"
  active_patch=

  # Fail loudly rather than continue against a corrupted tree. Only mutations/
  # may differ here; every source file must be back at the index.
  if ! git diff --quiet -- ':!mutations'; then
    printf 'mutation %s did not restore cleanly; aborting\n' "$id" >&2
    git diff --stat -- ':!mutations' >&2
    exit 3
  fi

  printf '%s\t%s\t%s\t%s\t%s\n' "$id" "$property" "$status" "$elapsed_ms" "$log_path" >> "$temporary"
  printf '%-34s %s %sms\n' "$id" "$status" "$elapsed_ms"
done < "$registry"

mv "$temporary" "$results"
trap - EXIT HUP INT TERM

if ! git diff --quiet -- ':!mutations'; then
  printf 'mutation run left source modifications; investigate before trusting results\n' >&2
  exit 3
fi
