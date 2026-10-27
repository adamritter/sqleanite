#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

for forbidden in '\bsorry\b' '\bnative_decide\b' '^\s*axiom\b' \
    '^\s*unsafe\b' '^\s*extern\b'; do
  if rg -n "$forbidden" SQLeanite -g '*.lean'; then
    printf 'verification audit failed: forbidden pattern %s\n' "$forbidden" >&2
    exit 1
  fi
done

# `@[extern] opaque` is the correct Lean declaration form for the deliberately
# unverified host boundary. Keep that exception name- and file-specific: a new
# opaque declaration anywhere (including beside these twelve) must turn the
# audit red until the trust-boundary review explicitly admits it.
opaque_report=$(mktemp)
trap 'rm -f "$opaque_report"' EXIT
rg -n '^\s*opaque\b' SQLeanite -g '*.lean' > "$opaque_report" || true
allowed_opaque='^(SQLeanite/SyscallVFS\.lean:[0-9]+:opaque (fdatasyncPath|fsyncParentPath|preadBytes|pwriteBytes|pwritePages|verifyPages|renamePath|unlinkPath)\b|SQLeanite/ProcessLock\.lean:[0-9]+:opaque processAlive\b|SQLeanite/WALVFS\.lean:[0-9]+:opaque (tryRangeLock|releaseRangeLock|nativeBigEndian)\b)'
if rg -v "$allowed_opaque" "$opaque_report"; then
  printf 'verification audit failed: opaque declaration outside the explicit host allowlist\n' >&2
  exit 1
fi
opaque_count=$(wc -l < "$opaque_report" | tr -d ' ')
if [ "$opaque_count" -ne 12 ]; then
  printf 'verification audit failed: expected 12 allowlisted host bindings, found %s\n' \
    "$opaque_count" >&2
  cat "$opaque_report" >&2
  exit 1
fi
require_extern() {
  file=$1; binding=$2; symbol=$3
  if ! rg -U -q "@\\[extern \"$symbol\"\\]\\nopaque $binding\\b" "$file"; then
    printf 'verification audit failed: allowlisted binding %s lacks its reviewed extern %s\n' \
      "$binding" "$symbol" >&2
    exit 1
  fi
}
require_extern SQLeanite/SyscallVFS.lean fdatasyncPath sqleanite_fdatasync_path
require_extern SQLeanite/SyscallVFS.lean fsyncParentPath sqleanite_fsync_parent_path
require_extern SQLeanite/SyscallVFS.lean preadBytes sqleanite_pread_bytes
require_extern SQLeanite/SyscallVFS.lean pwriteBytes sqleanite_pwrite_bytes
require_extern SQLeanite/SyscallVFS.lean pwritePages sqleanite_pwrite_pages
require_extern SQLeanite/SyscallVFS.lean verifyPages sqleanite_verify_pages
require_extern SQLeanite/SyscallVFS.lean renamePath sqleanite_rename_path
require_extern SQLeanite/SyscallVFS.lean unlinkPath sqleanite_unlink_path
require_extern SQLeanite/ProcessLock.lean processAlive sqleanite_process_alive
require_extern SQLeanite/WALVFS.lean tryRangeLock sqleanite_try_range_lock
require_extern SQLeanite/WALVFS.lean releaseRangeLock sqleanite_release_range_lock
require_extern SQLeanite/WALVFS.lean nativeBigEndian sqleanite_native_big_endian
printf 'allowlisted opaque host bindings: %s\n' "$opaque_count"

partial_pattern='^[[:space:]]*(private[[:space:]]+)?partial[[:space:]]+def\b'
library_count=$(rg -n "$partial_pattern" SQLeanite -g '*.lean' | wc -l | tr -d ' ')
process_count=$(rg -n "$partial_pattern" Main.lean | wc -l | tr -d ' ')
printf 'library partial definitions: %s\n' "$library_count"
printf 'process partial definitions: %s\n' "$process_count"
rg -n "$partial_pattern" SQLeanite Main.lean -g '*.lean' || true
