#!/bin/sh
# Assert that the verified core is actually what runs.
#
# The failure this guards against is real and has happened twice in this repo:
#
#   * P2 (index lookup = full scan) was proved only for Engine.evalIndex, which
#     was reachable from the old production SQL-FILE/--server entry points and
#     NOT from --verified-file. The proof was true and irrelevant to the
#     shipped path. That protocol now lives in a separate test-only binary.
#   * ProofAxioms named a deleted theorem and was not in the build graph, so the
#     proof contract silently rotted.
#
# A proof about code that does not run is worth nothing, so this is checked
# rather than remembered.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
status=0
lake_command=${LAKE_BIN:-lake}
sqlite_bin=${SQLITE3_BIN:-/usr/bin/sqlite3}

fail() { printf 'live-path check FAILED: %s\n' "$1" >&2; status=1; }
ok()   { printf 'ok - %s\n' "$1"; }

python3 scripts/check_module_boundaries.py
audit_sources=$(mktemp -d)
python3 scripts/lean_sources.py --materialize "$audit_sources"
trap 'rm -rf "$audit_sources"' EXIT

. "$root/scripts/live-path/01-connection-and-sql.sh"
. "$root/scripts/live-path/02-read-write-refinement.sh"
. "$root/scripts/live-path/03-physical-storage.sh"
. "$root/scripts/live-path/04-proof-and-byte-compatibility.sh"
. "$root/scripts/live-path/05-scalar-and-catalog.sh"
. "$root/scripts/live-path/06-schema-and-derived-sql.sh"
. "$root/scripts/live-path/07-catalog-and-constraints.sh"

. "$root/scripts/live-path/08-utf16-provenance.sh"

. "$root/scripts/live-path/09-typed-predicates.sh"

. "$root/scripts/live-path/10-trigger-catalog.sh"

. "$root/scripts/live-path/11-trigger-execution.sh"

exit "$status"
