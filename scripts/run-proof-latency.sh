#!/bin/sh
# Proof-check and incremental rebuild latency after representative edits.
# Maintenance cost is one of the survey's explicit recommendations.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd); cd "$root"
lake_command=${LAKE_BIN:-lake}
ms(){ s=$(date +%s%N); "$@" >/dev/null 2>&1 || true; e=$(date +%s%N); echo $(( (e-s)/1000000 )); }
printf 'scenario\telapsed_ms\n'
printf 'no-op rebuild\t%s\n' "$(ms $lake_command build)"
for target in SQLeanite/CoreEngine.lean SQLeanite/CellPagination.lean SQLeanite/GrowableStorage.lean; do
  printf '\n' >> "$target"                      # whitespace-only edit
  printf 'touch %s\t%s\n' "$(basename $target)" "$(ms $lake_command build)"
  git checkout -- "$target"
done
printf 'full rebuild from clean\t%s\n' "$( $lake_command clean >/dev/null 2>&1; ms $lake_command build )"
