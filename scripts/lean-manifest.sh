#!/bin/sh
# Emit a machine-readable theorem and trust-boundary manifest as JSON.
#
# Everything here is derived from the tree, never hand-maintained, so it cannot
# drift from what actually builds. `scripts/lean-verification-audit.sh` enforces
# the hygiene fields; this records them in a form other tools can consume.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
lake_command=${LAKE_BIN:-lake}
axioms=$(mktemp)
normalized=$(mktemp)
trap 'rm -f "$axioms" "$normalized"' EXIT

"$lake_command" env lean SQLeanite/ProofAxioms.lean > "$axioms" 2>&1

# Lean wraps long axiom lists over several lines. Normalize each report to one
# line before counting or converting it to JSON.
awk '
  /^\047.* depends on axioms: \[/ {
    report = $0
    while (report !~ /\]$/ && (getline nextLine) > 0) report = report " " nextLine
    print report
    next
  }
  /^\047.* does not depend on any axioms$/ { print }
' "$axioms" > "$normalized"

# A checked-in file can never contain its own Git commit hash: committing the
# generated hash changes that hash again. Use a digest of the actual proof and
# executable sources instead, so the manifest remains self-verifying.
source_digest=$(
  {
    find SQLeanite -type f -name '*.lean' -print
    printf '%s\n' Main.lean Tests.lean lean-toolchain lakefile.lean
  } | LC_ALL=C sort | xargs sha256sum | sha256sum | awk '{print $1}'
)
theorems=$(grep -rE '^[[:space:]]*(theorem|lemma)\b' --include='*.lean' \
  SQLeanite Tests.lean Main.lean 2>/dev/null | wc -l | tr -d ' ')
modules=$(ls SQLeanite/*.lean | wc -l | tr -d ' ')
lines=$(cat SQLeanite/*.lean | wc -l | tr -d ' ')
listed=$(grep -c 'depends on axioms\|does not depend' "$normalized" || true)
expected=$(grep -c '^#print axioms ' SQLeanite/ProofAxioms.lean)
if [ "$listed" -eq 0 ] || [ "$listed" -ne "$expected" ]; then
  printf 'manifest generation failed: expected %s axiom reports, found %s\n' \
    "$expected" "$listed" >&2
  exit 1
fi
sorry_count=$(grep -c 'sorryAx' "$axioms" || true)
errors=$(grep -c '^.*error' "$axioms" || true)

printf '{\n'
printf '  "source_digest": "%s",\n' "$source_digest"
printf '  "toolchain": "%s",\n' "$(cat lean-toolchain)"
printf '  "dependencies": [],\n'
printf '  "counts": {\n'
printf '    "theorems": %s,\n' "$theorems"
printf '    "modules": %s,\n' "$modules"
printf '    "library_lines": %s,\n' "$lines"
printf '    "headline_theorems": %s\n' "$listed"
printf '  },\n'
printf '  "hygiene": {\n'
for pattern in sorry native_decide axiom opaque unsafe extern; do
  n=$(grep -rEc "^[[:space:]]*${pattern}\b|\b${pattern}\b" --include='*.lean' SQLeanite 2>/dev/null \
      | awk -F: '{s+=$2} END {print s+0}')
  case $pattern in
    sorry|native_decide) n=$(grep -rE "\b${pattern}\b" --include='*.lean' SQLeanite | wc -l | tr -d ' ') ;;
    *) n=$(grep -rE "^[[:space:]]*${pattern}\b" --include='*.lean' SQLeanite | wc -l | tr -d ' ') ;;
  esac
  printf '    "%s": %s,\n' "$pattern" "$n"
done
printf '    "partial_def": %s,\n' \
  "$(grep -rE '^[[:space:]]*(private[[:space:]]+)?partial[[:space:]]+def\b' --include='*.lean' SQLeanite | wc -l | tr -d ' ')"
printf '    "sorryAx_in_axiom_report": %s,\n' "$sorry_count"
printf '    "axiom_report_errors": %s\n' "$errors"
printf '  },\n'
printf '  "trusted": [\n'
printf '    "Lean 4 kernel",\n'
printf '    "Lean elaborator, compiler, runtime and platform C toolchain",\n'
printf '    "Lean primitive Int/String/Array/Float operations",\n'
printf '    "IO.FS file operations, fsync, rename and directory locks",\n'
printf '    "Std.Mutex and task scheduling for the serialized connection",\n'
printf '    "generated-image provenance stamp (not cryptographic authentication)",\n'
printf '    "the operating system and filesystem page-write behaviour"\n'
printf '  ],\n'
printf '  "headline_theorems": [\n'
first=1
grep -E "depends on axioms|does not depend" "$normalized" | while IFS= read -r line; do
  name=$(printf '%s' "$line" | sed "s/^'//; s/'.*//")
  if printf '%s' "$line" | grep -q 'does not depend'; then
    ax='[]'
  else
    ax=$(printf '%s' "$line" | sed 's/.*\[//; s/\].*//' \
      | tr -d ' ' | awk -F, '{out="";for(i=1;i<=NF;i++){out=out (i>1?", ":"") "\"" $i "\""} print out}')
    ax="[$ax]"
  fi
  if [ "$first" = 1 ]; then first=0; else printf ',\n'; fi
  printf '    {"name": "%s", "axioms": %s}' "$name" "$ax"
done
printf '\n  ]\n}\n'
