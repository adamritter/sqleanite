#!/bin/sh
# The executable boundary: where the proofs stop, stated mechanically.
#
# The claim this project makes is a *verified core with a documented executable
# boundary*, not a verified binary. That is only honest if the boundary is written
# down and cannot quietly move, which is what this script is for: every entry
# point `Main.lean` calls is classified, the classification is checked against the
# audited theorem set, and new unclassified shipped code fails the audit instead
# of arriving silently.
#
# Three classifications, and the difference between them matters:
#
#   covered   a named audited theorem is about this function's result;
#   seam      the *pure* computation underneath is proved and audited, and the IO
#             wrapper that feeds it the file's pages is not. The composition down
#             to `Core.execute` is asserted by `scripts/live-path-check.sh`, not
#             proved;
#   boundary  no theorem covers it at all.
#
# Modes:
#   --markdown   emit docs/BOUNDARY.md
#   --json       emit the classification for scripts/lean-manifest.sh
#   --check      verify the classification is complete, current and honest
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
audit=SQLeanite/ProofAxioms.lean
target=docs/BOUNDARY.md

entries=$(mktemp)
scratch=$(mktemp)
observed=$(mktemp)
trap 'rm -f "$entries" "$scratch" "$observed"' EXIT

# entry|class|evidence (audited theorem, or "-" for boundary)|note
cat > "$entries" <<'ROWS'
CoreFileEngine.execute|seam|Core.execute_insert_exact|Statement effects and their composition to SQLite bytes are proved; the IO wrapper that opens the file, dispatches statements and commits is not.
CoreFileEngine.executeObserved|seam|CoreSQL.observeJoinedSelect_refines|Joined observations erase to the ordinary Core SELECT result; output callbacks, connection cache handling and file IO are not proved. Other statements retain the existing execute path.
CoreFileEngine.reopen|seam|CorePageLoad.open?_represents|Validating open is proved to reconstruct the represented database; the file reading around it is IO.
CoreFileEngine.create|seam|CoreFileAdapter.commit_crash_atomic|Image creation commits through the proved rollback plan; directory and handle handling is IO.
CoreFileEngine.snapshot|seam|CorePageLoad.open?_decode|Returns the validated open state; no theorem about the IO handle lifetime.
CoreFileEngine.statementWrites|covered|CoreFileEngine.requiresPersistence_write_in_transaction|Pure classification of statements, with its persistence theorem.
CoreWALFileEngine.execute|boundary|-|Shared WAL execution uses the pure Lean codecs; lock lifetime, index publication and the composition with SQL execution have no end-to-end refinement theorem.
CoreWALFileEngine.executeObserved|boundary|-|Copies a protected snapshot or holds a cross-engine writer session. The live shared-index protocol and output callbacks are tested IO boundaries.
CoreWALFileEngine.checkpoint|boundary|-|Backfills exact committed pages under writer/checkpoint/reader locks without truncating the main file or replacing mapped WAL/SHM inodes. No OS crash-refinement theorem.
CoreWALFileEngine.needsWriter|covered|CoreWALFileEngine.needsWriter_false_member|Pure predicate deciding whether a statement list needs the writer lock.
CoreWALFileAdapter.create|boundary|-|Initial WAL-mode image creation and header updates under an exclusive database lock; the file operation is not proved.
SQLite.WALShared.withSession|boundary|-|Linux OFD locks coordinate with SQLite POSIX locks. The DMS initialization handoff, snapshot capture and resource cleanup are executable obligations.
SQLite.WALShared.Session.append|boundary|-|Appends durable frames before mapping/header publication. All eight SQLite page sizes retain their geometry and committed WAL prefix; CoreSizedPageCodec has component properties but no complete image-refinement theorem. Linux coherent page-cache writes are trusted.
ProcessLock.withLock|seam|ProcessLock.run_successfulTrace|The lock *protocol* is proved, including that overlapping critical sections are rejected; that a directory on a real filesystem implements it is not.
CoreLazyFileEngine.collectReads|covered|CoreLazyFileEngine.collectReads_scalar_miss|Rejects a SELECT outside the cold-read shape before accumulating it; this is a necessary-condition theorem, not a query execution refinement.
CoreLazyFileEngine.parseReadChunks|covered|CoreLazyFileEngine.parseReadChunks_parse_error|Certified chunk parse errors return an optimizer miss. The separately audited shape-miss equation stops unsupported batches. Neither equation proves physical reads or whole-script equivalence.
CoreLazyFileEngine.execute?|boundary|-|The cold page-directed read fast path. CoreDecode contains proved reference traversals; the generated-image byte cursor and its IO/cache composition do not yet have refinement theorems.
CoreFileAdapter.lookupPrimaryRowDecision|boundary|-|Returns a plain IndexLookup, not the proof-carrying CertifiedCandidates the warm path uses. A hit self-checks rowid equality and row well-formedness; a miss is admitted only under the generated-image stamp.
CoreFileAdapter.lookupGeneratedPrimaryRowWith|boundary|-|Generated-image primary lookup through the shared byte cursor. Checks schema, rowid and row well-formedness; cache and geometry are scoped to one locked immutable read batch. No byte-cursor refinement theorem yet.
Runtime.ReadPager.Pager.get|boundary|-|Bounded raw-page cache with range and short-read checks. Snapshot lifetime is a caller obligation, tested but not proved.
Runtime.TableCursor.Cursor.seek|boundary|-|Uses checked page views and proved binary lower-bound search. Physical byte decoding, tree traversal and cache lifetime still lack a complete CoreDecode refinement.
Runtime.TablePage.View.lowerBound|covered|Runtime.TablePage.View.lowerBound_eq_linear|Binary search equals linear first-match search. Its ordering premise is established by an executed adjacency check and carried in the page view.
Runtime.Record.encodedSize|covered|Runtime.Record.encodedSize_eq_length|Computes the canonical encoded length from serial metadata without re-encoding payload bytes; exact for every physical record.
Runtime.Record.decodeRowCell|covered|Runtime.Record.decodeRowCell_eq_reference|Effectful equality to the existing CoreDecode cell reader, for every input and page source, including failure and overflow paths.
Runtime.Record.readRowWithSource|seam|Runtime.Record.readRowWithSource_eq_reference|Shared cell input equals the byte-list reference suffix; decoding and validation equal CoreDecode. Physical pager fidelity is still the caller's boundary.
CoreFileAdapter.lookupGeneratedPrimaryRange|boundary|-|As above, for separator-directed ranges.
CoreFileAdapter.lookupGeneratedIndexCandidatesWith|boundary|-|As above, for secondary-index candidates; every resolved rowid and value link is locally validated.
CoreFileAdapter.lookupGeneratedOrderedPrefix|boundary|-|As above, for the multi-leaf ORDER BY/LIMIT cursor.
CoreFileAdapter.readFileGeometry|boundary|-|Reads the header and catalog to decide whether a fast path applies.
CoreLazyWrite.executeInsert?|boundary|-|Page-local INSERT. The *plan* it computes is proved to denote the ordered insert (CoreLazyWrite.insertPlan_refines), but its WellFormedTree premises are unchecked at runtime, so it is reachable only under SQLEANITE_PAGE_LOCAL_WRITES=1 and is not part of the default configuration.
Main.lean|boundary|-|Argument parsing, stdin/stdout rendering, file-facing shell. Disclosed in docs/TRUST.md and never counted as verified.
ROWS

# What Main.lean actually reaches, extracted rather than remembered. If a new
# engine or adapter call appears here and is not classified above, --check fails.
observe_shipped_surface() {
  grep -oE '(CoreFileEngine|CoreLazyFileEngine|CoreWALFileEngine|CoreWALFileAdapter|CoreLazyWrite|ProcessLock|WALVFS|SQLite\.WALShared)\.[A-Za-z_0-9?]+' \
    Main.lean | sort -u > "$observed"
}

verify() {
  status=0
  # 1. Every `covered`/`seam` entry must name a theorem that is actually audited.
  while IFS='|' read -r entry class evidence note; do
    [ -n "$entry" ] || continue
    case $class in
      covered|seam)
        if ! grep -q "SQLeanite\.${evidence}\$" "$audit"; then
          printf 'executable-boundary: %s cites unaudited evidence %s\n' \
            "$entry" "$evidence" >&2
          status=1
        fi
        ;;
      boundary)
        if [ "$evidence" != "-" ]; then
          printf 'executable-boundary: %s is boundary-listed but cites %s\n' \
            "$entry" "$evidence" >&2
          status=1
        fi
        ;;
      *)
        printf 'executable-boundary: %s has unknown class %s\n' "$entry" "$class" >&2
        status=1
        ;;
    esac
    if [ -z "$note" ]; then
      printf 'executable-boundary: %s has no stated reason\n' "$entry" >&2
      status=1
    fi
  done < "$entries"

  # 2. Anti-drift: everything Main.lean reaches must be classified.
  observe_shipped_surface
  while read -r reached; do
    [ -n "$reached" ] || continue
    # Types and structures referenced for their fields are not entry points.
    case $reached in
      *.Paths|*.Config|*.Connection|*.insertPlan_refines) continue ;;
    esac
    if ! grep -q "^${reached}|" "$entries"; then
      printf 'executable-boundary: %s is shipped but not classified\n' "$reached" >&2
      status=1
    fi
  done < "$observed"

  # 3. Pure admission helpers now have three audited miss equations. Pin the
  #    exact set so additions/deletions require a classification review. The
  #    file-facing execute? still has no IO/page-cursor refinement theorem.
  expected_lazy=$(printf '%s\n' collectReads_scalar_miss \
    parseReadChunks_parse_error parseReadChunks_shape_miss | sort)
  lazy_theorems=$(sed -n 's/^theorem \([^ (]*\).*/\1/p; s/^private theorem \([^ (]*\).*/\1/p' \
    SQLeanite/CoreLazyFileEngine.lean | sort)
  lazy_audited=$(sed -n 's/^#print axioms SQLeanite.CoreLazyFileEngine\.//p' "$audit" | sort)
  if [ "$lazy_theorems" != "$expected_lazy" ] || [ "$lazy_audited" != "$expected_lazy" ]; then
    printf 'executable-boundary: CoreLazyFileEngine theorem/audit set changed; reclassify it\n' >&2
    status=1
  fi
  return "$status"
}

emit_markdown() {
  covered=$(awk -F'|' '$2 == "covered"' "$entries" | wc -l | tr -d ' ')
  seam=$(awk -F'|' '$2 == "seam"' "$entries" | wc -l | tr -d ' ')
  boundary=$(awk -F'|' '$2 == "boundary"' "$entries" | wc -l | tr -d ' ')
  cat <<HEAD
# The executable boundary

Generated by \`scripts/executable-boundary.sh --markdown\`. Do not edit by hand.

The claim is a **verified core with a documented executable boundary**, not a
verified binary. This document is the boundary. Of the shipped entry points
\`Main.lean\` reaches: **$covered covered**, **$seam seam**, **$boundary boundary**.

- **covered** — a named audited theorem is about this function's result.
- **seam** — the pure computation underneath is proved and audited; the IO
  wrapper that feeds it the file's pages is not. The composition down to
  \`Core.execute\` is *asserted by* \`scripts/live-path-check.sh\`, not proved.
- **boundary** — no theorem covers it.

## The pure/IO seam, stated precisely

The honest form of this is stronger than "the fast path is unproved", and weaker
than "the fast path is verified". Both halves matter:

> The reference CoreDecode page traversals are proved exact against the decoded
> abstraction and against the encoder —
> \`lookupIndexRangeFrom_refines_full_decode\`,
> \`lookupTableRangeFrom_decodeAbstract_exact\`,
> \`lookupIndexValueFrom_certified_exact\`, and the promoted-key index
> refinement. The optimizer is proved preserving (\`optimize_eval\`). What is
> **not** covered by a theorem is the IO wrapper that supplies those functions
> with the file's pages, so the composition down to \`Core.execute\` is asserted
> by the live-path audit rather than proved.
> \`CoreFileAdapter.byteArrayPageSource_eq_storageImage\` is the one place this
> bridge exists, for the pure source; \`preadPageSource\` and
> \`filePageSourceFor\` have no counterpart.

The generated-image primary and secondary row-resolution paths now share
\`Runtime.ReadPager\`, \`Runtime.TableCursor\` and \`Runtime.Record\`.
Their binary lower-bound search now has a linear-search equivalence theorem
and a present-key theorem, using the page view's checked ordering certificate.
The record-size computation is proved equal to canonical re-encoding length;
the optimized record reader is effectfully equal to CoreDecode, including
malformed input and overflow reads. Shared cell inputs carry their reference
suffix equality. These seven new audited theorems do not prove physical page
decoding, full tree routing, cache fidelity or lock lifetime. Those remain
explicit obligations; runtime tests and wiring checks do not discharge them.

### Mitigations, which are real and are not proofs

- a cold point-lookup hit self-checks \`row.rowid = rowid\` and
  \`row.WellFormed schema\` before returning;
- index lookups locally validate every resolved rowid and value link;
- a *miss* is admitted only under the generated-image provenance stamp, which
  \`docs/TRUST.md\` discloses is not a cryptographic MAC;
- \`scripts/live-path-check.sh\` pins that these shapes are the ones the executor
  actually takes.

None of these is a substitute for the missing lemma. The upgrade path is a
general "IO page source faithfully reads the file" lemma mirroring
\`byteArrayPageSource_eq_storageImage\`, plus refinement of the byte cursor
and record view to the reference traversals, before moving
\`CoreLazyFileEngine.execute?\` from boundary to seam.

## Classification

| entry point | class | evidence | why |
|---|---|---|---|
HEAD
  while IFS='|' read -r entry class evidence note; do
    [ -n "$entry" ] || continue
    if [ "$evidence" = "-" ]; then shown="—"; else shown="\`$evidence\`"; fi
    printf '| `%s` | %s | %s | %s |\n' "$entry" "$class" "$shown" "$note"
  done < "$entries"
  cat <<'TAIL'

## Anti-drift

`scripts/live-path-check.sh` runs `--check`, which fails if any of these hold:

1. a `covered` or `seam` entry cites a theorem that is not in
   `SQLeanite/ProofAxioms.lean`;
2. `Main.lean` reaches an engine or adapter entry point that is not classified
   here — so new unproved shipped code fails the audit instead of arriving
   silently;
3. the exact three `CoreLazyFileEngine` admission-helper theorems or their
   audit entries change. The classification distinguishes these miss equations
   from the unproved file-facing `execute?` composition and requires review
   for both added and removed theorems.

## Also in the executable TCB, and disclosed elsewhere

`docs/TRUST.md` is the authority for the rest: the Lean compiler and runtime, the
twelve opaque host bindings, `Std.Mutex` and task scheduling, the generated-image
stamp, result rendering, and the operating system and device behaviour named by
`SyscallVFS.Contract`. This document covers only the *shipped entry points* and
where their proofs stop.
TAIL
}

emit_json() {
  printf '  "executable_boundary": [\n'
  first=1
  while IFS='|' read -r entry class evidence note; do
    [ -n "$entry" ] || continue
    if [ "$first" = 1 ]; then first=0; else printf ',\n'; fi
    if [ "$evidence" = "-" ]; then
      printf '    {"entry": "%s", "class": "%s", "evidence": null}' "$entry" "$class"
    else
      printf '    {"entry": "%s", "class": "%s", "evidence": "SQLeanite.%s"}' \
        "$entry" "$class" "$evidence"
    fi
  done < "$entries"
  printf '\n  ]'
}

case ${1:---check} in
  --markdown)
    verify
    emit_markdown
    ;;
  --json)
    verify
    emit_json
    ;;
  --check)
    verify
    if [ ! -f "$target" ]; then
      printf 'executable-boundary: %s is missing; run --markdown > %s\n' \
        "$target" "$target" >&2
      exit 1
    fi
    emit_markdown > "$scratch"
    if ! cmp -s "$scratch" "$target"; then
      printf 'executable-boundary: %s is stale; regenerate with --markdown\n' \
        "$target" >&2
      diff -u "$target" "$scratch" >&2 || true
      exit 1
    fi
    printf 'executable boundary is classified and current: %s entries (%s covered, %s seam, %s boundary)\n' \
      "$(grep -c . "$entries")" \
      "$(awk -F'|' '$2 == "covered"' "$entries" | wc -l | tr -d ' ')" \
      "$(awk -F'|' '$2 == "seam"' "$entries" | wc -l | tr -d ' ')" \
      "$(awk -F'|' '$2 == "boundary"' "$entries" | wc -l | tr -d ' ')"
    ;;
  *)
    printf 'usage: %s [--markdown|--json|--check]\n' "$0" >&2
    exit 2
    ;;
esac
