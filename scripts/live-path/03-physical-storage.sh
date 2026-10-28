# Sourced by live-path-check.sh; shares its failure status and scratch files.

# A conflicting UPDATE retains the original row, including when a key changes.
if grep -q 'executeIgnoredUpdate state tableName alias stored assignments.toList where_' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreUpdateIgnore.row state tableName ctx.schema row.rowid values' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'expressionAssignmentsWith true ctx assignments' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreUpdateScan.order ctx stored bound condition' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreUpdateScan.byColumn_perm' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'SQLite.PlannerCost.scan' SQLeanite/CoreUpdateScan.lean &&
   grep -Fq 'table.withIndexes (table.indexes ++ [index])' "$audit_sources/SQLeanite/Core.lean" &&
   grep -q 'let some database ← applyIndexIOFrom source database entry' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'CoreUpdateIgnore.finish_skips' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreUpdateIgnore.finish_inserts' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "UPDATE OR IGNORE retains old rows on conflict and checks accepted key changes"
else
  fail "UPDATE OR IGNORE is disconnected from its state-preservation checks"
fi

# IGNORE classifies typed constraint conflicts, leaving ordinary errors intact.
if grep -q 'CoreInsertIgnore.shouldInsert stored values' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'if conflict == .ignore then ignoreInsertRows' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'ignoreInsertRows state tableName stored.schema columns rows.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'unless expressions.all SQLite.Scalar.admitted' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreInsertIgnore.shouldInsert_no_conflict' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.executeIgnoredInsert_skips' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "INSERT OR IGNORE keeps typed constraints separate from expression errors"
else
  fail "INSERT OR IGNORE is disconnected from checked conflict handling"
fi

# RETURNING binds the actual table name and materializes old row outputs
# before Core commands can be published by either public file engine.
if grep -q 'executeDeleteReturning state tableName alias stored where_ returning' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreReturning.prepare ctx columns.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreReturning.deletionOutput stored ctx expressions commands' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreReturning.deletionOutput_length' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "DELETE RETURNING materializes validated old values before mutation"
else
  fail "DELETE RETURNING is detached from its validated materialization"
fi

# VALUES result metadata is replayed against the source, and its multi-row
# coroutine keeps a separate OFFSET evaluation rule from scalar SELECT.
if grep -q 'matchValuesBase query rows' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'the same first VALUES row' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'select.valueRows.isSome then executeValues state select' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'let row ← constantRow { select with valueRows := none }' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'SQLite.Values.directCount rows.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'SQLite.Values.collations rows.toList wrappedValues' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'SQLite.Values.directCount_le_length' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.executeValues_preserves_state' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "VALUES queries use checked metadata and their own row-evaluation discipline"
else
  fail "VALUES parsing or row execution is disconnected from its checks"
fi

# INSERT SELECT evaluates a source snapshot, validates even empty projections,
# and routes evaluated values through the existing checked INSERT machinery.
if grep -q 'let selection ← executeSelect state query' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'checkInsertSelectColumns stored.schema columns selection.width' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'selection.result.rows.mapM selectedRowExpressions' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q '.insertSelect ..' SQLeanite/CoreFileEngine.lean &&
   grep -q 'CoreSQL.insertSelection_empty' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "INSERT SELECT validates source width and persists through ordinary INSERT execution"
else
  fail "INSERT SELECT is disconnected from checked insertion or persistence"
fi

# DROP shares the transaction/persistence machinery with other schema writes.
if grep -q 'CoreSchemaDrop.table state.database' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSchemaDrop.index stored' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q '.dropTable .. | .dropIndex ..' SQLeanite/CoreFileEngine.lean &&
   grep -q 'dropTable name ifExists => (prepareDropTable' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'dropIndex name ifExists => (prepareDropIndex' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSchemaDrop.index_exact' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "DROP tables/indexes retains Core invariants and uses schema-write persistence"
else
  fail "DROP execution is disconnected from transaction persistence or its contracts"
fi

# Header-format restrictions must cover cold reads and in-transaction writes.
if grep -q 'CoreFileAdapter.requireReadable paths.main' SQLeanite/CoreFileEngine.lean &&
   grep -q 'CoreFileAdapter.requireReadable paths.main' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'CoreFileAdapter.requireWritableFormat connection.paths.main' SQLeanite/CoreFileEngine.lean &&
   grep -q 'CoreFileAdapter.requireWritableFormat paths.main' "$audit_sources/SQLeanite/CoreLazyWrite.lean" &&
   grep -q 'CoreWALFileAdapter.requireWritableFormat session' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'let header ← committedHeader session' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'SQLite.HeaderVersion.writeError? header' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'SQLite.HeaderVersion.readError? header' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'HeaderVersion.unknown_write' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "file and WAL header versions gate optimized reads and transaction writes"
else
  fail "file-format version admission is disconnected from execution"
fi

# Physical strides include reserved tails; record decoders receive usable bytes.
if grep -q 'pageBytes whole pageBytes pageNumber).map (List.take usable.val)' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q '(read pageNumber).map (List.take usable.val)' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'requireUnreservedWrite paths.main' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'unsupported reserved-byte database writes' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'headerUsablePageSize?_partition' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "reserved tails are excluded from decoding and unsupported writers fail before publication"
else
  fail "reserved-page geometry or unsupported-write guards are disconnected"
fi

if grep -q 'CellPagination.paginateCells' "$audit_sources/SQLeanite/CoreFile.lean"; then
  ok "encoder uses proved pagination"
else
  fail "the encoder no longer uses proved pagination"
fi

if grep -q 'GrowableStorage.deltaWrites old (storageImage image)' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'writeMainPages paths.main writes' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'SyscallVFS.pwritePages path.toString (pageTransfers writes)' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'SyscallVFS.verifyPages path.toString (pageTransfers writes)' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'allocatedPage startPage offset' "$audit_sources/SQLeanite/WidePageTree.lean" &&
   grep -q 'WidePageTree.buildNumberedWithFanout fanout startPage' \
     "$audit_sources/SQLeanite/CoreWideIndex.lean" &&
   grep -q 'interiorFanoutFor cells' "$audit_sources/SQLeanite/CoreWideIndex.lean" &&
   grep -q 'POSIXVFS.persistentCommitPlan oldImage' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'activatePersistentJournal syncOps paths' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'retirePersistentJournal syncOps paths' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'decodePersistent_encode' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'run_persistentCommitPlan' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'pageTransfers_toList' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'prepareBulkCommit? oldImage new' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'PreparedBulkCommit.postImageCertificate' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "rollback commits publish the proved changed-page transaction"
else
  fail "Core rollback commits bypass changed-page publication"
fi

if grep -q 'LiveState.invalidateCertificates result.1' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'retiredCertificates.set' SQLeanite/CoreFileEngine.lean &&
   grep -q 'certificates := some \[\]' SQLeanite/CoreFileEngine.lean; then
  ok "writes invalidate read certificates without rescanning or destructor tails"
else
  fail "write path reattached stale read certificates or lost bounded retirement"
fi

if grep -q 'prepareOrdinaryDelta? state next.database' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'commitLocalizedCertified connection.syncOps' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'connection.paths prepared.expectedBefore prepared.writes' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'PreparedOrdinaryDelta.ordinaryLocalizedCommit' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "ordinary localized commits consume one proof-carrying preparation"
else
  fail "ordinary localized syscall inputs detached from durability preparation"
fi

if grep -q 'structure PreparedLocalizedWrites' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'preparedCommitPlan journal prepared.writes' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'requestsEq' "$audit_sources/SQLeanite/CoreFileAdapter.lean"; then
  ok "header/freelist planning is tied to the exact localized syscall trace"
else
  fail "localized syscall trace detached from header/freelist preparation"
fi

if grep -q 'canonicalCandidate' SQLeanite/CoreFileEngine.lean &&
   grep -q 'tableExpectedBeforeEq' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'LocalizedLastIndexDelta.liveDeltaEquations' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "changed-index commits retain exact candidate and table-delta equations"
else
  fail "changed-index syscall inputs detached from their logical table delta"
fi

if grep -q 'CorePageCodec.encodeChecked database' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'prepareBulkCommit? oldImage new' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'CorePageCodec.encodeChecked database' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'let finalPlan ← topology.withCells? resolved.cells' SQLeanite/CoreSizedPageCodec.lean &&
   rg -F -q 'retainedIndexSQL catalog' SQLeanite/CoreWALFileAdapter.lean &&
   ! grep -q 'def encodeTable' "$audit_sources/SQLeanite/CoreOverflow.lean"; then
  ok "file creation uses the checked Core codec; WAL bulk encoding preserves its selected geometry and topology"
else
  fail "a live writer bypasses the expected Core codec"
fi

if grep -q 'provisional.retarget? resolved.cells' "$audit_sources/SQLeanite/CoreOverflow.lean" &&
   ! grep -q '_sameTopology' "$audit_sources/SQLeanite/CoreOverflow.lean" &&
   ! grep -q 'RecursivePageBTree.build leaves' "$audit_sources/SQLeanite/CoreOverflow.lean" &&
   ! grep -q 'RecursivePageBTree.buildIndex leaves' "$audit_sources/SQLeanite/CoreOverflow.lean"; then
  ok "overflow pointer resolution preserves one planned page topology"
else
  fail "overflow encoding rebuilt or rechecked independently planned topology"
fi

if grep -q 'CoreFileAdapter.lookupIndexCandidates' SQLeanite/CoreFileEngine.lean &&
   grep -q 'Core.executeUncertifiedQueryWithCandidates' SQLeanite/CoreFileEngine.lean &&
   grep -q 'lookupIndexValueIOFrom source value' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'lookupIndexRangeIOFrom source operation value' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'indexValueCandidatesWith source.readPage' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'indexValueCandidatesWith (m := Id)' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'indexRangeCandidatesWith source.readPage' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'indexRangeCandidatesWith (m := Id)' "$audit_sources/SQLeanite/CoreDecode.lean"; then
  ok "file SELECTs exercise validated page-directed point/range index lookup"
else
  fail "file SELECTs bypass persisted-index traversal"
fi

uncertified_calls=$(grep -c 'Core.executeUncertifiedQueryWithCandidates' \
  SQLeanite/CoreFileEngine.lean || true)
if [ "$uncertified_calls" -eq 1 ] &&
   grep -q 'match ← connection.provenance.get with' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q '| .foreign =>' SQLeanite/CoreFileEngine.lean &&
   grep -q '| .generated =>' SQLeanite/CoreFileEngine.lean &&
   grep -q 'generatedImageStamp paths' SQLeanite/CoreFileEngine.lean; then
  ok "uncertified candidate comparison is confined to foreign files"
else
  fail "a generated/certified query can reach the foreign validation boundary"
fi

if grep -q 'CoreFileAdapter.lookupCertifiedIndexCandidates certificates' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'return (live, .ok (live, \[lookup.result\]))' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'retargetIntegerIndexCertificates certificates' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'StoredIntegerIndex state.database' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'tableMember : table ∈ database.tables' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   ! grep -q 'certifiedLookupWorthAttempting' \
     SQLeanite/CoreFileEngine.lean &&
   ! grep -q 'if rowsEqual : stored.table.rows = table.rows' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'lookupIndexValueFrom_certified_exact' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'lookupIndexRangeFrom_certified_exact' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'StoredIntegerIndex.retarget_value_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'updateState?_tablePagesSufficient' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CertifiedCandidates.result_exact' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "proof-carrying certified indexes survive state transitions without table scans"
else
  fail "the certified index path detached from lookup or maintenance proofs"
fi

if grep -q 'reuseFreedRoot under freed' \
     "$audit_sources/SQLeanite/PersistentPageTree.lean" &&
   grep -q 'allocatedTree.reuseFresh? nextPage deleted.2' \
     "$audit_sources/SQLeanite/CoreChunkPageDelta.lean" &&
   grep -q 'Store.reuseFresh?_toList' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'table.IdentityWellFormed' \
     "$audit_sources/SQLeanite/CoreChunkPageDelta.lean" &&
   grep -q 'updateState?_identityWellFormed' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "localized deletion keeps active and freed page identities disjoint"
else
  fail "localized deletion detached from its physical identity invariant"
fi

if grep -q 'CoreChunkPageDelta.updateStateCandidate?' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'prepareAppendedIndex? validated input delta' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'certifyIndexEncoding? rootPage after index' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'prepareLocalizedLastIndex? validated' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'unless indexTailMatches source entry.rootPage prior.value.pages' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'CoreFileAdapter.indexTailMatches_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'commitLocalizedCertified connection.syncOps' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'certifyIndexEncoding?_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'replaceBetween?_sameData' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'updateStateCandidate?_identityWellFormed' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'def packSized' SQLeanite/CellPagination.lean &&
   grep -q 'packSized current (encodedSize current) rest' \
     SQLeanite/CellPagination.lean &&
   grep -q 'CellPagination.fastFit_iff' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "new and shrinking indexes use certified localized encoding"
else
  fail "new or changed-index localization detached from its encoding proofs"
fi

if grep -q 'current.retarget? delta sufficient' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'ValidatedOpenState.retarget?_indexImage' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'let (validated, _) ← CoreFileAdapter.commit' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'prepareBulkCommit? oldImage new' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'PreparedBulkCommit.postImageCertificate' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'encodeBulkWithState_represents' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'verifyWrittenPages paths.main writes' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'changedPageWrites oldTail' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'omitted_changedPageWrites_matches' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "commits retain one validated state and omit byte-identical index pages"
else
  fail "commit validation or localized index filtering detached from its proofs"
fi

if ! grep -q 'after.find? fun row => !before.any' \
     "$audit_sources/SQLeanite/CoreChunkPageDelta.lean" &&
   ! grep -q 'before.find? fun row => !after.any' \
     "$audit_sources/SQLeanite/CoreChunkPageDelta.lean" &&
   grep -q 'firstInserted_mem_after' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'firstDeleted_mem_before' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "bulk row differencing uses proved linear ordered merges"
else
  fail "bulk row differencing regressed to nested scans or lost its proof"
fi

if grep -q 'certifyWideIntegerIndex source fuel' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'certifyAllValueIndex source fuel' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'CertifiedAllValueIndex.valueEntries_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CertifiedAllValueIndex.rangeEntries_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'IntegerIndexRouting.valueEntries_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'IntegerIndexRouting.rangeEntries_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'decodeWideAbstractIndexTreeFrom_toList' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'decodeWideAbstractIndexTreeFrom' "$audit_sources/SQLeanite/CoreDecode.lean"; then
  ok "wide and mixed C-produced indexes retain exact query certificates"
else
  fail "general index certification detached from the live connection"
fi

if grep -q 'CoreOptimizerBridge.optimize tableName query' SQLeanite/CoreFileEngine.lean &&
   grep -q 'CoreOptimizerBridge.optimize tableName query' SQLeanite/CoreWALFileEngine.lean &&
   grep -q 'QuerySemantics.optimizePlan' "$audit_sources/SQLeanite/CoreOptimizerBridge.lean" &&
   grep -q 'QuerySemantics.unionDistribution' "$audit_sources/SQLeanite/CoreOptimizerBridge.lean" &&
   grep -q 'unionDistribution' SQLeanite/Optimizer.lean; then
  ok "rollback and WAL SELECTs execute the proved denotational optimizer pipeline"
else
  fail "a live Core SELECT path bypasses the denotational optimizer"
fi

if grep -q 'def rewriteRoot (plan : Plan)' SQLeanite/Optimizer.lean &&
   grep -q 'projectionElimination (constantFolding plan)' \
     SQLeanite/Optimizer.lean &&
   grep -q 'rewriteRoot_cost_le' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'optimizePlan_cost_le' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'filterFusion_not_unconditionally_cost_safe' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "live optimizer root is restricted to proved cost-safe rewrites"
else
  fail "live optimizer selected a rewrite without its logical cost certificate"
fi

# The check above is a spot check on three names. This one is exhaustive over the
# `Rewrite` enum: every constructor must be either (a) selected by the live root
# pipeline *and* carrying its own `_cost_le` certificate, or (b) not selected and
# named in the docstring that says why. A new rewrite constructor then cannot be
# added silently -- it lands in neither bucket and this fails.
rewrite_constructors=$(awk '
  /^inductive Rewrite where/ { inside = 1; next }
  inside && /^  deriving/ { inside = 0 }
  inside && /^  \| / { sub(/^  \| /, ""); print $1 }
' SQLeanite/Optimizer.lean)
rewrite_total=$(printf '%s\n' "$rewrite_constructors" | grep -c .)
rewrite_selected=0
rewrite_excluded=0
rewrite_broken=""
root_body=$(grep -A 1 '^def rewriteRoot (plan : Plan)' SQLeanite/Optimizer.lean |
  tail -n 1)
for rewrite in $rewrite_constructors; do
  if printf '%s' "$root_body" | grep -q "$rewrite"; then
    if grep -q "theorem ${rewrite}_cost_le" SQLeanite/QueryCost.lean &&
       grep -q "${rewrite}_cost_le" "$audit_sources/SQLeanite/ProofAxioms.lean"; then
      rewrite_selected=$((rewrite_selected + 1))
    else
      rewrite_broken="$rewrite_broken $rewrite(selected,uncertified)"
    fi
  else
    # Not selected. Either a proved negative result or an explicitly stated
    # exclusion in the docstring above `rewriteRoot`.
    stated=$(sed -n '/^Predicate pushdown needs a nonempty-right precondition/,/cost certificate\./p' \
      SQLeanite/Optimizer.lean)
    case $rewrite in
      filterFusion)
        if grep -q "${rewrite}_not_unconditionally_cost_safe" \
             "$audit_sources/SQLeanite/ProofAxioms.lean"; then
          rewrite_excluded=$((rewrite_excluded + 1))
        else
          rewrite_broken="$rewrite_broken $rewrite(excluded,unjustified)"
        fi
        ;;
      predicatePushdown)
        if printf '%s' "$stated" | grep -q 'Predicate pushdown'; then
          rewrite_excluded=$((rewrite_excluded + 1))
        else
          rewrite_broken="$rewrite_broken $rewrite(excluded,undocumented)"
        fi
        ;;
      unionDistribution)
        if printf '%s' "$stated" | grep -q 'join distribution'; then
          rewrite_excluded=$((rewrite_excluded + 1))
        else
          rewrite_broken="$rewrite_broken $rewrite(excluded,undocumented)"
        fi
        ;;
      *)
        rewrite_broken="$rewrite_broken $rewrite(unaccounted)"
        ;;
    esac
  fi
done
if [ -n "$rewrite_broken" ]; then
  fail "rewrite accounting incomplete:$rewrite_broken"
elif [ "$((rewrite_selected + rewrite_excluded))" -ne "$rewrite_total" ] ||
     [ "$rewrite_total" -eq 0 ]; then
  fail "rewrite accounting does not cover the enum: \
$rewrite_selected selected + $rewrite_excluded excluded of $rewrite_total"
else
  ok "cost accounting is exhaustive over the rewrite enum \
($rewrite_selected of $rewrite_total selected and certified, \
$rewrite_excluded excluded with a stated reason)"
fi

if grep -q 'innerJoin_true_eval' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'permute_eval' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'permute_symm_eval' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "POPL algebra product and permutation parity witnesses are audited"
else
  fail "POPL algebra parity witness detached from the proof audit"
fi

# Being *audited* is weaker than being *reached*. `permute_eval` on its own is a
# theorem about a standalone module: `RelationalAlgebra.lean` is imported only by
# `CoreReadSemantics` and `ProofAxioms`, so an audit entry proves nothing about
# the shipped projection. The permutation parity claim therefore additionally
# requires a bridge stated over the *live* query denotation, and this asserts
# that bridge exists, is about `Core.Query`, and lands in the audit.
if grep -q 'theorem permuted_projection_denotes' \
     "$audit_sources/SQLeanite/CoreReadSemantics.lean" &&
   grep -q 'RelationalAlgebra.permute (columnBijection perm)' \
     "$audit_sources/SQLeanite/CoreReadSemantics.lean" &&
   grep -q 'queryDenotation' "$audit_sources/SQLeanite/CoreReadSemantics.lean" &&
   grep -q 'ofList_map_permute' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'permuted_projection_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "live projection permutation reaches the POPL permutation operator"
else
  fail "column permutation parity is audited but not reached from Core.Query"
fi

# The documented-executable-boundary claim is only honest if the boundary cannot
# move quietly. This fails when a shipped entry point is unclassified, when a
# classification cites an unaudited theorem, or when a boundary-listed module
# acquires theorems and the document understates what is proved.
if scripts/executable-boundary.sh --check > "$scratch_parity" 2>&1; then
  ok "$(cat "$scratch_parity")"
else
  cat "$scratch_parity" >&2
  fail "the executable boundary is stale, incomplete or overstated"
fi

# Byte compatibility is the claim with no prior art, so its evidence must be
# present and its declarations must be checked rather than remembered. Three
# things are pinned: the reverse corpus covers the named file features, the
# out-of-scope shapes are asserted to *fail closed* rather than merely being
# absent, and the generated compatibility document is current.
if grep -q 'without-rowid|reject|' scripts/run-reverse-differential.sh &&
   grep -q 'composite-primary-key|reject|' scripts/run-reverse-differential.sh &&
   grep -q 'no-primary-key|pass|' scripts/run-reverse-differential.sh; then
  ok "remaining unsupported file shapes fail closed and implicit-rowid tables are accepted"
else
  fail "an out-of-scope file shape lost its fail-closed declaration"
fi
