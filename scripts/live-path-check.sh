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

# Row-expression predicates remain on the production Core read boundary.
if grep -q 'executeFilteredSelect state select source stored' SQLeanite/CoreSQL.lean &&
   grep -q 'ctx.scan select.where_ expressions select.distinct result.rows' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.executeFilteredSelect_preserves_state' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreExpr.scan_length_le' SQLeanite/ProofAxioms.lean; then
  ok "row-expression WHERE uses bounded scans on Core query results"
else
  fail "row-expression WHERE route or its registered contracts are missing"
fi

# DISTINCT source representatives must use the same route after file reopen.
if [ "$(grep -c 'if queryNeedsRepresentatives select.distinct columns ordering then' SQLeanite/CoreSQL.lean)" -eq 2 ] &&
   grep -q 'directQuery : CoreSQL.queryNeedsRepresentatives' SQLeanite/CoreSQLReadText.lean; then
  ok "DISTINCT representative routing is shared by SQL and the persisted recognizer"
else
  fail "DISTINCT representative routing or direct-query proof premise is missing"
fi

# Row-dependent UPDATE remains an atomic trace of proved Core point updates.
if grep -q 'executeExpressionUpdate state tableName alias stored' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.executeExpressionUpdate_eq_runCoreCommands' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.rowUpdateCommands_length_le' SQLeanite/ProofAxioms.lean; then
  ok "row-dependent UPDATE uses a bounded Core command trace"
else
  fail "row-dependent UPDATE is detached from its Core trace contracts"
fi

# Scalar DELETE must share the Core atomic command boundary.
if grep -q 'executeExpressionDelete state tableName alias stored where_' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.executeExpressionDelete_eq_runCoreCommands' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.rowDeleteCommands_length_le' SQLeanite/ProofAxioms.lean; then
  ok "row-dependent DELETE uses a bounded Core command trace"
else
  fail "row-dependent DELETE is detached from its Core trace contracts"
fi

# 1. No Legacy* module survives.
if ls SQLeanite/Legacy*.lean >/dev/null 2>&1; then
  fail "Legacy modules still present"
else
  ok "no Legacy modules"
fi

# 2. The Core cone must not reach the legacy interpreter's executor.
if grep -rl 'import SQLeanite.Legacy' SQLeanite/Core*.lean >/dev/null 2>&1; then
  fail "a Core module imports a Legacy module"
else
  ok "Core imports no Legacy module"
fi

# 3. ProofAxioms must be in the build graph and free of dead references.
if grep -q '^import SQLeanite.ProofAxioms' SQLeanite.lean; then
  ok "ProofAxioms is in the build graph"
else
  fail "ProofAxioms is not imported by the library root, so it can rot"
fi

# 4. Every theorem named in ProofAxioms must still exist. `lake build` covers
#    this now that ProofAxioms is imported, but check the report directly too.
axioms=$(mktemp); scratch_parity=$(mktemp)
trap 'rm -f "$axioms" "$scratch_parity"' EXIT
if ! "$lake_command" env lean SQLeanite/ProofAxioms.lean > "$axioms" 2>&1; then
  printf 'live-path check FAILED: ProofAxioms did not elaborate\n' >&2
  cat "$axioms" >&2
  exit 1
fi
expected=$(grep -c '^#print axioms ' SQLeanite/ProofAxioms.lean)
reported=$(grep -c 'depends on axioms\|does not depend' "$axioms" || true)
if [ "$reported" -ne "$expected" ]; then
  fail "ProofAxioms report is incomplete: expected $expected declarations, found $reported"
fi
if grep -q 'unknown constant' "$axioms"; then
  fail "ProofAxioms names a theorem that no longer exists"
  grep 'unknown constant' "$axioms" >&2
else
  ok "every headline theorem resolves"
fi
if grep -q 'sorryAx' "$axioms"; then
  fail "a headline theorem depends on sorryAx"
else
  ok "no headline theorem depends on sorryAx"
fi

# Every production SQL entry point must replay the concrete token certificate.
for entry in Main.lean SQLeanite/CoreFileEngine.lean \
    SQLeanite/CoreWALFileEngine.lean SQLeanite/CoreLazyFileEngine.lean; do
  if grep -q 'CoreTokenGrammar.parseStatements sql' "$entry" &&
     ! grep -Eq '(^|[^[:alnum:]_.])parse sql' "$entry"; then
    ok "$entry uses certified SQL admission"
  else
    fail "$entry bypasses the concrete SQL certificate"
  fi
done

if grep -q 'SQLite.PhysicalAffinity.write column.affinity' SQLeanite/CoreSQL.lean &&
   grep -q 'comparisonLiteral schema index' SQLeanite/CoreSQL.lean &&
   grep -q 'Core.readColumnValues schema.columns' SQLeanite/CoreRecord.lean &&
   grep -q 'SQLite.PhysicalAffinity.accepts column.affinity' SQLeanite/Core.lean &&
   grep -q 'Core.readColumnValues_eq_self' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreTokenGrammar.parseStatements_certified' SQLeanite/ProofAxioms.lean; then
  ok "stored affinity is checked on writes, comparisons and record reads"
else
  fail "stored affinity detached from the proved production path"
fi

# Constant expressions use the pure scalar layer on the production translator.
if grep -q 'SQLite.Scalar.admitted expression' SQLeanite/SQLSurface.lean &&
   grep -q 'value (← SQLite.Scalar.eval expression)' SQLeanite/SQLSurface.lean &&
   grep -q 'SQLSurface.literal expression' SQLeanite/CoreSQL.lean &&
   grep -q 'executeConstantSelect state select' SQLeanite/CoreSQL.lean &&
   grep -q 'private def formatFloat : Float → String := SQLite.FloatCodec.render' SQLeanite/Value.lean &&
   grep -q 'let value := SQLite.FloatCodec.decimalToBinary' SQLeanite/Value.lean &&
   grep -q 'SQLite.FloatCodec.multiply128_reconstruct' SQLeanite/ProofAxioms.lean &&
   grep -q 'SQLite.Numeric.integerPrefix_bounds' SQLeanite/ProofAxioms.lean &&
   grep -q 'SQLite.Scalar.add_integer_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.executeConstantSelect_preserves_state' SQLeanite/ProofAxioms.lean; then
  ok "pure SQLite scalar layer and constant SELECT are wired into Core SQL"
else
  fail "scalar layer detached from the live translator or its proofs"
fi

# Text/blob helpers must be called from the production scalar evaluator.
if grep -q 'import SQLeanite.SQLite.Text' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'SQLite.Text.substr v start count' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'SQLite.Text.unhex v ignored' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'SQLite.Text.slice_length_le' SQLeanite/ProofAxioms.lean &&
   grep -q 'SQLite.Text.minmax_null' SQLeanite/ProofAxioms.lean; then
  ok "pure text/blob functions are wired into scalar evaluation and proof audit"
else
  fail "text/blob functions detached from the live scalar path or its proofs"
fi

if grep -q 'CoreExpr.Context' SQLeanite/CoreSQL.lean &&
   grep -q 'executeExpressionSelect state select source stored wherePredicate' SQLeanite/CoreSQL.lean &&
   grep -q 'SQLite.Scalar.evalWith (ctx.lookup row) ctx.affinity' SQLeanite/CoreExpr.lean &&
   grep -q 'CoreExpr.projectRow_width' SQLeanite/ProofAxioms.lean; then
  ok "row projections use explicit bindings, shared scalar evaluation and audited result widths"
else
  fail "row expressions detached from the production evaluator or width proof"
fi

if grep -q 'limitRows query.limit (stableDistinctBy distinctRowKey projected)' SQLeanite/CoreEngine.lean &&
   grep -q 'orderedLimit (Core.stableDistinctBy' SQLeanite/CoreReadSemantics.lean &&
   grep -q 'Core.Query.eval_distinct_limit' SQLeanite/ProofAxioms.lean &&
   grep -q 'Core.Query.eval_distinct_key_nodup' SQLeanite/ProofAxioms.lean &&
   grep -q 'Core.stableDistinctBy' SQLeanite/CoreExpr.lean; then
  ok "DISTINCT precedes LIMIT on the live Core query and its bag denotation"
else
  fail "DISTINCT/LIMIT implementation detached from its corrected denotation"
fi

if grep -q 'CoreCompound.combine operation left right' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.combineRows_denotes' SQLeanite/ProofAxioms.lean &&
   grep -q 'distinctRowKey row' SQLeanite/CoreCompound.lean; then
  ok "SQL compounds use numeric keys and the live key-bag refinement"
else
  fail "SQL compound equality detached from its typed set-operation proof"
fi

if grep -q 'distinctRowKey (query.originalKey row)' SQLeanite/CoreEngine.lean &&
   grep -q 'query.outputKey rows key' SQLeanite/CoreEngine.lean &&
   grep -q 'GroupQuery.representative_key' SQLeanite/ProofAxioms.lean; then
  ok "GROUP BY compares numeric keys and retains a proved source representative"
else
  fail "GROUP BY numeric equivalence or original representative is detached"
fi

# 5. Functions that carry the headline proofs must be reachable from the CLI.
#    Checked structurally: the executor must call the planner, and Main must
#    route --verified-file into the Core engine.
if grep -q 'query.eval (table.plannedRows query)' SQLeanite/CoreEngine.lean; then
  ok "executor runs Table.plannedRows"
else
  fail "the executor no longer runs the proved index planner"
fi

if grep -q 'table.insertValues values' SQLeanite/CoreEngine.lean &&
   grep -q 'table.replaceValues values' SQLeanite/CoreEngine.lean &&
   grep -q 'table.findRowid? row.rowid' SQLeanite/Core.lean &&
   grep -q 'table.rowTree.root.lookup rowid.treeKey' SQLeanite/Core.lean &&
   grep -q 'table.rowTree.root.last?.map' SQLeanite/Core.lean &&
   grep -q 'PersistentPageTree.Node.lookup_eq_erase' SQLeanite/ProofAxioms.lean &&
   grep -q 'table.upsertGeneratedFresh row valid hidden' SQLeanite/Core.lean &&
   grep -q 'Table.findDeclaredPrimary?_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'Table.upsertGeneratedFresh_rows' SQLeanite/ProofAxioms.lean &&
   grep -q 'Table.findRowid?_eq_some_iff' SQLeanite/ProofAxioms.lean; then
  ok "executor uses proof-carrying Core INSERT/REPLACE and balanced TEXT-key routing"
else
  fail "Core INSERT/REPLACE bypasses their proof-carrying table operations"
fi

if grep -q 'table.retainRows fun row' SQLeanite/CoreEngine.lean &&
   grep -q 'table.patchRowid assignments rowid' SQLeanite/CoreEngine.lean &&
   grep -q 'table.updateWhere assignments predicate' SQLeanite/CoreEngine.lean &&
   grep -q 'table.patchRows assignments (selects predicate)' SQLeanite/CoreEngine.lean; then
  ok "executor uses tree-local point UPDATE and validated general mutations"
else
  fail "Core DELETE/UPDATE bypasses their validated mutation paths"
fi

if grep -q 'execute_createTable_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_createIndex_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_insert_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_replace_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_deleteWhere_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_updateWhere_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_commit_exact' SQLeanite/ProofAxioms.lean; then
  ok "all seven write commands retain execute-level correspondence proofs"
else
  fail "a live write command detached from its execute-level theorem"
fi

if grep -q 'execute_createTable_to_bytes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_createIndex_to_bytes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_insert_to_bytes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_replace_to_bytes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_delete_to_bytes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_update_to_bytes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_commit_to_bytes' SQLeanite/ProofAxioms.lean &&
   grep -q 'localized_state_represents_database' \
     SQLeanite/ProofAxioms.lean; then
  ok "all seven write postconditions compose with SQLite bytes"
else
  fail "a live write command detached from its SQLite byte refinement"
fi

if grep -q 'comparisonPredicate schema' SQLeanite/CoreSQL.lean &&
   grep -q 'lexFast sql' SQLeanite/Lexer.lean &&
   grep -q 'lex_sound' SQLeanite/ProofAxioms.lean &&
   grep -q 'parse_success_tokenizes' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreTokenGrammar.parseCertified_sound' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreTokenGrammar.parseCertified_agrees_parse' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreTokenGrammar.Parses.grammar' SQLeanite/ProofAxioms.lean &&
   grep -q 'ParsedSupportedText.tokenizes' SQLeanite/ProofAxioms.lean &&
   grep -q 'ParsedSupportedText.grammar' SQLeanite/ProofAxioms.lean &&
   grep -q 'literalSyntax_of_success' SQLeanite/ProofAxioms.lean &&
   grep -q 'predicateSyntax_of_success' SQLeanite/ProofAxioms.lean &&
   grep -q 'groupOutputSyntax_of_success' SQLeanite/ProofAxioms.lean &&
   grep -q 'joinPredicateSyntax_of_success' SQLeanite/ProofAxioms.lean &&
   grep -q 'parsedSupportedText_of_execute_success' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreTokenGrammar.parseCertified sql' SQLeanite/CoreSQL.lean; then
  ok "live Core translation carries independent proof-producing token grammar"
else
  fail "Core SQL translation detached from its grammar or text certificate"
fi

if grep -q 'rollbackCommit_core_crash_atomic' SQLeanite/ProofAxioms.lean &&
   grep -q 'rollbackCommit_represents_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'rollbackCommit_core_returned_recovers_new' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'rollbackCommit_core_repeated_recovery_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'rollbackCommit_represents_recovery_crash_trace_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'rollbackCommit_padded_recovery_crash_trace_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'rollbackCommit_recovery_crash_trace_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreFreelistCodec.decode_paddedImage' \
     SQLeanite/CoreDurability.lean &&
   grep -q 'CoreFileAdapter.commit_crash_atomic' \
     SQLeanite/CoreDurability.lean &&
   grep -q 'CorePageCodec.decode_encodeBulk' \
     SQLeanite/CoreDurability.lean &&
   grep -q 'decodeChecked_makeJournal_exact' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'PhysicalJournalCodec.encodePersistentActiveBytes journal' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'PhysicalJournalCodec.decodePersistent encoded.data.toList' \
     SQLeanite/CoreFileAdapter.lean; then
  ok "rollback crash atomicity reaches concrete Core SQLite bytes"
else
  fail "Core database durability detached from the codec or journal theorem"
fi

if grep -q 'executeCommand_commit_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeCommand_returned_recovers_new' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeCommand_recovery_crash_trace_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreDurability.rollbackWrites_represents_crash_atomic' \
     SQLeanite/CoreEndToEnd.lean &&
   grep -q 'execute_write_exact command success' \
     SQLeanite/CoreEndToEnd.lean; then
  ok "all persisted Core commands compose with crash-atomic SQLite bytes"
else
  fail "Core write semantics detached from the durability composition"
fi

if grep -q 'executeText_commit_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_returned_recovers_new' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_recovery_crash_trace_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeStatement_eq_core translated' \
     SQLeanite/CoreSQLWriteText.lean &&
   grep -q 'CoreEndToEnd.executeCommand_commit_crash_atomic' \
     SQLeanite/CoreSQLWriteText.lean &&
   grep -q 'CoreDurability.PostImageCertificate' \
     SQLeanite/CoreSQLWriteText.lean &&
   grep -q 'PostImageCertificate.representsDatabase' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreTokenGrammar.parseCertified sql' SQLeanite/CoreSQL.lean; then
  ok "supported SQL write text composes with crash-atomic SQLite bytes"
else
  fail "SQL text boundary detached from write durability"
fi

if grep -q 'executeText_insertRows_commit_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'insertRows_eq_runCoreCommands' SQLeanite/CoreSQLWriteText.lean &&
   grep -q 'executeWriteCommands_exact' SQLeanite/CoreSQLWriteText.lean; then
  ok "multi-row SQL write text composes with crash-atomic SQLite bytes"
else
  fail "multi-row SQL write refinement is detached from the live executor"
fi

if grep -q 'CoreSQLTraceText.executeText_commit_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQLTraceText.executeText_localized_commit_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_committedLocalizedIndexedSingle_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_committedLocalizedIndexedSingleOfRowsInline_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_committedLocalizedIndexedInlineTables_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_committedLocalizedIndexedSingleOfInlineTree_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_committedLocalizedIndexedSingleOfInlineRows_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_committedLocalizedIndexedSingleYCSB_crash_atomic' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CommittedLocalizedDelta.trace_eq_commitPlan' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'LocalizedRepresentation.representsDatabase' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'localizedRepresentation_of_certificates' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'sqliteHeaderMatches_of_pageZeroWrite' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'catalogRead_of_pageZeroWrite' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreLocalizedRepresentation.TablesDecode.mapM' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'IndexMetadataGroups.rebuild' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'applyIndexesForOpen_of_index_certificates' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'runStatements_eq_commands' SQLeanite/CoreSQLTraceText.lean &&
   grep -q '| begin : TranslatedBlock' SQLeanite/CoreSQLTraceText.lean &&
   grep -q '| rollback : TranslatedBlock' SQLeanite/CoreSQLTraceText.lean; then
  ok "transactional SQL statement lists compose with crash recovery"
else
  fail "transactional SQL statement-list proof is detached"
fi

if grep -q 'executeText_read_refines' SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_count_refines' SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_sum_refines' SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_extreme_refines' SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_group_refines' SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_join_refines' SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_binary_refines' SQLeanite/ProofAxioms.lean &&
   grep -q 'executeText_compound_refines' SQLeanite/ProofAxioms.lean &&
   grep -q 'armsRefine armsTranslated' \
     SQLeanite/CoreSQLReadText.lean &&
   grep -q 'CoreSQL.combineRows_denotes' \
     SQLeanite/CoreSQLReadText.lean &&
   grep -q 'CoreReadSemantics.execute_query_denotes' \
     SQLeanite/CoreSQLReadText.lean &&
   grep -q 'executeStatement_eq_core translated' \
     SQLeanite/CoreSQLReadText.lean &&
   grep -q 'CoreTokenGrammar.parseCertified sql' SQLeanite/CoreSQL.lean; then
  ok "supported SQL read text reaches the independent bag denotation"
else
  fail "SQL text boundary detached from read denotation"
fi

if grep -q '| .primaryKey rowid => table.primaryKeyRows rowid' \
     SQLeanite/CoreEngine.lean &&
   grep -q 'exact Query.eval_primaryKey table query rowid' \
     SQLeanite/CoreEngine.lean; then
  ok "executor uses exact proved primary-key pruning"
else
  fail "the live primary-key planner detached from its exactness theorem"
fi

if grep -q '"--verified-file" :: databasePath :: rest => coreBatch' Main.lean; then
  ok "--verified-file routes to the Core engine"
else
  fail "--verified-file no longer routes to the Core engine"
fi

if ! grep -q '^import SQLeanite.CoreRuntime$' Main.lean; then
  fail "Main does not use the narrow production Core import surface"
elif grep -q '^import SQLeanite$\|^import SQLeanite.Engine$' Main.lean; then
  fail "Main imports the umbrella or legacy interpreter"
else
  ok "production executable excludes the legacy interpreter import"
fi

if grep -q 'CanonicalSchemaSQL.parse sql' SQLeanite/CoreDecode.lean; then
  ok "decoder uses the canonical schema recognizer"
else
  fail "the decoder no longer tries the proved canonical schema recognizer"
fi

# The general open must derive its page geometry from the validated header, not
# from the 4096-byte constant. It previously did this by passing `usable` to
# `filePageSourceFor`; it now slices a single buffered read using `usable.val`,
# which is faster but just as easy to get wrong -- substituting the fixed-size
# `byteArrayPageSource` here silently broke the 1024-byte differential case, so
# both the positive and the negative check are asserted.
if grep -q 'let pageBytes := usable.val' \
     SQLeanite/CoreFileAdapter.lean &&
   ! grep -q 'byteArrayPageSource whole count' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'decodeCatalogForPageSize source.usable.val firstPage' \
     SQLeanite/CoreDecode.lean &&
   grep -q 'decodeTableLeafCell source.usable input' \
     SQLeanite/CoreDecode.lean &&
   grep -q 'decodeLeafIndexCell source.usable input' \
     SQLeanite/CoreDecode.lean &&
   grep -q 'headerUsablePageSize?_val' SQLeanite/ProofAxioms.lean; then
  ok "general opens carry the validated SQLite page size through decoding"
else
  fail "general opens detached from dynamic page-size validation"
fi

if grep -q 'CellPagination.paginateCells' SQLeanite/CoreFile.lean; then
  ok "encoder uses proved pagination"
else
  fail "the encoder no longer uses proved pagination"
fi

if grep -q 'GrowableStorage.deltaWrites old (storageImage image)' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'writeMainPages paths.main writes' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'SyscallVFS.pwritePages path.toString (pageTransfers writes)' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'SyscallVFS.verifyPages path.toString (pageTransfers writes)' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'allocatedPage startPage offset' SQLeanite/WidePageTree.lean &&
   grep -q 'WidePageTree.buildNumberedWithFanout fanout startPage' \
     SQLeanite/CoreWideIndex.lean &&
   grep -q 'interiorFanoutFor cells' SQLeanite/CoreWideIndex.lean &&
   grep -q 'POSIXVFS.persistentCommitPlan oldImage' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'activatePersistentJournal syncOps paths' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'retirePersistentJournal syncOps paths' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'decodePersistent_encode' SQLeanite/ProofAxioms.lean &&
   grep -q 'run_persistentCommitPlan' SQLeanite/ProofAxioms.lean &&
   grep -q 'pageTransfers_toList' SQLeanite/ProofAxioms.lean &&
   grep -q 'prepareBulkCommit? oldImage new' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'PreparedBulkCommit.postImageCertificate' \
     SQLeanite/ProofAxioms.lean; then
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
     SQLeanite/ProofAxioms.lean; then
  ok "ordinary localized commits consume one proof-carrying preparation"
else
  fail "ordinary localized syscall inputs detached from durability preparation"
fi

if grep -q 'structure PreparedLocalizedWrites' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'preparedCommitPlan journal prepared.writes' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'requestsEq' SQLeanite/CoreFileAdapter.lean; then
  ok "header/freelist planning is tied to the exact localized syscall trace"
else
  fail "localized syscall trace detached from header/freelist preparation"
fi

if grep -q 'canonicalCandidate' SQLeanite/CoreFileEngine.lean &&
   grep -q 'tableExpectedBeforeEq' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'LocalizedLastIndexDelta.liveDeltaEquations' \
     SQLeanite/ProofAxioms.lean; then
  ok "changed-index commits retain exact candidate and table-delta equations"
else
  fail "changed-index syscall inputs detached from their logical table delta"
fi

if grep -q 'CorePageCodec.encodeChecked database' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'prepareBulkCommit? oldImage new' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'CorePageCodec.encodeChecked database' SQLeanite/CoreWALFileAdapter.lean &&
   ! grep -q 'def encodeTable' SQLeanite/CoreOverflow.lean; then
  ok "all writers use store-owned table topology and checked creation/WAL encoding"
else
  fail "a live writer bypasses the expected Core codec"
fi

if grep -q 'provisional.retarget? resolved.cells' SQLeanite/CoreOverflow.lean &&
   ! grep -q '_sameTopology' SQLeanite/CoreOverflow.lean &&
   ! grep -q 'RecursivePageBTree.build leaves' SQLeanite/CoreOverflow.lean &&
   ! grep -q 'RecursivePageBTree.buildIndex leaves' SQLeanite/CoreOverflow.lean; then
  ok "overflow pointer resolution preserves one planned page topology"
else
  fail "overflow encoding rebuilt or rechecked independently planned topology"
fi

if grep -q 'CoreFileAdapter.lookupIndexCandidates' SQLeanite/CoreFileEngine.lean &&
   grep -q 'Core.executeUncertifiedQueryWithCandidates' SQLeanite/CoreFileEngine.lean &&
   grep -q 'lookupIndexValueIOFrom source value' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'lookupIndexRangeIOFrom source operation value' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'indexValueCandidatesWith source.readPage' SQLeanite/CoreDecode.lean &&
   grep -q 'indexValueCandidatesWith (m := Id)' SQLeanite/CoreDecode.lean &&
   grep -q 'indexRangeCandidatesWith source.readPage' SQLeanite/CoreDecode.lean &&
   grep -q 'indexRangeCandidatesWith (m := Id)' SQLeanite/CoreDecode.lean; then
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
     SQLeanite/CoreFileAdapter.lean &&
   ! grep -q 'certifiedLookupWorthAttempting' \
     SQLeanite/CoreFileEngine.lean &&
   ! grep -q 'if rowsEqual : stored.table.rows = table.rows' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'lookupIndexValueFrom_certified_exact' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'lookupIndexRangeFrom_certified_exact' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'StoredIntegerIndex.retarget_value_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'updateState?_tablePagesSufficient' SQLeanite/ProofAxioms.lean &&
   grep -q 'CertifiedCandidates.result_exact' SQLeanite/ProofAxioms.lean; then
  ok "proof-carrying certified indexes survive state transitions without table scans"
else
  fail "the certified index path detached from lookup or maintenance proofs"
fi

if grep -q 'reuseFreedRoot under freed' \
     SQLeanite/PersistentPageTree.lean &&
   grep -q 'allocatedTree.reuseFresh? nextPage deleted.2' \
     SQLeanite/CoreChunkPageDelta.lean &&
   grep -q 'Store.reuseFresh?_toList' SQLeanite/ProofAxioms.lean &&
   grep -q 'table.IdentityWellFormed' \
     SQLeanite/CoreChunkPageDelta.lean &&
   grep -q 'updateState?_identityWellFormed' \
     SQLeanite/ProofAxioms.lean; then
  ok "localized deletion keeps active and freed page identities disjoint"
else
  fail "localized deletion detached from its physical identity invariant"
fi

if grep -q 'CoreChunkPageDelta.updateStateCandidate?' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'prepareAppendedIndex? validated input delta' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'certifyIndexEncoding? rootPage after index' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'prepareLocalizedLastIndex? validated' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'unless indexTailMatches source entry.rootPage prior.value.pages' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'CoreFileAdapter.indexTailMatches_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'commitLocalizedCertified connection.syncOps' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'certifyIndexEncoding?_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'replaceBetween?_sameData' SQLeanite/ProofAxioms.lean &&
   grep -q 'updateStateCandidate?_identityWellFormed' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'def packSized' SQLeanite/CellPagination.lean &&
   grep -q 'packSized current (encodedSize current) rest' \
     SQLeanite/CellPagination.lean &&
   grep -q 'CellPagination.fastFit_iff' SQLeanite/ProofAxioms.lean; then
  ok "new and shrinking indexes use certified localized encoding"
else
  fail "new or changed-index localization detached from its encoding proofs"
fi

if grep -q 'current.retarget? delta sufficient' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'ValidatedOpenState.retarget?_indexImage' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'let (validated, _) ← CoreFileAdapter.commit' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'prepareBulkCommit? oldImage new' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'PreparedBulkCommit.postImageCertificate' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'encodeBulkWithState_represents' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'verifyWrittenPages paths.main writes' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'changedPageWrites oldTail' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'omitted_changedPageWrites_matches' \
     SQLeanite/ProofAxioms.lean; then
  ok "commits retain one validated state and omit byte-identical index pages"
else
  fail "commit validation or localized index filtering detached from its proofs"
fi

if ! grep -q 'after.find? fun row => !before.any' \
     SQLeanite/CoreChunkPageDelta.lean &&
   ! grep -q 'before.find? fun row => !after.any' \
     SQLeanite/CoreChunkPageDelta.lean &&
   grep -q 'firstInserted_mem_after' SQLeanite/ProofAxioms.lean &&
   grep -q 'firstDeleted_mem_before' SQLeanite/ProofAxioms.lean; then
  ok "bulk row differencing uses proved linear ordered merges"
else
  fail "bulk row differencing regressed to nested scans or lost its proof"
fi

if grep -q 'certifyWideIntegerIndex source fuel' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'certifyAllValueIndex source fuel' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'CertifiedAllValueIndex.valueEntries_exact' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CertifiedAllValueIndex.rangeEntries_exact' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'IntegerIndexRouting.valueEntries_exact' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'IntegerIndexRouting.rangeEntries_exact' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'decodeWideAbstractIndexTreeFrom_toList' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'decodeWideAbstractIndexTreeFrom' SQLeanite/CoreDecode.lean; then
  ok "wide and mixed C-produced indexes retain exact query certificates"
else
  fail "general index certification detached from the live connection"
fi

if grep -q 'CoreOptimizerBridge.optimize tableName query' SQLeanite/CoreFileEngine.lean &&
   grep -q 'CoreOptimizerBridge.optimize tableName query' SQLeanite/CoreWALFileEngine.lean &&
   grep -q 'QuerySemantics.optimizePlan' SQLeanite/CoreOptimizerBridge.lean &&
   grep -q 'QuerySemantics.unionDistribution' SQLeanite/CoreOptimizerBridge.lean &&
   grep -q 'unionDistribution' SQLeanite/Optimizer.lean; then
  ok "rollback and WAL SELECTs execute the proved denotational optimizer pipeline"
else
  fail "a live Core SELECT path bypasses the denotational optimizer"
fi

if grep -q 'def rewriteRoot (plan : Plan)' SQLeanite/Optimizer.lean &&
   grep -q 'projectionElimination (constantFolding plan)' \
     SQLeanite/Optimizer.lean &&
   grep -q 'rewriteRoot_cost_le' SQLeanite/ProofAxioms.lean &&
   grep -q 'optimizePlan_cost_le' SQLeanite/ProofAxioms.lean &&
   grep -q 'filterFusion_not_unconditionally_cost_safe' \
     SQLeanite/ProofAxioms.lean; then
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
       grep -q "${rewrite}_cost_le" SQLeanite/ProofAxioms.lean; then
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
             SQLeanite/ProofAxioms.lean; then
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

if grep -q 'innerJoin_true_eval' SQLeanite/ProofAxioms.lean &&
   grep -q 'permute_eval' SQLeanite/ProofAxioms.lean &&
   grep -q 'permute_symm_eval' SQLeanite/ProofAxioms.lean; then
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
     SQLeanite/CoreReadSemantics.lean &&
   grep -q 'RelationalAlgebra.permute (columnBijection perm)' \
     SQLeanite/CoreReadSemantics.lean &&
   grep -q 'queryDenotation' SQLeanite/CoreReadSemantics.lean &&
   grep -q 'ofList_map_permute' SQLeanite/ProofAxioms.lean &&
   grep -q 'permuted_projection_denotes' SQLeanite/ProofAxioms.lean; then
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
   grep -q 'no-primary-key|reject|' scripts/run-reverse-differential.sh; then
  ok "out-of-scope file shapes are declared and checked to fail closed"
else
  fail "an out-of-scope file shape lost its fail-closed declaration"
fi

if grep -q 'overflow-chain|' scripts/run-reverse-differential.sh &&
   grep -q 'auto-vacuum|' scripts/run-reverse-differential.sh &&
   grep -q 'post-vacuum|' scripts/run-reverse-differential.sh &&
   grep -q 'freelist-after-delete|' scripts/run-reverse-differential.sh &&
   grep -q 'multipage-interior|' scripts/run-reverse-differential.sh &&
   grep -q 'wal-mode|' scripts/run-reverse-differential.sh &&
   grep -q 'real-values|' scripts/run-reverse-differential.sh &&
   grep -q 'blob-values|' scripts/run-reverse-differential.sh; then
  ok "reverse corpus covers every file feature claimed as accepted"
else
  fail "a file feature is claimed as accepted with no reverse-direction cell"
fi

if [ -f docs/COMPATIBILITY.md ] &&
   scripts/run-reverse-differential.sh --markdown > "$scratch_parity" 2>/dev/null &&
   cmp -s "$scratch_parity" docs/COMPATIBILITY.md; then
  ok "generated compatibility document is current"
else
  fail "docs/COMPATIBILITY.md is stale; regenerate with --markdown"
fi

# Every shrink/refill image must now be clean; keep both strict runners wired.
if grep -q 'regress-page-reclaim.sh' scripts/reproduce-all.sh &&
   grep -q 'run-forward-compat.sh' scripts/reproduce-all.sh &&
   grep -q 'empty image failed integrity_check' scripts/regress-page-reclaim.sh &&
   ! grep -q 'orphan_bound' scripts/regress-page-reclaim.sh &&
   ! grep -q 'excepted=' scripts/run-forward-compat.sh; then
  ok "indexed page reclamation requires clean images after every phase"
else
  fail "strict page-reclamation checks or their runners are missing"
fi

# The one assumed law is disclosed as *checkable*, and that claim rests entirely on
# `TextRoundtrips` having a `Decidable` instance. If the instance disappears, the
# assumption silently becomes irreducible and TRUST.md is overstating.
if grep -q 'instance (value : String) : Decidable (TextRoundtrips value)' \
     SQLeanite/CoreDecode.lean &&
   grep -q 'def UTF8Roundtrips' SQLeanite/CoreDecode.lean &&
   grep -q 'per-string check at the boundary' docs/TRUST.md; then
  utf8_sites=$(rg -c '\(utf8 : (CoreDecode\.)?UTF8Roundtrips\)' -g '*.lean' \
    SQLeanite/ | awk -F: '{s+=$2} END {print s+0}')
  if grep -q "$utf8_sites hypothesis positions" docs/TRUST.md; then
    ok "the assumed UTF-8 law is decidable and its $utf8_sites sites are counted"
  else
    fail "TRUST.md's UTF-8 site count is stale: tree says $utf8_sites"
  fi
else
  fail "the assumed UTF-8 law lost its decidability or its disclosure"
fi

# `PostImageCertificate` must stay constructive. A new constructor that accepts a
# bare decoder equation would turn the crash theorem's post-image premise into an
# assumption, which is exactly what its docstring forbids.
post_image_block=$(awk '
  /^inductive PostImageCertificate/ { inside = 1 }
  inside { print }
  inside && /^$/ { inside = 0 }
' SQLeanite/CoreDurability.lean)
post_image_constructors=$(printf '%s\n' "$post_image_block" | grep -c '^  | ')
if ! grep -q 'no constructor accepting an opaque decoder equation' \
       SQLeanite/CoreDurability.lean; then
  fail "PostImageCertificate lost the docstring stating its design rule"
elif printf '%s\n' "$post_image_block" | grep -q 'CoreDecode.decode'; then
  fail "a PostImageCertificate constructor accepts a decoder equation"
elif [ "$post_image_constructors" -ne 5 ]; then
  fail "PostImageCertificate has $post_image_constructors constructors, expected 5"
else
  ok "PostImageCertificate stays constructive across all 5 alternatives"
fi

# The write side must reach the same bag algebra the read side denotes into, and
# it must reach it through the *same* abstraction function -- two abstractions
# would make the write and read statements incomparable, which is precisely the
# gap this closes. `coreRow` is the shared one.
if grep -q 'CoreReadSemantics.coreRow' SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'KRelation.single' SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'execute_insert_denotes' SQLeanite/ProofAxioms.lean &&
   grep -q 'tableDenotation_orderedUpsert_fresh' SQLeanite/ProofAxioms.lean; then
  ok "live INSERT reaches the bag algebra through the read side's abstraction"
else
  fail "the write side has no bag denotation, or uses a second abstraction"
fi

# The round trip has to be reachable from SQL text at both ends, or it presumes a
# parser step the executable does not perform.
if grep -q 'insertText_bytes_reopen_readText_denotes' \
     SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'CoreSQL.execute state insertText' SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'CoreSQL.execute { database := reopened } readText' \
     SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'CorePageCodec.encodeBulk' SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'CoreDecode.decode image.fileBytes' \
     SQLeanite/CoreWriteSemantics.lean &&
   grep -q 'insertText_bytes_reopen_readText_denotes' SQLeanite/ProofAxioms.lean; then
  ok "write text, bytes, reopen and read text compose into one audited theorem"
else
  fail "the write/read round trip is not reachable from live SQL text"
fi

# Freshness is what separates INSERT from REPLACE at the denotation level. If it
# stops being carried, the bag statement silently weakens to replace-then-union.
if grep -q 'existing.rowid.value ≠ row.rowid.value' SQLeanite/CoreEngine.lean &&
   grep -q 'existing.rowid.value ≠ row.rowid.value' SQLeanite/CoreEndToEnd.lean &&
   grep -q 'existing.rowid.value ≠ row.rowid.value' SQLeanite/CoreWriteBytes.lean; then
  ok "INSERT carries rowid freshness from the table through to the byte level"
else
  fail "rowid freshness is checked but not carried into the postcondition"
fi

# The parity artifact is generated from the audit, so a witness that is renamed,
# deleted or dropped from `ProofAxioms.lean` makes the table stale and this fails.
# A hand-maintained parity table is exactly the kind of claim that rots quietly.
if scripts/popl-parity.sh --check > "$scratch_parity" 2>&1; then
  ok "$(cat "$scratch_parity")"
else
  cat "$scratch_parity" >&2
  fail "POPL parity table is stale or names an unaudited witness"
fi

# The bridge must be about the same projection the executor runs, not a copy of
# it: `permuted_projection_denotes` is stated over `Core.Query.projectedRows`
# through `query_eval_denotes`, which is the same route `execute_query_denotes`
# takes. If the executor's projection stops going through `Query.projectedRows`,
# this pins that the bridge has to move with it.
if grep -q 'query.columns.map row.value' SQLeanite/CoreEngine.lean &&
   grep -q 'permutedColumns_map_value' SQLeanite/CoreReadSemantics.lean &&
   grep -q 'Core.Query.projectedRows' SQLeanite/CoreReadSemantics.lean; then
  ok "permutation bridge is stated over the executor's own projection"
else
  fail "permutation bridge drifted from the live Query.projectedRows"
fi

if grep -q 'execute_query_denotes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_join_denotes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_group_denotes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_count_denotes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_sum_denotes' SQLeanite/ProofAxioms.lean &&
   grep -q 'execute_extreme_denotes' SQLeanite/ProofAxioms.lean &&
   grep -q 'compound_denotes' SQLeanite/ProofAxioms.lean; then
  ok "every live Core read form reaches the multiplicity denotation"
else
  fail "a live Core read form is detached from the relational semantics"
fi

if grep -q 'where_\.leftOnly = true' SQLeanite/CoreJoin.lean &&
   grep -q 'left\.rows\.filter (selectsLeft where_)' SQLeanite/CoreJoin.lean &&
   grep -q 'matchingRows_pushLeft' SQLeanite/ProofAxioms.lean &&
   grep -q 'leftOuterRows_pushLeft' SQLeanite/ProofAxioms.lean; then
  ok "live inner and left-outer joins use proved preserved-side pushdown"
else
  fail "the live join planner detached from safe left-predicate pushdown"
fi

if grep -q 'CoreOptimizerBridge.optimizeJoin leftTable rightTable query' \
     SQLeanite/CoreSQL.lean &&
   grep -q 'def innerJoinPlan' SQLeanite/CoreOptimizerBridge.lean &&
   grep -q 'def leftOuterJoinPlan' SQLeanite/CoreOptimizerBridge.lean &&
   grep -q 'symbolicLeftOnPlan' SQLeanite/CoreOptimizerBridge.lean &&
   grep -q 'symbolicLeftWherePlan' SQLeanite/CoreOptimizerBridge.lean &&
   grep -q 'optimize_innerJoinPlan_eval' SQLeanite/ProofAxioms.lean &&
   grep -q 'optimize_leftOuterJoinPlan_eval' SQLeanite/ProofAxioms.lean &&
   grep -q 'optimizeJoin_eval' SQLeanite/ProofAxioms.lean; then
  ok "live inner and width-aware left joins execute the denotational optimizer"
else
  fail "live joins bypass or detached from denotational refinement"
fi

if grep -q 'CoreOptimizerBridge.optimizeCompoundOp operation' \
     SQLeanite/CoreSQL.lean &&
   grep -q 'CoreCompound.combine operation left right' \
     SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.combineRows_denotes' SQLeanite/ProofAxioms.lean &&
   grep -q 'optimizeCompoundOp_eq' SQLeanite/ProofAxioms.lean; then
  ok "live compound SELECTs execute the SQL-key bag refinement and operator optimizer"
else
  fail "live compound SELECTs bypass or detached from denotational refinement"
fi

if ! grep -q 'CellPagination.paginateCells' SQLeanite/CoreOverflow.lean &&
   grep -q 'RecursivePageBTree.IndexStore' SQLeanite/CoreOverflow.lean &&
   grep -q 'provisional.retarget? resolved.cells' \
     SQLeanite/CoreOverflow.lean &&
   grep -q 'IndexStore.retarget?_pageCount' SQLeanite/ProofAxioms.lean &&
   grep -q 'IndexStore.retarget?_represents' SQLeanite/ProofAxioms.lean; then
  ok "index encoding retains one proof-carrying page topology"
else
  fail "index encoding re-chunks or detached from its topology proofs"
fi

if grep -q 'CoreFileAdapter.loadOpenState paths' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'CorePageLoad.openGenerated? source' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'CoreDecode.rebuildCanonicalDatabase base.tables indexEntries' \
     SQLeanite/CorePageLoad.lean &&
   grep -q 'loadOpenTables? source tableEntries' \
     SQLeanite/CorePageLoad.lean &&
   grep -q 'retargetOpenTables? initialStates database.tables' \
     SQLeanite/CorePageLoad.lean &&
   grep -q 'CorePageLoad.open?_represents' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CorePageLoad.openGenerated?_represents' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreDecode.rebuildCanonicalDatabase_overflowEncoded' \
     SQLeanite/ProofAxioms.lean; then
  ok "generated write opens validate tables once and restore proved index metadata"
else
  fail "the write opener detached from its proof-carrying combined loader"
fi

if grep -q 'CoreLazyFileEngine.execute? paths sql' Main.lean &&
   grep -q 'CoreFileAdapter.lookupPrimaryRowDecision paths tableName rowid' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'CoreDecode.lookupTableRowidIOFrom schema source rowid' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'CoreFile.hasGeneratedImageStamp header' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'encodeBulk_generatedHeader' SQLeanite/ProofAxioms.lean &&
   grep -q 'lookupTableRowidWith source.readPage' SQLeanite/CoreDecode.lean &&
   grep -q 'lookupTableRowidWith (m := Id)' SQLeanite/CoreDecode.lean; then
  ok "foreign primary fallback retains the reference page traversal and provenance checks"
else
  fail "the cold primary-key path detached from traversal or provenance proof"
fi

if grep -q 'CoreFileAdapter.lookupGeneratedPrimaryRowWith generated paths' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'cursor.seek target fuel' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'Runtime.Record.readRowWithSource schema source cell' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'Runtime.ReadPager.ofPath' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'let some page ← cursor.pager.get pageNumber' \
     SQLeanite/Runtime/TableCursor.lean &&
   grep -q 'CoreDecode.decodeRowCellIOFrom schema source' \
     SQLeanite/Runtime/Record.lean; then
  ok "generated reads use pager/cursor/record layers (runtime boundary, not a refinement proof)"
else
  fail "generated read layers detached from the shipped path"
fi

if grep -q 'let index := view.lowerBound target' SQLeanite/Runtime/TableCursor.lean &&
   grep -q 'pageNumber (some cache.tableViews)' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'let some view := TablePage.decode? page' SQLeanite/Runtime/TableCursor.lean &&
   grep -q 'if ordered : CheckedOrder.adjacent' SQLeanite/Runtime/TablePage.lean &&
   grep -q 'LowerBound.search' SQLeanite/Runtime/TablePage.lean &&
   grep -q 'encodedSize record = cell.payloadSize.val' SQLeanite/Runtime/Record.lean &&
   grep -q '(source.pageCount + 1) cell.input' SQLeanite/Runtime/Record.lean &&
   grep -q '^#print axioms SQLeanite.Runtime.TablePage.View.lowerBound_eq_linear' SQLeanite/ProofAxioms.lean &&
   grep -q '^#print axioms SQLeanite.Runtime.TablePage.View.lowerBound_present' SQLeanite/ProofAxioms.lean &&
   grep -q '^#print axioms SQLeanite.Runtime.Record.decodeRowCell_eq_reference' SQLeanite/ProofAxioms.lean &&
   grep -q '^#print axioms SQLeanite.Runtime.Record.readRowWithSource_eq_reference' SQLeanite/ProofAxioms.lean; then
  ok "checked binary search and allocation-free size validation use audited refinements"
else
  fail "SQLite-style page/record algorithms detached from their checked premises or proofs"
fi

if grep -q 'lookupGeneratedPrimaryRange' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'CoreDecode.lookupTableRangeIOFrom schema source' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'tableRangeCandidatesWith source.readPage' \
     SQLeanite/CoreDecode.lean &&
   grep -q 'tableRangeCandidatesWith (m := Id)' SQLeanite/CoreDecode.lean &&
   grep -q 'lookupTableRangeFrom_encodeChunkNodeWithOverflow_exact' \
     SQLeanite/ProofAxioms.lean; then
  ok "cold primary ranges use exact separator-directed traversal"
else
  fail "the cold primary-range path detached from its shared proved traversal"
fi

if grep -q 'lookupGeneratedIndexCandidates' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'PageReadCache.create' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'query (some cache)' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'preadPageSourceCached paths.main count cache' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'executeReadStatements? paths statementList' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'Core.Index.isImplicitPrimary schema' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'CanonicalIndexSQL.parseGeneratedCertified' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'CoreFile.hasGeneratedImageStamp header' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'lookupIndexValueIOFrom source value' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'lookupIndexRangeIOFrom source operation value' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'lookupTableRowidIOFrom schema source' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'lookupIndexValueFrom_encodeIndex_exact' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'lookupIndexValueFrom_text_encodeIndex_exact' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'lookupIndexRangeFrom_encodeIndex_exact' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'implicitPrimaryIndexes_areImplicit' \
     SQLeanite/ProofAxioms.lean; then
  ok "cold read batches cache raw pages and use exact generated-index traversal"
else
  fail "the cold generated-index path detached from provenance or exactness"
fi

if grep -q 'lookupGeneratedOrderedPrefix paths' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'lookupIndexPrefixIOFrom source limit' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'indexPrefixWith source.readPage' SQLeanite/CoreDecode.lean &&
   grep -q 'indexPrefixWith (m := Id) source.readPage' SQLeanite/CoreDecode.lean &&
   grep -q 'indexPrefixFrom_text_encodeIndex_exact' \
     SQLeanite/ProofAxioms.lean; then
  ok "cold ORDER BY LIMIT uses a proved multi-leaf index cursor"
else
  fail "the cold ORDER BY prefix detached from its shared exact traversal"
fi

if grep -q 'lookupGeneratedPrimaryJoin paths' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'CoreDecode.decodeSubtreeRowsIOFrom rightSchema source' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'CoreDecode.lookupTableRangeIOFrom leftSchema' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'evalPrimaryKeyCandidates' \
     SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'evalPrimaryKeyCandidates_eq_eval' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'lookupTableRangeFrom_encodeChunkNodeWithOverflow_exact' \
     SQLeanite/ProofAxioms.lean; then
  ok "cold primary-key joins use a complete bounded-left merge"
else
  fail "the cold primary-key join detached from range or semantic exactness"
fi

if grep -q 'table.rows.mergeSort (integerIndexRowLe index)' \
     SQLeanite/CoreFile.lean &&
   grep -q 'table.rows.mergeSort (textIndexRowLe index)' \
     SQLeanite/CoreFile.lean &&
   grep -q 'CoreFile.sortedIndexRows table index' \
     SQLeanite/CoreOverflow.lean &&
   grep -q 'integerIndexRowLe_trans' SQLeanite/ProofAxioms.lean &&
   grep -q 'textIndexRowLe_trans' SQLeanite/ProofAxioms.lean &&
   grep -q 'expectedIndexEntries_eq_sortSource' \
     SQLeanite/ProofAxioms.lean; then
  ok "physical INTEGER/TEXT indexes use proved merge-sort paths"
else
  fail "physical index encoding detached from its proved fast ordering"
fi

if grep -q 'preparePageDirectedIndexDelete? validated' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'deleteIndexEntriesBatch?' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'let (cell, rest) ← takeExact cellLength input' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'let certified ← certifyDecodedIndexAt? entry.rootPage' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'localizedIndexReadable_of_onStorage' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'deletedRowsOrdered?_length' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreFileAdapter.takeExact_spec' SQLeanite/ProofAxioms.lean &&
   grep -q 'certifyDecodedIndex?_exact' SQLeanite/ProofAxioms.lean; then
  ok "indexed bulk DELETE carries an exact decoded post-state certificate"
else
  fail "page-directed indexed DELETE detached from its physical certificate"
fi

if grep -q 'let source := byteArrayPageSource input count' \
     SQLeanite/CoreFileAdapter.lean &&
   ! sed -n '/def loadOpenState/,/structure CertifiedIndexEncoding/p' \
      SQLeanite/CoreFileAdapter.lean | grep -q 'CoreDecode.pages'; then
  ok "validated write-open reads pages directly from the file buffer"
else
  fail "validated write-open regressed to whole-file list pagination"
fi

if grep -q 'preparePageDirectedIndexInsert? validated' \
     SQLeanite/CoreFileEngine.lean &&
   grep -q 'insertIndexEntryNoSplit?' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'let certified ← certifyDecodedIndexAt? entry.rootPage' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'localizedIndexReadable_of_onStorage' \
     SQLeanite/ProofAxioms.lean &&
   grep -q 'firstInserted_mem_after' SQLeanite/ProofAxioms.lean &&
   grep -q 'certifyDecodedIndex?_exact' SQLeanite/ProofAxioms.lean; then
  ok "single-row indexed INSERT carries an exact decoded post-state certificate"
else
  fail "page-directed indexed INSERT detached from its physical certificate"
fi

# 6. The binary must really produce a SQLite file the C implementation accepts.
if [ -x .lake/build/bin/sqleanite ] && [ -x "$sqlite_bin" ]; then
  tmp=$(mktemp -d)
  printf 'CREATE TABLE t(id INTEGER PRIMARY KEY, v);\nINSERT INTO t VALUES(1,%s);\n' "'x'" > "$tmp/s.sql"
  .lake/build/bin/sqleanite --verified-file "$tmp/db" "$tmp/s.sql" >/dev/null 2>&1 || fail "sqleanite could not write a database"
  if [ "$("$sqlite_bin" "$tmp/db" 'PRAGMA integrity_check;' 2>&1)" = "ok" ]; then
    ok "C sqlite3 accepts a Lean-written file"
  else
    fail "C sqlite3 rejected a Lean-written file"
  fi
  {
    printf 'CREATE TABLE d(id INTEGER PRIMARY KEY, v);\n'
    printf 'CREATE INDEX d_v ON d(v);\nBEGIN;\n'
    i=1
    while [ "$i" -le 60 ]; do
      printf "INSERT INTO d VALUES(%s,'v-%s');\n" "$i" "$((i % 7))"
      i=$((i + 1))
    done
    printf 'COMMIT;\n'
  } > "$tmp/delete-seed.sql"
  .lake/build/bin/sqleanite --verified-file "$tmp/delete-db" \
    "$tmp/delete-seed.sql" >/dev/null 2>&1 ||
      fail "sqleanite could not seed an indexed DELETE database"
  printf 'DELETE FROM d WHERE id > 40;\n' > "$tmp/delete.sql"
  .lake/build/bin/sqleanite --verified-file "$tmp/delete-db" \
    "$tmp/delete.sql" >/dev/null 2>&1 ||
      fail "page-directed indexed DELETE failed"
  delete_check=$("$sqlite_bin" -batch -noheader "$tmp/delete-db" \
    'PRAGMA integrity_check; SELECT count(*) FROM d; SELECT count(*) FROM d INDEXED BY d_v;' 2>&1)
  if [ "$delete_check" = "ok
40
40" ]; then
    ok "page-directed indexed DELETE is integrity-check clean"
  else
    fail "C sqlite3 rejected the page-directed indexed DELETE"
  fi
  printf "INSERT INTO d VALUES(100,'v-1');\n" > "$tmp/insert.sql"
  .lake/build/bin/sqleanite --verified-file "$tmp/delete-db" \
    "$tmp/insert.sql" >/dev/null 2>&1 ||
      fail "page-directed indexed INSERT failed"
  insert_check=$("$sqlite_bin" -batch -noheader "$tmp/delete-db" \
    "PRAGMA integrity_check; SELECT count(*) FROM d; SELECT count(*) FROM d INDEXED BY d_v WHERE v='v-1';" 2>&1)
  if [ "$insert_check" = "ok
41
7" ]; then
    ok "page-directed indexed INSERT is integrity-check clean"
  else
    fail "C sqlite3 rejected the page-directed indexed INSERT"
  fi
  printf 'INSERT INTO t VALUES(2,%s);\n' "'y'" > "$tmp/write.sql"
  chmod 444 "$tmp/db"
  if .lake/build/bin/sqleanite --verified-file "$tmp/db" "$tmp/write.sql" \
      >"$tmp/readonly.out" 2>"$tmp/readonly.err"; then
    fail "sqleanite wrote a read-only database"
  elif grep -q '^Error: attempt to write a readonly database$' \
      "$tmp/readonly.err" &&
      ! grep -q 'uncaught exception' "$tmp/readonly.err"; then
    ok "read-only writes produce an ordinary SQLite-style diagnostic"
  else
    fail "read-only write diagnostic was misleading"
  fi
  chmod 644 "$tmp/db"
  printf x > "$tmp/bad"
  if .lake/build/bin/sqleanite --verified-file "$tmp/bad" </dev/null \
      >"$tmp/bad.out" 2>"$tmp/bad.err"; then
    fail "sqleanite accepted a corrupt database"
  elif grep -q '^Error: invalid general MVP SQLite image:' "$tmp/bad.err" &&
      ! grep -q 'uncaught exception' "$tmp/bad.err"; then
    ok "corrupt input rejection is a normal diagnostic, not a crash"
  else
    fail "corrupt input rejection still looks like an uncaught crash"
  fi
  rm -r -- "$tmp"
else
  printf 'skip - binary or configured SQLite reference unavailable\n'
fi

exit $status
