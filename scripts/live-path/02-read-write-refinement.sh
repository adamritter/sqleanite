# Sourced by live-path-check.sh; shares its failure status and scratch files.

# Constant expressions use the pure scalar layer on the production translator.
if grep -q 'SQLite.Scalar.admitted expression' SQLeanite/SQLSurface.lean &&
   grep -q 'value (← SQLite.Scalar.eval expression)' SQLeanite/SQLSurface.lean &&
   grep -q 'SQLSurface.literal expression' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'executeConstantSelect state select' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'private def formatFloat : Float → String := SQLite.FloatCodec.render' SQLeanite/Value.lean &&
   grep -q 'let value := SQLite.FloatCodec.decimalToBinary' SQLeanite/Value.lean &&
   grep -q 'SQLite.FloatCodec.multiply128_reconstruct' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'SQLite.Numeric.integerPrefix_bounds' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'SQLite.Scalar.add_integer_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.executeConstantSelect_preserves_state' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "pure SQLite scalar layer and constant SELECT are wired into Core SQL"
else
  fail "scalar layer detached from the live translator or its proofs"
fi

if grep -q '"round", \[v, places\].*roundValue v places' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'FloatCodec.renderFixed r n' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Scalar.roundPrecision_le' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "round uses the pure fixed-decimal codec and bounded precision"
else
  fail "round detached from its implementation or precision theorem"
fi

if grep -q 'Pattern.evaluate false b a' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Pattern.evaluate true b a' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Pattern.matches_empty' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "LIKE and GLOB use the pure pattern matcher on the live scalar path"
else
  fail "pattern matching detached from its implementation or component proofs"
fi

if grep -q 'table.uniqueConflict row' "$audit_sources/SQLeanite/Core.lean" &&
   grep -q 'table.uniqueConflict patched true' "$audit_sources/SQLeanite/Core.lean" &&
   grep -q 'replaceUniqueRows state tableName' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CREATE UNIQUE INDEX' SQLeanite/CanonicalIndexSQL.lean &&
   grep -q 'Core.Table.insertValues_unique' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "UNIQUE metadata and constraints are on the Core write path"
else
  fail "UNIQUE constraints detached from production writes or their proof"
fi

if grep -q 'prepareCreateTable state name ifNotExists' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'prepareCreateIndex state name ifNotExists' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q '!CoreSQL.schemaNoop current statement' SQLeanite/CoreFileEngine.lean &&
   grep -q '!CoreSQL.schemaNoop state statement' SQLeanite/CoreWALFileEngine.lean &&
   grep -q 'CoreSQL.executeStatement_createTable_noop' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.executeStatement_createIndex_noop' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "schema admission and IF NOT EXISTS no-ops preserve the live file paths"
else
  fail "schema no-op guards detached from execution or persistence"
fi

if grep -q 'notNull := integerAlias || column.notNull' SQLeanite/CoreSchemaTranslate.lean &&
   grep -q '| none | some .null => .rowid row.rowid' "$audit_sources/SQLeanite/CoreData.lean" &&
   grep -q 'Core.Row.declaredKey_null_ne_nonnull' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'TEXT PRIMARY KEY NOT NULL' "$audit_sources/SQLeanite/CanonicalSchemaSQL.lean" &&
   grep -q 'conflict == .replace && hasReplaceKeys stored' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'replacing && hasReplaceKeys stored' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'Core.Row.declaredKey_null_injective' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "nullable TEXT keys preserve distinct NULLs, declared NOT NULL and REPLACE allocation"
else
  fail "nullable TEXT key constraints or REPLACE allocation detached from the live path"
fi

if [ "$(grep -c 'ascendingCellPointers (cellCount - 1) contentStart remaining' "$audit_sources/SQLeanite/CoreDecode.lean")" -eq 4 ] &&
   grep -q 'CoreDecode.ascendingCellPointers_leafPointers' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreDecode.ascendingCellPointers_next' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "packed schema, row and index decoders check the whole pointer ordering"
else
  fail "packed-page recognition lost its whole-pointer ordering guard"
fi

if grep -F -q 'let definitions ← tablePrimaryColumns definitions (constraints.filter (·.primaryKey))' SQLeanite/CoreSchemaTranslate.lean &&
   grep -q 'matchTablePrimary constraint' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'collations := collations.push collation' "$audit_sources/SQLeanite/Parser.lean" &&
   grep -q 'descending := descending.push desc' "$audit_sources/SQLeanite/Parser.lean" &&
   grep -q 'CoreSQL.markPrimaryColumn_names' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.tablePrimaryColumns_empty' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'match insertValueIndex schema.primaryKey targetIndex indices' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.insertValueIndex_rowid' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "table PRIMARY KEY syntax retains metadata and lowers through checked Core schemas"
else
  fail "table-key metadata or checked lowering detached from the live path"
fi

if grep -q 'inputRowValues schema columns evaluateAll' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'rows.toList (1 < rows.size)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'ctx projection inputs evaluateAll' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.inputRowValues stored.schema columns (1 < rows.size)' "$audit_sources/SQLeanite/CoreSQLWriteText.lean" &&
   grep -q 'CoreSQL.evaluateInsertExpressions_evaluated' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.inputRowValues_single' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "multi-VALUES source evaluation reaches all insert policies and RETURNING with matching trace premises"
else
  fail "multi-VALUES evaluation mode detached from insertion or its proof boundary"
fi

if grep -q 'integerPrimaryNotNull := integerAlias && column.notNull' SQLeanite/CoreSchemaTranslate.lean &&
   grep -q 'if column.integerPrimaryNotNull then " INTEGER PRIMARY KEY NOT NULL"' "$audit_sources/SQLeanite/CanonicalSchemaSQL.lean" &&
   grep -q 'integerPrimaryKey := true, integerPrimaryNotNull := true' "$audit_sources/SQLeanite/CanonicalSchemaSQL.lean" &&
   grep -q 'CanonicalSchemaSQL.parseBaseColumn_integerNotNull_append' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "declared INTEGER key NOT NULL metadata survives canonical print and parse"
else
  fail "declared INTEGER key nullability detached from the schema codec"
fi

# Text/blob helpers must be called from the production scalar evaluator.
if python3 scripts/check_module_boundaries.py --reaches SQLeanite.SQLite.Scalar SQLeanite.SQLite.Text &&
   grep -q 'SQLite.Text.substr v start count' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'SQLite.Text.unhex v ignored' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'SQLite.Text.slice_length_le' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'SQLite.Text.minmax_null' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "pure text/blob functions are wired into scalar evaluation and proof audit"
else
  fail "text/blob functions detached from the live scalar path or its proofs"
fi

if grep -q 'CoreExpr.Context' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'executeExpressionSelect state select source stored wherePredicate' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'SQLite.Scalar.evalTypedQueryWith' SQLeanite/CoreExpr.lean &&
   grep -F -q 'ctx.scalarQuery.map (fun execute => execute row)' SQLeanite/CoreExpr.lean &&
   grep -q 'CoreExpr.projectRow_width' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "row projections use explicit bindings, shared scalar evaluation and audited result widths"
else
  fail "row expressions detached from the production evaluator or width proof"
fi

if grep -q 'limitRows query.limit (stableDistinctBy distinctRowKey projected)' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'orderedLimit (Core.stableDistinctBy' "$audit_sources/SQLeanite/CoreReadSemantics.lean" &&
   grep -q 'Core.Query.eval_distinct_limit' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'Core.Query.eval_distinct_key_nodup' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'Core.stableDistinctBy' SQLeanite/CoreExpr.lean; then
  ok "DISTINCT precedes LIMIT on the live Core query and its bag denotation"
else
  fail "DISTINCT/LIMIT implementation detached from its corrected denotation"
fi

if grep -q 'CoreCompound.combine operation left right' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.combineRows_denotes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'distinctRowKey row' SQLeanite/CoreCompound.lean; then
  ok "SQL compounds use numeric keys and the live key-bag refinement"
else
  fail "SQL compound equality detached from its typed set-operation proof"
fi

if grep -q 'distinctRowKey (query.originalKey row)' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'query.outputKey rows key' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'GroupQuery.representative_key' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "GROUP BY compares numeric keys and retains a proved source representative"
else
  fail "GROUP BY numeric equivalence or original representative is detached"
fi

# 5. Functions that carry the headline proofs must be reachable from the CLI.
#    Checked structurally: the executor must call the planner, and Main must
#    route --verified-file into the Core engine.
if grep -q 'query.eval (table.plannedRows query)' "$audit_sources/SQLeanite/CoreEngine.lean"; then
  ok "executor runs Table.plannedRows"
else
  fail "the executor no longer runs the proved index planner"
fi

if grep -q 'table.insertValues values' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'table.replaceValues values' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'table.findRowid? row.rowid' "$audit_sources/SQLeanite/Core.lean" &&
   grep -q 'table.rowTree.root.lookup rowid.treeKey' "$audit_sources/SQLeanite/Core.lean" &&
   grep -q 'table.rowTree.root.last?.map' "$audit_sources/SQLeanite/Core.lean" &&
   grep -q 'PersistentPageTree.Node.lookup_eq_erase' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'table.upsertGeneratedFresh row valid hidden' "$audit_sources/SQLeanite/Core.lean" &&
   grep -q 'Table.findDeclaredPrimary?_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'Table.upsertGeneratedFresh_rows' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'Table.findRowid?_eq_some_iff' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "executor uses proof-carrying Core INSERT/REPLACE and balanced TEXT-key routing"
else
  fail "Core INSERT/REPLACE bypasses their proof-carrying table operations"
fi

if grep -q 'table.retainRows fun row' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'table.patchRowid assignments rowid' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'table.updateWhere assignments predicate' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'table.patchRows assignments (selects predicate)' "$audit_sources/SQLeanite/CoreEngine.lean"; then
  ok "executor uses tree-local point UPDATE and validated general mutations"
else
  fail "Core DELETE/UPDATE bypasses their validated mutation paths"
fi

if grep -q 'execute_createTable_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_createIndex_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_insert_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_replace_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_deleteWhere_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_updateWhere_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_commit_exact' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "all seven write commands retain execute-level correspondence proofs"
else
  fail "a live write command detached from its execute-level theorem"
fi

if grep -q 'execute_createTable_to_bytes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_createIndex_to_bytes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_insert_to_bytes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_replace_to_bytes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_delete_to_bytes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_update_to_bytes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'execute_commit_to_bytes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'localized_state_represents_database' \
     "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "all seven write postconditions compose with SQLite bytes"
else
  fail "a live write command detached from its SQLite byte refinement"
fi

if grep -q 'comparisonPredicate schema' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'lexFast sql' SQLeanite/Lexer.lean &&
   grep -q 'lex_sound' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'parse_success_tokenizes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreTokenGrammar.parseCertified_sound' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreTokenGrammar.parseCertified_agrees_parse' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreTokenGrammar.Parses.grammar' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'ParsedSupportedText.tokenizes' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'ParsedSupportedText.grammar' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'literalSyntax_of_success' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'predicateSyntax_of_success' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'groupOutputSyntax_of_success' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'joinPredicateSyntax_of_success' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'parsedSupportedText_of_execute_success' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreTokenGrammar.parseCertified sql' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  ok "live Core translation carries independent proof-producing token grammar"
else
  fail "Core SQL translation detached from its grammar or text certificate"
fi

if grep -q 'rollbackCommit_core_crash_atomic' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'rollbackCommit_represents_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'rollbackCommit_core_returned_recovers_new' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'rollbackCommit_core_repeated_recovery_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'rollbackCommit_represents_recovery_crash_trace_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'rollbackCommit_padded_recovery_crash_trace_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'rollbackCommit_recovery_crash_trace_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreFreelistCodec.decode_paddedImage' \
     "$audit_sources/SQLeanite/CoreDurability.lean" &&
   grep -q 'CoreFileAdapter.commit_crash_atomic' \
     "$audit_sources/SQLeanite/CoreDurability.lean" &&
   grep -q 'CorePageCodec.decode_encodeBulk' \
     "$audit_sources/SQLeanite/CoreDurability.lean" &&
   grep -q 'decodeChecked_makeJournal_exact' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'PhysicalJournalCodec.encodePersistentActiveBytes journal' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'PhysicalJournalCodec.decodePersistent encoded.data.toList' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean"; then
  ok "rollback crash atomicity reaches concrete Core SQLite bytes"
else
  fail "Core database durability detached from the codec or journal theorem"
fi

if grep -q 'executeCommand_commit_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeCommand_returned_recovers_new' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeCommand_recovery_crash_trace_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreDurability.rollbackWrites_represents_crash_atomic' \
     SQLeanite/CoreEndToEnd.lean &&
   grep -q 'execute_write_exact command success' \
     SQLeanite/CoreEndToEnd.lean; then
  ok "all persisted Core commands compose with crash-atomic SQLite bytes"
else
  fail "Core write semantics detached from the durability composition"
fi

if grep -q 'executeText_commit_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_returned_recovers_new' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_recovery_crash_trace_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeStatement_eq_core translated' \
     "$audit_sources/SQLeanite/CoreSQLWriteText.lean" &&
   grep -q 'CoreEndToEnd.executeCommand_commit_crash_atomic' \
     "$audit_sources/SQLeanite/CoreSQLWriteText.lean" &&
   grep -q 'CoreDurability.PostImageCertificate' \
     "$audit_sources/SQLeanite/CoreSQLWriteText.lean" &&
   grep -q 'PostImageCertificate.representsDatabase' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreTokenGrammar.parseCertified sql' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  ok "supported SQL write text composes with crash-atomic SQLite bytes"
else
  fail "SQL text boundary detached from write durability"
fi

if grep -q 'executeText_insertRows_commit_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'insertRows_eq_runCoreCommands' "$audit_sources/SQLeanite/CoreSQLWriteText.lean" &&
   grep -q 'executeWriteCommands_exact' "$audit_sources/SQLeanite/CoreSQLWriteText.lean"; then
  ok "multi-row SQL write text composes with crash-atomic SQLite bytes"
else
  fail "multi-row SQL write refinement is detached from the live executor"
fi

if grep -q 'CoreSQLTraceText.executeText_commit_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQLTraceText.executeText_localized_commit_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_committedLocalizedIndexedSingle_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_committedLocalizedIndexedSingleOfRowsInline_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_committedLocalizedIndexedInlineTables_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_committedLocalizedIndexedSingleOfInlineTree_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_committedLocalizedIndexedSingleOfInlineRows_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_committedLocalizedIndexedSingleYCSB_crash_atomic' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CommittedLocalizedDelta.trace_eq_commitPlan' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'LocalizedRepresentation.representsDatabase' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'localizedRepresentation_of_certificates' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'sqliteHeaderMatches_of_pageZeroWrite' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'catalogRead_of_pageZeroWrite' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreLocalizedRepresentation.TablesDecode.mapM' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'IndexMetadataGroups.rebuild' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'applyIndexesForOpen_of_index_certificates' \
     "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'runStatements_eq_commands' "$audit_sources/SQLeanite/CoreSQLTraceText.lean" &&
   grep -q '| begin : TranslatedBlock' "$audit_sources/SQLeanite/CoreSQLTraceText.lean" &&
   grep -q '| rollback : TranslatedBlock' "$audit_sources/SQLeanite/CoreSQLTraceText.lean"; then
  ok "transactional SQL statement lists compose with crash recovery"
else
  fail "transactional SQL statement-list proof is detached"
fi

if grep -q 'executeText_read_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_count_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_sum_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_extreme_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_group_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_join_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_binary_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'executeText_compound_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'armsRefine armsTranslated' \
     "$audit_sources/SQLeanite/CoreSQLReadText.lean" &&
   grep -q 'CoreSQL.combineRows_denotes' \
     "$audit_sources/SQLeanite/CoreSQLReadText.lean" &&
   grep -q 'CoreReadSemantics.execute_query_denotes' \
     "$audit_sources/SQLeanite/CoreSQLReadText.lean" &&
   grep -q 'executeStatement_eq_core translated' \
     "$audit_sources/SQLeanite/CoreSQLReadText.lean" &&
   grep -q 'CoreTokenGrammar.parseCertified sql' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  ok "supported SQL read text reaches the independent bag denotation"
else
  fail "SQL text boundary detached from read denotation"
fi

if grep -q '| .primaryKey rowid => table.primaryKeyRows rowid' \
     "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'exact Query.eval_primaryKey table query rowid' \
     "$audit_sources/SQLeanite/CoreEngine.lean"; then
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

if grep -q 'CanonicalSchemaSQL.parse sql' SQLeanite/CoreCatalogSQL.lean; then
  ok "decoder uses the canonical schema recognizer"
else
  fail "the decoder no longer tries the proved canonical schema recognizer"
fi

# The general open must derive its page geometry from the validated header, not
# from the 4096-byte constant. It previously did this by passing `usable` to
# `filePageSourceFor`; it now strides a buffered read by physical page size,
# which is faster but just as easy to get wrong -- substituting the fixed-size
# `byteArrayPageSource` here silently broke the 1024-byte differential case, so
# both the positive and the negative check are asserted.
if grep -q 'let pageBytes := header.headerPrefix.pageSize' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   ! grep -q 'byteArrayPageSource whole count' \
     "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'catalogPage? source.usable.val pageNumber page' \
     "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'decodeTableLeafCell source.usable input' \
     "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'decodeLeafIndexCell source.usable input' \
     "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'headerUsablePageSize?_val' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "general opens carry the validated SQLite page size through decoding"
else
  fail "general opens detached from dynamic page-size validation"
fi

# Tuple targets and RHS values are replayed together and never truncated.
if grep -q 'SQLite.RowAssignment.bind names.toList values.toList' "$audit_sources/SQLeanite/Parser.lean" &&
   grep -q 'assignments.size ≤ SQLite.Limits.maxColumns' "$audit_sources/SQLeanite/Parser.lean" &&
   grep -q 'matchAssignmentNames ((name, expression) :: rest)' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'matchAssignmentValues ((← get).remaining.length + 1) expressions' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'SQLite.RowAssignment.bind_exact' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'SQLite.RowAssignment.bind_length' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "row-value UPDATE checks widths and replays each grouped name/value pair"
else
  fail "row-value UPDATE is disconnected from its checked lowering"
fi

# RETURNING disables one-pass UPDATE and preserves outputs of accepted rows.
if grep -q 'executeUpdateReturning state tableName alias stored assignments.toList where_ conflict returning' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreReturning.updatedOutput outputCtx cells projection outcome' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'updateReturningRows state tableName ctx outputCtx bound conflict projection rowids' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreReturning.updatedOutput_zero' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.updateReturningRow_missing' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.updateReturningRows_length_le' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'update table alias assignments where_ conflict returning' "$audit_sources/SQLeanite/CoreTokenGrammar.lean"; then
  ok "UPDATE RETURNING freezes selected rowids and materializes accepted new values"
else
  fail "UPDATE RETURNING is disconnected from checked row selection or output"
fi

# INSERT RETURNING preserves accepted-row output before a later REPLACE.
if grep -q 'executeInsertReturning state table columns (.inr query) conflict returning' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'executeInsertReturning state table columns (.inl rows) conflict returning' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreLastInsert.prepareReturning state ctx returning.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreReturning.prepare ctx (columns.map' SQLeanite/CoreLastInsert.lean &&
   grep -q 'CoreSQL.insertReturningRow_ignored' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.insertReturningRows_length_le' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'insertSelect table columns query conflict returning' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'insert table columns rows conflict returning' "$audit_sources/SQLeanite/CoreTokenGrammar.lean"; then
  ok "INSERT RETURNING checks its tokens and emits only accepted row outputs"
else
  fail "INSERT RETURNING is disconnected from checked binding or output collection"
fi

# REPLACE freezes the selection but re-seeks current values before each row.
if grep -q 'executeReplacedUpdate state tableName alias stored assignments.toList where_' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreUpdateReplace.pending tableName stored.schema.primaryKey trace' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreUpdateReplace.plan stored rowid' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreUpdateReplace.plan_validated' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreUpdateReplace.pending_length' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.replacedUpdateRows_missing' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "UPDATE OR REPLACE validates candidates and re-seeks pending rows"
else
  fail "UPDATE OR REPLACE is disconnected from its validated mutation trace"
fi
