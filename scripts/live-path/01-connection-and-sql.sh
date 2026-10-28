# Sourced by live-path-check.sh; shares its failure status and scratch files.
# Live WAL IO is an explicit boundary. Pin its production wiring without
# treating these textual checks as a proof of OS concurrency or durability.
if rg -F -q 'SQLite.WALShared.withSession paths true fun session =>' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreWALFileAdapter.commitInSession syncOps session' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'session.append syncOps.syncFile header pages' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'session.visibleWAL' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'SQLite.IndexCatalog.track (← catalog.get) state next statement source' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'indexDeclarations ++ (← storedCatalog session)' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'WALVFS.withRange paths.shm 120 1 true false' SQLeanite/SQLite/WALShared.lean &&
   rg -F -q 'withSharedRetry paths.shm 121 7 (action session)' SQLeanite/SQLite/WALShared.lean &&
   rg -F -q 'WALAppend.initialBytes initialHeader first.size' SQLeanite/SQLite/WALShared.lean &&
   rg -F -q 'CoreSizedPageCodec.encode? usable database baseHeader' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'WAL page size cannot change while appending' SQLeanite/SQLite/WALAppend.lean &&
   rg -F -q 'SyscallVFS.pwritePages paths.main.toString transfers' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'session.markBackfilled' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'F_OFD_SETLK' native/sqleanite_vfs.c; then
  ok "shared WAL sessions, append publication and non-truncating checkpoints reach production IO"
else
  fail "shared WAL locking, geometry guard or checkpoint publication is disconnected"
fi

if ! rg -F -q 'CoreSourceSQL.executeStatement state (statement state sql) source' SQLeanite/CoreConnectionSQL.lean; then
  echo 'missing connection-to-source execution path' >&2; exit 1
fi

if ! rg -F -q 'CoreConnectionSQL.executeStatement state sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean"; then
  echo 'missing derived-to-connection execution path' >&2; exit 1
fi

if rg -F -q 'CoreLastInsert.bind state (counterExpression state expr)' SQLeanite/CoreConnectionSQL.lean &&
   rg -F -q 'projection.map (CoreLastInsert.bind next)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'lastInsertRowid := state.lastInsertRowid' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreConnectionSQL.account_lastInsertRowid' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "connection rowid reads, per-row RETURNING and private materialization are wired"
else
  fail "connection rowid register path is disconnected"
fi

if rg -F -q 'CorePragmaTable.executeWith (fun state schema name target => viewInspection fuel state schema name target)' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CorePragmaTable.bindHidden current.database hidden' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'matchExprList arguments.toList' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'source.functionArgs.isNone' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CorePragmaTable.bindHidden_empty' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "PRAGMA table functions certify arguments and bind hidden columns before Core reads"
else
  fail "PRAGMA table-function argument, binding or lower-layer guard is disconnected"
fi

if rg -F -q 'CoreJsonTable.execute current name arguments' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'SQLite.JsonTable.evaluate (name.toLower == "json_tree") input path' SQLeanite/CoreJsonTable.lean &&
   rg -F -q 'CoreJsonTable.inlineProjection nested query inner source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'SQLite.JsonTable.evaluate_null' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "JSON table traversal, typed values and simple projection flattening reach Core reads"
else
  fail "JSON table execution or subtype-preserving projection path is disconnected"
fi

# Raw CREATE source is retained only after logical execution and metadata checking.
if rg -F -q 'CoreDerivedSQL.executeStatement state statement source' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreDerivedSQL.executeStatement state statement source' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'statements.toList chunk' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'statements.toList chunk' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreSQL.executeStatement state statement' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'SQLite.CreateCatalog.table source' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'table.withCatalogSQL sql' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'SQLite.AlterCatalog.addColumn before.catalogSQL source' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'CoreSourceSQL.executeStatement_add_trace' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSourceSQL.executeStatement_add_incomplete' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSourceSQL.retain_effect' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSourceSQL.executeStatement_create_noop' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "source-aware creation retains checked schema spelling before file publication"
else
  fail "source-aware catalog boundary or its checked effects are missing"
fi

# CTAS derives checked metadata and publishes only through a Core command trace.
if grep -q 'executeCreateTableAs state name query ifNotExists' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreCreateTableAs.columns state.database query' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'column.sourceSql == some source' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'CoreSQL.executeCreateTableAs_trace' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q '.createTableAs .. | .createTable ..' SQLeanite/CoreFileEngine.lean; then
  ok "CTAS certifies column metadata and executes a Core creation/insertion trace"
else
  fail "CTAS source metadata, Core trace or persistence wiring is missing"
fi

# PRAGMA atoms retain lexical spelling and explicit schema qualification.
if grep -q 'pure (.pragma name arg schema)' "$audit_sources/SQLeanite/Parser.lean" &&
   grep -q 'matchPragmaArgument expression' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'CoreSchemaPragma.execute state name argument schema' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'PragmaSyntax.numeric_integer_spelling' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "PRAGMA atoms and schema qualifiers remain explicit through certification"
else
  fail "PRAGMA spelling, schema binding or its contract is missing"
fi

# Schema PRAGMAs read live Core metadata without mutating the connection state.
if grep -q 'CoreSchemaPragma.execute state name argument' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'schema.catalogColumns.zipIdx.map' SQLeanite/CoreSchemaPragma.lean &&
   grep -q 'table.indexes.reverse.zipIdx.map' SQLeanite/CoreSchemaPragma.lean &&
   grep -q 'CoreSchemaPragma.execute_preserves_state' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "schema PRAGMAs read live Core metadata and preserve state"
else
  fail "schema PRAGMA routing or state-preservation contract is missing"
fi

# Foreign schema loading never runs SQL and both index readers validate contents.
if grep -q 'CoreSchemaSQL.tableSchema sql' SQLeanite/CoreCatalogSQL.lean &&
   grep -q 'CoreTokenGrammar.parseCertified first' SQLeanite/CoreSchemaSQL.lean &&
   rg -F -q 'checkedEncodedIndex source.textEncoding table index physical' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'if encoding ≤ 1 then return ← checkedIndex table index physical' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'physical.map (readIndexEntry column) == encodedIndexEntries encoding table index' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'CoreDecode.checkedEncodedIndex_utf8' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   ! grep -q 'CoreSQL.execute' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'CoreDecode.checkedIndex_contents' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "foreign catalog admission is metadata-only and validates physical indexes"
else
  fail "foreign schema admission or index content checks are missing"
fi

# Row-expression predicates remain on the production Core read boundary.
if grep -q 'executeFilteredSelect state select source stored' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'ctx.scanWindowObserved select.where_ expressions select.distinct result.rows' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.executeFilteredSelect_preserves_state' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreExpr.scan_length_le' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreExpr.scanWindow_limit_zero' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "row-expression WHERE uses bounded scans on Core query results"
else
  fail "row-expression WHERE route or its registered contracts are missing"
fi

# DISTINCT source representatives must use the same route after file reopen.
if [ "$(grep -c 'queryNeedsRepresentatives select.distinct columns ordering then' "$audit_sources/SQLeanite/CoreSQL.lean")" -eq 2 ] &&
   grep -q 'directQuery : CoreSQL.queryNeedsRepresentatives' "$audit_sources/SQLeanite/CoreSQLReadText.lean"; then
  ok "DISTINCT representative routing is shared by SQL and the persisted recognizer"
else
  fail "DISTINCT representative routing or direct-query proof premise is missing"
fi

# Direct and cold reads must validate qualifiers before dropping AST names.
if [ "$(grep -c 'unless selectNamesBound stored.schema source select' "$audit_sources/SQLeanite/CoreSQL.lean")" -eq 2 ] &&
   grep -q 'unless CoreSQL.selectNamesBound schema source select' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'unless writeNamesBound stored.schema table alias' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'namesBound : CoreSQL.selectNamesBound' "$audit_sources/SQLeanite/CoreSQLReadText.lean" &&
   grep -q 'namesBound : CoreSQL.writeNamesBound' "$audit_sources/SQLeanite/CoreSQLWriteText.lean" &&
   grep -q 'Scalar.bindNames_quoted' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "quoted identifiers and source scopes bind before direct Core execution"
else
  fail "source name validation is missing from a Core execution route"
fi

# General sorting preserves alias binding and evaluates retained candidates.
if grep -q 'CoreOrder.scan ctx select.where_ expressions terms' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.directOrdering schema source select' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'orderingTranslated : CoreSQL.directOrdering' "$audit_sources/SQLeanite/CoreSQLReadText.lean" &&
   grep -q 'CoreOrder.scan_limit_zero' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreOrder.insertStable_length' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "ORDER BY binding and bounded candidate sorting are on the Core path"
else
  fail "ORDER BY resolver, sorter, or its registered contracts are missing"
fi

# Sorting modifiers stay explicit through token certification and key comparison.
if grep -q 'term.nullsFirst' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'CoreOrder.validateTerm ctx' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'SQLite.Collation.compareValue spec.collation' SQLeanite/CoreOrder.lean &&
   grep -q 'Collation.noCase_nul' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'Collation.rtrimBytes_space' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "NULL placement and byte-level ordering collations use the Core sorter"
else
  fail "ordering modifiers or collation contracts are missing from production"
fi

# Row-dependent UPDATE remains an atomic trace of proved Core point updates.
if grep -q 'executeExpressionUpdate state tableName alias stored' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.executeExpressionUpdate_eq_runCoreCommands' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.rowUpdateCommands_length_le' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "row-dependent UPDATE uses a bounded Core command trace"
else
  fail "row-dependent UPDATE is detached from its Core trace contracts"
fi

# Scalar DELETE must share the Core atomic command boundary.
if grep -q 'executeExpressionDelete state tableName alias stored where_' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.executeExpressionDelete_eq_runCoreCommands' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.rowDeleteCommands_length_le' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "row-dependent DELETE uses a bounded Core command trace"
else
  fail "row-dependent DELETE is detached from its Core trace contracts"
fi

# WAL snapshots overlay their validated committed frames on the main file.
if grep -q 'SQLite.WALRead.recover contents.data.toList' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'snapshot.readPage base' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'WALRead.Replay.run_uncommitted' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'WALRead.Snapshot.readPage_base' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "WAL reads validate frame prefixes and preserve untouched main pages"
else
  fail "general WAL recovery is detached from its committed-prefix contracts"
fi

# SQL IN uses the scalar evaluator and binds indexed searches before scanning.
if grep -q 'evalInListTyped eval operandAffinity constant argument values negated applyLeftAffinity' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'expressionSearch ctx stored select.where_' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'Scalar.evalInList_empty' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "IN expressions and constant indexed searches are on the production path"
else
  fail "IN evaluator or expression search route is missing"
fi

# Scalar TEXT keeps original bytes across casts, stored reads, and output conversion.
if grep -q 'return Text.fromBytes (Text.bytes v)' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Text.characterSpans (Text.bytes v)' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'textBytes payload.bytes.toArray' SQLeanite/CoreExpr.lean &&
   grep -q 'Text.fromBytes_invalid' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreExpr.value_invalid_text' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'SQLite.CLI.listTextBytes' Main.lean; then
  ok "raw TEXT byte preservation is on the production scalar and storage paths"
else
  fail "raw TEXT conversion or its registered contracts are missing"
fi

# Boolean keywords bind to real columns before scalar preparation and search planning.
if grep -q 'ctx.bindNames expression' SQLeanite/CoreExpr.lean &&
   grep -q 'ctx.hasBooleanColumn expression' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'return plainScalar (isTruth a truth' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'bindBooleanKeywords_shadowed' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "boolean keyword binding and IS truth tests are on the production path"
else
  fail "boolean keyword binding or its registered contracts are missing"
fi

# Numeric aggregates share the physical-value accumulator after Core reads.
if grep -q 'SQLite.AggregateSum.sum (rows.map' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   grep -q 'state.sum.total / Float.ofNat state.sum.count' SQLeanite/CoreAggregate.lean &&
   grep -q 'SQLite.AggregateSum.realValue state.sum.total' SQLeanite/CoreAggregate.lean &&
   grep -q 'AggregateSum.sum_nulls' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'AggregateSum.average_nulls' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'prepared.results.accumulateSelected ctx select.where_' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.executeAggregateSelect_preserves_state' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreAggregateHaving.prepare ctx select.columns.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreAggregate.prepareTemplateFuel ctx true' SQLeanite/CoreAggregateHaving.lean &&
   grep -q 'accumulator.ingest term ctx input' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'prepared.finish ctx values representative' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'PreparedResults.accumulate_length' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "SUM/AVG/TOTAL use the numeric accumulator on production Core values"
else
  fail "numeric aggregate execution or its registered contracts are missing"
fi

# Internal aggregate ordering has its own source-token and scalar-input checks.
if grep -q 'state.pending.foldlM (fun state input => state.apply term input)' SQLeanite/CoreAggregate.lean &&
   grep -q 'AggregateOrder.decode? encoded' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'CoreAggregateOrdering.validateIgnored ctx order.expr' SQLeanite/CoreAggregate.lean &&
   grep -q 'let replaceEqual := ordered && term.distinct' SQLeanite/CoreAggregate.lean &&
   grep -q 'AggregateOrder.decode_encode' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "internal aggregate ORDER BY uses checked keys and DISTINCT representatives"
else
  fail "internal aggregate ordering or its registered contracts are missing"
fi

# FILTER is rechecked against source tokens and runs before aggregate arguments.
if grep -q 'expectKeyword "filter"' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'unless ← term.matchesFilter ctx row do return state' SQLeanite/CoreAggregate.lean &&
   grep -q 'term.matchesFilter ctx row' SQLeanite/CoreAggregateHaving.lean &&
   grep -q 'bucket.rows true' SQLeanite/CoreGrouped.lean &&
   grep -q 'CoreAggregate.Term.filteredRows_none' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "aggregate FILTER is token-checked and precedes argument evaluation"
else
  fail "aggregate FILTER execution or its registered contracts are missing"
fi

# Probability hints preserve values and branch evaluation after literal validation.
if grep -q 'Probability.recognizesName n then (Probability.input? n args).isSome' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Probability.input? name args then eval argument' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Probability.probability_integer' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "probability hints preserve values and validate probability literals"
else
  fail "probability hint execution or its registered contracts are missing"
fi

# Unicode escape functions retain byte sequences, including source-NUL suffixes.
if grep -q 'SQLite.DatabaseSize.pageCount? header input.length PhysicalCodec.pageSize' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'SQLite.DatabaseSize.pageCount? header metadata.byteSize.toNat header.headerPrefix.pageSize' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'SQLite.DatabaseSize.pageBytes main snapshot.pageSize' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'DatabaseSize.pageCount_stale' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "SQLite valid and stale header sizes share the bounded file/WAL geometry rules"
else
  fail "SQLite header-size validity is disconnected from file decoding"
fi

if grep -q 'let some catalog ← catalogIOFrom source' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'resolvedTablePayloadIOFrom source (source.pageCount + 1) cell' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   grep -q 'CoreDecode.catalogWalk_exhausted' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreDecode.decodeFromIOPageSource source' SQLeanite/CoreWALFileAdapter.lean; then
  ok "SQLite schema pages and overflow records use the bounded public catalog reader"
else
  fail "SQLite multi-page schema reader is disconnected"
fi

if grep -q 'Format.evaluate values' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Format.field_count_ignored' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'FloatCodec.decode17 value' SQLeanite/SQLite/Format.lean; then
  ok "SQLite printf conversion and decimal rounding are on the public scalar path"
else
  fail "SQLite printf conversion and decimal rounding are disconnected"
fi

if grep -q 'Math.evaluate? name args.toList' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Math.accepts n args.size' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Math.rounding_integer' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'Math.unary_null' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "SQLite math conversion and evaluation are on the public scalar path"
else
  fail "SQLite math conversion and evaluation are disconnected"
fi

if grep -q 'SQLite.UnicodeEscape.unistr v' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'SQLite.UnicodeEscape.quote v' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   grep -q 'Text.checkedBytes (← decodeFuel' SQLeanite/SQLite/UnicodeEscape.lean &&
   grep -q 'UnicodeEscape.decodeFuel_source_nul' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'UnicodeEscape.quote_blob' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "Unicode escape functions use the checked byte-preserving scalar path"
else
  fail "Unicode escape execution or its registered contracts are missing"
fi

# String aggregates retain byte values and evaluate separators on each input row.
if python3 scripts/check_module_boundaries.py --reaches SQLeanite.CoreAggregate SQLeanite.SQLite.AggregateConcat &&
   grep -q 'term.separator.mapM (ctx.eval row)' SQLeanite/CoreAggregate.lean &&
   grep -q 'state.concat.step input.value input.second' SQLeanite/CoreAggregate.lean &&
   grep -q 'SQLSurface.value state.concat.finish' SQLeanite/CoreAggregate.lean &&
   grep -q 'AggregateConcat.State.first_separator_ignored' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'AggregateConcat.State.step_null' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "string aggregates use the byte-preserving checked accumulator"
else
  fail "string aggregate execution or its registered contracts are missing"
fi

# Rebuilt and page-size-converted images retain application-owned header
# fields through the existing proved freelist/header layout. WAL uses the
# newest committed header, including a page-one overlay.
if grep -q 'let metadata ← previousMetadata.orElse' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'prepareBulkCommit? old database (some (updatedMetadata.getD metadata))' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'let layout := { baseLayout with metadata }' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'let metadata ← writeMetadata session' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'snapshot.readPage base 1' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'Layout.applicationId_preserved' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'Layout.userVersion_preserved' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "application-owned header metadata uses the proved layout in file and WAL writes"
else
  fail "database application metadata detached from the persisted header path"
fi

# Raw aliases must not be mistaken for source-bound predicates by a direct
# Core command or by the persisted-query recognizer.
if grep -q 'select.where_.any (CoreOrder.needsAliases ctx select.columns.toList)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'where_ := select.where_.map (CoreOrder.resolveAliases' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'executeExpressionSelect state resolved source stored none' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreOrder.resolveAliases_literal' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "WHERE aliases resolve before evaluation and bypass unresolved direct reads"
else
  fail "WHERE alias resolution detached from the live source-binding path"
fi

# General grouping must retain Core aggregates, source representatives and
# predicate-before-output evaluation through the new expression grouping path.
if grep -q 'CoreGrouped.run ctx select (stored.rows.map' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'prepared.aggregate.results.accumulate ctx bucket.rows' SQLeanite/CoreGrouped.lean &&
   grep -q 'CoreAggregateHaving.representative ctx' SQLeanite/CoreGrouped.lean &&
   grep -q 'prepared.aggregate.matches ctx values row' SQLeanite/CoreGrouped.lean &&
   grep -q 'CoreOrder.insertStable prepared.directions' SQLeanite/CoreGrouped.lean &&
   grep -q 'CoreGrouped.emitOrdered_limit_zero' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "grouped expressions retain Core aggregates, HAVING and bounded output ordering"
else
  fail "grouped expressions detached from the production aggregate path"
fi

# Explicit rowids must not enter the generated append proof without its premise.
if grep -q 'if automatic : values\[table.schema.primaryKey\]? = some .null then' SQLeanite/CoreWidePageDelta.lean &&
   grep -q 'table.createRow_generated automatic created' SQLeanite/CoreWidePageDelta.lean &&
   grep -q 'Core.Row.declaredKey_no_declared' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'Core.Row.create_set_rowid' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "implicit keys use distinct rowids and localized appends require automatic allocation"
else
  fail "rowid allocation is detached from its key/append contracts"
fi

# A geometry conversion has its own whole-image publication model.
if grep -q 'CoreFileAdapter.needsPageSizeConversion connection.paths' SQLeanite/CoreFileEngine.lean &&
   grep -q 'AtomicFileReplacement.plan prepared.newImage.fileBytes' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   grep -q 'AtomicFileReplacement.prefix_atomic' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "foreign page sizes use a separately modeled whole-image publication"
else
  fail "page-size conversion lost its publication route or component contract"
fi

# Rowid changes preserve the original snapshot and publish one Core trace.
if grep -q 'executeRekeyUpdate state tableName alias stored assignments.toList where_' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreSQL.executeRekeyUpdate_eq_runCoreCommands' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreSQL.rowRekeyBatch_changes_le' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "rowid UPDATE uses a bounded atomic Core delete/insert trace"
else
  fail "rowid updates are detached from their Core trace contract"
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
trap 'rm -f "$axioms" "$scratch_parity"; rm -rf "$audit_sources"' EXIT
if ! "$lake_command" env lean "$audit_sources/SQLeanite/ProofAxioms.lean" > "$axioms" 2>&1; then
  printf 'live-path check FAILED: ProofAxioms did not elaborate\n' >&2
  cat "$axioms" >&2
  exit 1
fi
expected=$(grep -c '^#print axioms ' "$audit_sources/SQLeanite/ProofAxioms.lean")
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
  case "$entry" in
    SQLeanite/CoreFileEngine.lean|SQLeanite/CoreWALFileEngine.lean|SQLeanite/CoreLazyFileEngine.lean) token_source=chunk ;;
    *) token_source=sql ;;
  esac
  if rg -F -q "CoreTokenGrammar.parseStatements $token_source" "$entry" &&
     ! rg -q '(^|[^[:alnum:]_.])parse (sql|chunk)' "$entry"; then
    ok "$entry uses certified SQL admission"
  else
    fail "$entry bypasses the concrete SQL certificate"
  fi
done

if grep -q 'SQLite.PhysicalAffinity.write column.affinity' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'comparisonLiteral schema index' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'Core.readColumnValues schema.columns' SQLeanite/CoreRecord.lean &&
   grep -q 'SQLite.PhysicalAffinity.accepts column.affinity' "$audit_sources/SQLeanite/CoreData.lean" &&
   grep -q 'Core.readColumnValues_eq_self' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreTokenGrammar.parseStatements_certified' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "stored affinity is checked on writes, comparisons and record reads"
else
  fail "stored affinity detached from the proved production path"
fi
