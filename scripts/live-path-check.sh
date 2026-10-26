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

# CTAS derives checked metadata and publishes only through a Core command trace.
if grep -q 'executeCreateTableAs state name query ifNotExists' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreCreateTableAs.columns state.database query' SQLeanite/CoreSQL.lean &&
   grep -q 'column.sourceSql == some source' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'CoreSQL.executeCreateTableAs_trace' SQLeanite/ProofAxioms.lean &&
   grep -q '.createTableAs .. | .createTable ..' SQLeanite/CoreFileEngine.lean; then
  ok "CTAS certifies column metadata and executes a Core creation/insertion trace"
else
  fail "CTAS source metadata, Core trace or persistence wiring is missing"
fi

# PRAGMA atoms retain lexical spelling and explicit schema qualification.
if grep -q 'pure (.pragma name arg schema)' SQLeanite/Parser.lean &&
   grep -q 'matchPragmaArgument expression' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'CoreSchemaPragma.execute state name argument schema' SQLeanite/CoreSQL.lean &&
   grep -q 'PragmaSyntax.numeric_integer_spelling' SQLeanite/ProofAxioms.lean; then
  ok "PRAGMA atoms and schema qualifiers remain explicit through certification"
else
  fail "PRAGMA spelling, schema binding or its contract is missing"
fi

# Schema PRAGMAs read live Core metadata without mutating the connection state.
if grep -q 'CoreSchemaPragma.execute state name argument' SQLeanite/CoreSQL.lean &&
   grep -q 'schema.catalogColumns.zipIdx.map' SQLeanite/CoreSchemaPragma.lean &&
   grep -q 'table.indexes.reverse.zipIdx.map' SQLeanite/CoreSchemaPragma.lean &&
   grep -q 'CoreSchemaPragma.execute_preserves_state' SQLeanite/ProofAxioms.lean; then
  ok "schema PRAGMAs read live Core metadata and preserve state"
else
  fail "schema PRAGMA routing or state-preservation contract is missing"
fi

# Foreign schema loading never runs SQL and both index readers validate contents.
if grep -q 'CoreSchemaSQL.tableSchema sql' SQLeanite/CoreDecode.lean &&
   grep -q 'CoreTokenGrammar.parseCertified first' SQLeanite/CoreSchemaSQL.lean &&
   [ "$(grep -c 'checkedIndex table index physical' SQLeanite/CoreDecode.lean)" -eq 3 ] &&
   ! grep -q 'CoreSQL.execute' SQLeanite/CoreDecode.lean &&
   grep -q 'CoreDecode.checkedIndex_contents' SQLeanite/ProofAxioms.lean; then
  ok "foreign catalog admission is metadata-only and validates physical indexes"
else
  fail "foreign schema admission or index content checks are missing"
fi

# Row-expression predicates remain on the production Core read boundary.
if grep -q 'executeFilteredSelect state select source stored' SQLeanite/CoreSQL.lean &&
   grep -q 'ctx.scanWindow select.where_ expressions select.distinct result.rows' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.executeFilteredSelect_preserves_state' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreExpr.scan_length_le' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreExpr.scanWindow_limit_zero' SQLeanite/ProofAxioms.lean; then
  ok "row-expression WHERE uses bounded scans on Core query results"
else
  fail "row-expression WHERE route or its registered contracts are missing"
fi

# DISTINCT source representatives must use the same route after file reopen.
if [ "$(grep -c 'queryNeedsRepresentatives select.distinct columns ordering then' SQLeanite/CoreSQL.lean)" -eq 2 ] &&
   grep -q 'directQuery : CoreSQL.queryNeedsRepresentatives' SQLeanite/CoreSQLReadText.lean; then
  ok "DISTINCT representative routing is shared by SQL and the persisted recognizer"
else
  fail "DISTINCT representative routing or direct-query proof premise is missing"
fi

# Direct and cold reads must validate qualifiers before dropping AST names.
if [ "$(grep -c 'unless selectNamesBound stored.schema source select' SQLeanite/CoreSQL.lean)" -eq 2 ] &&
   grep -q 'unless CoreSQL.selectNamesBound schema source select' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'unless writeNamesBound stored.schema table alias' SQLeanite/CoreSQL.lean &&
   grep -q 'namesBound : CoreSQL.selectNamesBound' SQLeanite/CoreSQLReadText.lean &&
   grep -q 'namesBound : CoreSQL.writeNamesBound' SQLeanite/CoreSQLWriteText.lean &&
   grep -q 'Scalar.bindNames_quoted' SQLeanite/ProofAxioms.lean; then
  ok "quoted identifiers and source scopes bind before direct Core execution"
else
  fail "source name validation is missing from a Core execution route"
fi

# General sorting preserves alias binding and evaluates retained candidates.
if grep -q 'CoreOrder.scan ctx select.where_ expressions terms' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.directOrdering schema source select' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'orderingTranslated : CoreSQL.directOrdering' SQLeanite/CoreSQLReadText.lean &&
   grep -q 'CoreOrder.scan_limit_zero' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreOrder.insertStable_length' SQLeanite/ProofAxioms.lean; then
  ok "ORDER BY binding and bounded candidate sorting are on the Core path"
else
  fail "ORDER BY resolver, sorter, or its registered contracts are missing"
fi

# Sorting modifiers stay explicit through token certification and key comparison.
if grep -q 'term.nullsFirst' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'CoreOrder.validateTerm ctx' SQLeanite/CoreSQL.lean &&
   grep -q 'SQLite.Collation.compareValue spec.collation' SQLeanite/CoreOrder.lean &&
   grep -q 'Collation.noCase_nul' SQLeanite/ProofAxioms.lean &&
   grep -q 'Collation.rtrimBytes_space' SQLeanite/ProofAxioms.lean; then
  ok "NULL placement and byte-level ordering collations use the Core sorter"
else
  fail "ordering modifiers or collation contracts are missing from production"
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

# WAL snapshots overlay their validated committed frames on the main file.
if grep -q 'SQLite.WALRead.recover contents.data.toList' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'snapshot.readPage base' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'WALRead.Replay.run_uncommitted' SQLeanite/ProofAxioms.lean &&
   grep -q 'WALRead.Snapshot.readPage_base' SQLeanite/ProofAxioms.lean; then
  ok "WAL reads validate frame prefixes and preserve untouched main pages"
else
  fail "general WAL recovery is detached from its committed-prefix contracts"
fi

# SQL IN uses the scalar evaluator and binds indexed searches before scanning.
if grep -q 'evalInList eval operandAffinity constant argument values negated applyLeftAffinity' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'expressionSearch ctx stored select.where_' SQLeanite/CoreSQL.lean &&
   grep -q 'Scalar.evalInList_empty' SQLeanite/ProofAxioms.lean; then
  ok "IN expressions and constant indexed searches are on the production path"
else
  fail "IN evaluator or expression search route is missing"
fi

# Scalar TEXT keeps original bytes across casts, stored reads, and output conversion.
if grep -q 'return Text.fromBytes (Text.bytes v)' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Text.characterSpans (Text.bytes v)' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'textBytes payload.bytes.toArray' SQLeanite/CoreExpr.lean &&
   grep -q 'Text.fromBytes_invalid' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreExpr.value_invalid_text' SQLeanite/ProofAxioms.lean &&
   grep -q 'SQLite.CLI.listTextBytes' Main.lean; then
  ok "raw TEXT byte preservation is on the production scalar and storage paths"
else
  fail "raw TEXT conversion or its registered contracts are missing"
fi

# Boolean keywords bind to real columns before scalar preparation and search planning.
if grep -q 'ctx.bindNames expression' SQLeanite/CoreExpr.lean &&
   grep -q 'ctx.hasBooleanColumn expression' SQLeanite/CoreSQL.lean &&
   grep -q 'return isTruth left truth' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'bindBooleanKeywords_shadowed' SQLeanite/ProofAxioms.lean; then
  ok "boolean keyword binding and IS truth tests are on the production path"
else
  fail "boolean keyword binding or its registered contracts are missing"
fi

# Numeric aggregates share the physical-value accumulator after Core reads.
if grep -q 'SQLite.AggregateSum.sum (rows.map' SQLeanite/CoreEngine.lean &&
   grep -q 'SQLite.AggregateSum.average inputs' SQLeanite/CoreAggregate.lean &&
   grep -q 'SQLite.AggregateSum.total inputs' SQLeanite/CoreAggregate.lean &&
   grep -q 'AggregateSum.sum_nulls' SQLeanite/ProofAxioms.lean &&
   grep -q 'AggregateSum.average_nulls' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreAggregate.selectRows ctx select.where_ result.rows' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.executeAggregateSelect_preserves_state' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreAggregateHaving.prepare ctx select.columns.toList' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreAggregate.prepareTemplateFuel ctx true' SQLeanite/CoreAggregateHaving.lean &&
   grep -q 'prepared.results.accumulate ctx inputs' SQLeanite/CoreSQL.lean &&
   grep -q 'prepared.finish ctx values representative' SQLeanite/CoreSQL.lean &&
   grep -q 'PreparedResults.accumulate_length' SQLeanite/ProofAxioms.lean; then
  ok "SUM/AVG/TOTAL use the numeric accumulator on production Core values"
else
  fail "numeric aggregate execution or its registered contracts are missing"
fi

# Internal aggregate ordering has its own source-token and scalar-input checks.
if grep -q 'let rows ← term.orderedRows ctx rows' SQLeanite/CoreAggregate.lean &&
   grep -q 'AggregateOrder.decode? encoded' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'CoreAggregateOrdering.validateIgnored ctx order.expr' SQLeanite/CoreAggregate.lean &&
   grep -q 'replaceEqual := distinct && identicalKey' SQLeanite/CoreAggregateOrdering.lean &&
   grep -q 'AggregateOrder.decode_encode' SQLeanite/ProofAxioms.lean; then
  ok "internal aggregate ORDER BY uses checked keys and DISTINCT representatives"
else
  fail "internal aggregate ordering or its registered contracts are missing"
fi

# FILTER is rechecked against source tokens and runs before aggregate arguments.
if grep -q 'expectKeyword "filter"' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'let rows ← term.filteredRows ctx rows' SQLeanite/CoreAggregate.lean &&
   grep -q 'term.matchesFilter ctx row' SQLeanite/CoreAggregateHaving.lean &&
   grep -q 'bucket.rows true' SQLeanite/CoreGrouped.lean &&
   grep -q 'CoreAggregate.Term.filteredRows_none' SQLeanite/ProofAxioms.lean; then
  ok "aggregate FILTER is token-checked and precedes argument evaluation"
else
  fail "aggregate FILTER execution or its registered contracts are missing"
fi

# Probability hints preserve values and branch evaluation after literal validation.
if grep -q 'Probability.recognizesName n then (Probability.input? n args).isSome' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Probability.input? name args then eval argument' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Probability.probability_integer' SQLeanite/ProofAxioms.lean; then
  ok "probability hints preserve values and validate probability literals"
else
  fail "probability hint execution or its registered contracts are missing"
fi

# Unicode escape functions retain byte sequences, including source-NUL suffixes.
if grep -q 'SQLite.DatabaseSize.pageCount? header input.length PhysicalCodec.pageSize' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'SQLite.DatabaseSize.pageCount? header metadata.byteSize.toNat header.headerPrefix.pageSize' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'SQLite.DatabaseSize.pageBytes main snapshot.pageSize' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'DatabaseSize.pageCount_stale' SQLeanite/ProofAxioms.lean; then
  ok "SQLite valid and stale header sizes share the bounded file/WAL geometry rules"
else
  fail "SQLite header-size validity is disconnected from file decoding"
fi

if grep -q 'let some catalog ← catalogIOFrom source' SQLeanite/CoreDecode.lean &&
   grep -q 'resolvedTablePayloadIOFrom source (source.pageCount + 1) cell' SQLeanite/CoreDecode.lean &&
   grep -q 'CoreDecode.catalogWalk_exhausted' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreDecode.decodeFromIOPageSource source' SQLeanite/CoreWALFileAdapter.lean; then
  ok "SQLite schema pages and overflow records use the bounded public catalog reader"
else
  fail "SQLite multi-page schema reader is disconnected"
fi

if grep -q 'Format.evaluate values' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Format.field_count_ignored' SQLeanite/ProofAxioms.lean &&
   grep -q 'FloatCodec.decode17 value' SQLeanite/SQLite/Format.lean; then
  ok "SQLite printf conversion and decimal rounding are on the public scalar path"
else
  fail "SQLite printf conversion and decimal rounding are disconnected"
fi

if grep -q 'Math.evaluate? name args.toList' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Math.accepts n args.size' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Math.rounding_integer' SQLeanite/ProofAxioms.lean &&
   grep -q 'Math.unary_null' SQLeanite/ProofAxioms.lean; then
  ok "SQLite math conversion and evaluation are on the public scalar path"
else
  fail "SQLite math conversion and evaluation are disconnected"
fi

if grep -q 'SQLite.UnicodeEscape.unistr v' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'SQLite.UnicodeEscape.quote v' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Text.checkedBytes (← decodeFuel' SQLeanite/SQLite/UnicodeEscape.lean &&
   grep -q 'UnicodeEscape.decodeFuel_source_nul' SQLeanite/ProofAxioms.lean &&
   grep -q 'UnicodeEscape.quote_blob' SQLeanite/ProofAxioms.lean; then
  ok "Unicode escape functions use the checked byte-preserving scalar path"
else
  fail "Unicode escape execution or its registered contracts are missing"
fi

# String aggregates retain byte values and evaluate separators on each input row.
if grep -q 'import SQLeanite.SQLite.AggregateConcat' SQLeanite/CoreAggregate.lean &&
   grep -q 'term.separator.mapM (ctx.eval row)' SQLeanite/CoreAggregate.lean &&
   grep -q 'state.step value (separator.getD' SQLeanite/CoreAggregate.lean &&
   grep -q 'SQLSurface.value state.finish' SQLeanite/CoreAggregate.lean &&
   grep -q 'AggregateConcat.State.first_separator_ignored' SQLeanite/ProofAxioms.lean &&
   grep -q 'AggregateConcat.State.step_null' SQLeanite/ProofAxioms.lean; then
  ok "string aggregates use the byte-preserving checked accumulator"
else
  fail "string aggregate execution or its registered contracts are missing"
fi

# Rebuilt and page-size-converted images retain application-owned header
# fields through the existing proved freelist/header layout. WAL uses the
# newest committed header, including a page-one overlay.
if grep -q 'let metadata ← previousMetadata.orElse' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'prepareBulkCommit? old database (some metadata)' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'let layout := { baseLayout with metadata }' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'let metadata ← writeMetadata paths' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'snapshot.readPage base 1' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'Layout.applicationId_preserved' SQLeanite/ProofAxioms.lean &&
   grep -q 'Layout.userVersion_preserved' SQLeanite/ProofAxioms.lean; then
  ok "application-owned header metadata uses the proved layout in file and WAL writes"
else
  fail "database application metadata detached from the persisted header path"
fi

# Raw aliases must not be mistaken for source-bound predicates by a direct
# Core command or by the persisted-query recognizer.
if grep -q 'select.where_.any (CoreOrder.needsAliases ctx select.columns.toList)' SQLeanite/CoreSQL.lean &&
   grep -q 'where_ := select.where_.map (CoreOrder.resolveAliases' SQLeanite/CoreSQL.lean &&
   grep -q 'executeExpressionSelect state resolved source stored none' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreOrder.resolveAliases_literal' SQLeanite/ProofAxioms.lean; then
  ok "WHERE aliases resolve before evaluation and bypass unresolved direct reads"
else
  fail "WHERE alias resolution detached from the live source-binding path"
fi

# General grouping must retain Core aggregates, source representatives and
# predicate-before-output evaluation through the new expression grouping path.
if grep -q 'CoreGrouped.run ctx select (stored.rows.map' SQLeanite/CoreSQL.lean &&
   grep -q 'prepared.aggregate.results.accumulate ctx bucket.rows' SQLeanite/CoreGrouped.lean &&
   grep -q 'CoreAggregateHaving.representative ctx' SQLeanite/CoreGrouped.lean &&
   grep -q 'prepared.aggregate.matches ctx values row' SQLeanite/CoreGrouped.lean &&
   grep -q 'CoreOrder.insertStable prepared.directions' SQLeanite/CoreGrouped.lean &&
   grep -q 'CoreGrouped.emitOrdered_limit_zero' SQLeanite/ProofAxioms.lean; then
  ok "grouped expressions retain Core aggregates, HAVING and bounded output ordering"
else
  fail "grouped expressions detached from the production aggregate path"
fi

# Explicit rowids must not enter the generated append proof without its premise.
if grep -q 'if automatic : values\[table.schema.primaryKey\]? = some .null then' SQLeanite/CoreWidePageDelta.lean &&
   grep -q 'table.createRow_generated automatic created' SQLeanite/CoreWidePageDelta.lean &&
   grep -q 'Core.Row.declaredKey_no_declared' SQLeanite/ProofAxioms.lean &&
   grep -q 'Core.Row.create_set_rowid' SQLeanite/ProofAxioms.lean; then
  ok "implicit keys use distinct rowids and localized appends require automatic allocation"
else
  fail "rowid allocation is detached from its key/append contracts"
fi

# A geometry conversion has its own whole-image publication model.
if grep -q 'CoreFileAdapter.needsPageSizeConversion connection.paths' SQLeanite/CoreFileEngine.lean &&
   grep -q 'AtomicFileReplacement.plan prepared.newImage.fileBytes' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'AtomicFileReplacement.prefix_atomic' SQLeanite/ProofAxioms.lean; then
  ok "foreign page sizes use a separately modeled whole-image publication"
else
  fail "page-size conversion lost its publication route or component contract"
fi

# Rowid changes preserve the original snapshot and publish one Core trace.
if grep -q 'executeRekeyUpdate state tableName alias stored assignments.toList where_' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.executeRekeyUpdate_eq_runCoreCommands' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.rowRekeyBatch_changes_le' SQLeanite/ProofAxioms.lean; then
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
  case "$entry" in
    SQLeanite/CoreFileEngine.lean|SQLeanite/CoreWALFileEngine.lean) token_source=chunk ;;
    *) token_source=sql ;;
  esac
  if rg -F -q "CoreTokenGrammar.parseStatements $token_source" "$entry" &&
     ! rg -q '(^|[^[:alnum:]_.])parse (sql|chunk)' "$entry"; then
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

if grep -q '"round", \[v, places\].*roundValue v places' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'FloatCodec.renderFixed r n' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Scalar.roundPrecision_le' SQLeanite/ProofAxioms.lean; then
  ok "round uses the pure fixed-decimal codec and bounded precision"
else
  fail "round detached from its implementation or precision theorem"
fi

if grep -q 'Pattern.evaluate false b a' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Pattern.evaluate true b a' SQLeanite/SQLite/Scalar.lean &&
   grep -q 'Pattern.matches_empty' SQLeanite/ProofAxioms.lean; then
  ok "LIKE and GLOB use the pure pattern matcher on the live scalar path"
else
  fail "pattern matching detached from its implementation or component proofs"
fi

if grep -q 'table.uniqueConflict row' SQLeanite/Core.lean &&
   grep -q 'table.uniqueConflict patched true' SQLeanite/Core.lean &&
   grep -q 'replaceUniqueRows state tableName' SQLeanite/CoreSQL.lean &&
   grep -q 'CREATE UNIQUE INDEX' SQLeanite/CanonicalIndexSQL.lean &&
   grep -q 'Core.Table.insertValues_unique' SQLeanite/ProofAxioms.lean; then
  ok "UNIQUE metadata and constraints are on the Core write path"
else
  fail "UNIQUE constraints detached from production writes or their proof"
fi

if grep -q 'prepareCreateTable state name ifNotExists' SQLeanite/CoreSQL.lean &&
   grep -q 'prepareCreateIndex state name ifNotExists' SQLeanite/CoreSQL.lean &&
   grep -q '!CoreSQL.schemaNoop current statement' SQLeanite/CoreFileEngine.lean &&
   grep -q '!CoreSQL.schemaNoop state statement' SQLeanite/CoreWALFileEngine.lean &&
   grep -q 'CoreSQL.executeStatement_createTable_noop' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.executeStatement_createIndex_noop' SQLeanite/ProofAxioms.lean; then
  ok "schema admission and IF NOT EXISTS no-ops preserve the live file paths"
else
  fail "schema no-op guards detached from execution or persistence"
fi

if grep -q 'notNull := integerAlias || column.notNull' SQLeanite/CoreSQL.lean &&
   grep -q '| none | some .null => .rowid row.rowid' SQLeanite/Core.lean &&
   grep -q 'Core.Row.declaredKey_null_ne_nonnull' SQLeanite/ProofAxioms.lean &&
   grep -q 'TEXT PRIMARY KEY NOT NULL' SQLeanite/CanonicalSchemaSQL.lean &&
   grep -q 'conflict == .replace && hasReplaceKeys stored' SQLeanite/CoreSQL.lean &&
   grep -q 'replacing && hasReplaceKeys stored' SQLeanite/CoreSQL.lean &&
   grep -q 'Core.Row.declaredKey_null_injective' SQLeanite/ProofAxioms.lean; then
  ok "nullable TEXT keys preserve distinct NULLs, declared NOT NULL and REPLACE allocation"
else
  fail "nullable TEXT key constraints or REPLACE allocation detached from the live path"
fi

if [ "$(grep -c 'ascendingCellPointers (cellCount - 1) contentStart remaining' SQLeanite/CoreDecode.lean)" -eq 4 ] &&
   grep -q 'CoreDecode.ascendingCellPointers_leafPointers' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreDecode.ascendingCellPointers_next' SQLeanite/ProofAxioms.lean; then
  ok "packed schema, row and index decoders check the whole pointer ordering"
else
  fail "packed-page recognition lost its whole-pointer ordering guard"
fi

if grep -q 'let definitions ← tablePrimaryColumns definitions constraints' SQLeanite/CoreSQL.lean &&
   grep -q 'matchTablePrimary constraint' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'collations := collations.push collation' SQLeanite/Parser.lean &&
   grep -q 'descending := descending.push desc' SQLeanite/Parser.lean &&
   grep -q 'CoreSQL.markPrimaryColumn_names' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.tablePrimaryColumns_empty' SQLeanite/ProofAxioms.lean &&
   grep -q 'match insertValueIndex schema.primaryKey targetIndex indices' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.insertValueIndex_rowid' SQLeanite/ProofAxioms.lean; then
  ok "table PRIMARY KEY syntax retains metadata and lowers through checked Core schemas"
else
  fail "table-key metadata or checked lowering detached from the live path"
fi

if grep -q 'inputRowValues schema columns evaluateAll' SQLeanite/CoreSQL.lean &&
   grep -q 'rows.toList (1 < rows.size)' SQLeanite/CoreSQL.lean &&
   grep -q 'ctx projection inputs evaluateAll' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.inputRowValues stored.schema columns (1 < rows.size)' SQLeanite/CoreSQLWriteText.lean &&
   grep -q 'CoreSQL.evaluateInsertExpressions_evaluated' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.inputRowValues_single' SQLeanite/ProofAxioms.lean; then
  ok "multi-VALUES source evaluation reaches all insert policies and RETURNING with matching trace premises"
else
  fail "multi-VALUES evaluation mode detached from insertion or its proof boundary"
fi

if grep -q 'integerPrimaryNotNull := integerAlias && column.notNull' SQLeanite/CoreSQL.lean &&
   grep -q 'if column.integerPrimaryNotNull then " INTEGER PRIMARY KEY NOT NULL"' SQLeanite/CanonicalSchemaSQL.lean &&
   grep -q 'integerPrimaryKey := true, integerPrimaryNotNull := true' SQLeanite/CanonicalSchemaSQL.lean &&
   grep -q 'CanonicalSchemaSQL.parseBaseColumn_integerNotNull_append' SQLeanite/ProofAxioms.lean; then
  ok "declared INTEGER key NOT NULL metadata survives canonical print and parse"
else
  fail "declared INTEGER key nullability detached from the schema codec"
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
# `filePageSourceFor`; it now strides a buffered read by physical page size,
# which is faster but just as easy to get wrong -- substituting the fixed-size
# `byteArrayPageSource` here silently broke the 1024-byte differential case, so
# both the positive and the negative check are asserted.
if grep -q 'let pageBytes := header.headerPrefix.pageSize' \
     SQLeanite/CoreFileAdapter.lean &&
   ! grep -q 'byteArrayPageSource whole count' \
     SQLeanite/CoreFileAdapter.lean &&
   grep -q 'catalogPage? source.usable.val pageNumber page' \
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

# Tuple targets and RHS values are replayed together and never truncated.
if grep -q 'SQLite.RowAssignment.bind names.toList values.toList' SQLeanite/Parser.lean &&
   grep -q 'assignments.size ≤ SQLite.Limits.maxColumns' SQLeanite/Parser.lean &&
   grep -q 'matchAssignmentNames ((name, expression) :: rest)' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'matchAssignmentValues ((← get).remaining.length + 1) expressions' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'SQLite.RowAssignment.bind_exact' SQLeanite/ProofAxioms.lean &&
   grep -q 'SQLite.RowAssignment.bind_length' SQLeanite/ProofAxioms.lean; then
  ok "row-value UPDATE checks widths and replays each grouped name/value pair"
else
  fail "row-value UPDATE is disconnected from its checked lowering"
fi

# RETURNING disables one-pass UPDATE and preserves outputs of accepted rows.
if grep -q 'executeUpdateReturning state tableName alias stored assignments.toList where_ conflict returning' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreReturning.updatedOutput outputCtx values projection outcome' SQLeanite/CoreSQL.lean &&
   grep -q 'updateReturningRows state tableName ctx outputCtx bound conflict projection rowids' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreReturning.updatedOutput_zero' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.updateReturningRow_missing' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.updateReturningRows_length_le' SQLeanite/ProofAxioms.lean &&
   grep -q 'update table alias assignments where_ conflict returning' SQLeanite/CoreTokenGrammar.lean; then
  ok "UPDATE RETURNING freezes selected rowids and materializes accepted new values"
else
  fail "UPDATE RETURNING is disconnected from checked row selection or output"
fi

# INSERT RETURNING preserves accepted-row output before a later REPLACE.
if grep -q 'executeInsertReturning state table columns (.inr query) conflict returning' SQLeanite/CoreSQL.lean &&
   grep -q 'executeInsertReturning state table columns (.inl rows) conflict returning' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreReturning.prepare ctx returning.toList' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSQL.insertReturningRow_ignored' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.insertReturningRows_length_le' SQLeanite/ProofAxioms.lean &&
   grep -q 'insertSelect table columns query conflict returning' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'insert table columns rows conflict returning' SQLeanite/CoreTokenGrammar.lean; then
  ok "INSERT RETURNING checks its tokens and emits only accepted row outputs"
else
  fail "INSERT RETURNING is disconnected from checked binding or output collection"
fi

# REPLACE freezes the selection but re-seeks current values before each row.
if grep -q 'executeReplacedUpdate state tableName alias stored assignments.toList where_' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreUpdateReplace.pending tableName stored.schema.primaryKey trace' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreUpdateReplace.plan stored rowid' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreUpdateReplace.plan_validated' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreUpdateReplace.pending_length' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.replacedUpdateRows_missing' SQLeanite/ProofAxioms.lean; then
  ok "UPDATE OR REPLACE validates candidates and re-seeks pending rows"
else
  fail "UPDATE OR REPLACE is disconnected from its validated mutation trace"
fi

# A conflicting UPDATE retains the original row, including when a key changes.
if grep -q 'executeIgnoredUpdate state tableName alias stored assignments.toList where_' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreUpdateIgnore.row state tableName ctx.schema row.rowid values' SQLeanite/CoreSQL.lean &&
   grep -q 'expressionAssignmentsWith true ctx assignments' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreUpdateScan.order ctx stored bound condition' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreUpdateScan.byColumn_perm' SQLeanite/ProofAxioms.lean &&
   grep -q 'SQLite.PlannerCost.scan' SQLeanite/CoreUpdateScan.lean &&
   grep -Fq 'table.withIndexes (table.indexes ++ [index])' SQLeanite/Core.lean &&
   grep -q 'let some database ← applyIndexIOFrom source database entry' SQLeanite/CoreDecode.lean &&
   grep -q 'CoreUpdateIgnore.finish_skips' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreUpdateIgnore.finish_inserts' SQLeanite/ProofAxioms.lean; then
  ok "UPDATE OR IGNORE retains old rows on conflict and checks accepted key changes"
else
  fail "UPDATE OR IGNORE is disconnected from its state-preservation checks"
fi

# IGNORE classifies typed constraint conflicts, leaving ordinary errors intact.
if grep -q 'CoreInsertIgnore.shouldInsert stored values' SQLeanite/CoreSQL.lean &&
   grep -q 'if conflict == .ignore then ignoreInsertRows' SQLeanite/CoreSQL.lean &&
   grep -q 'ignoreInsertRows state tableName stored.schema columns rows.toList' SQLeanite/CoreSQL.lean &&
   grep -q 'unless expressions.all SQLite.Scalar.admitted' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreInsertIgnore.shouldInsert_no_conflict' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.executeIgnoredInsert_skips' SQLeanite/ProofAxioms.lean; then
  ok "INSERT OR IGNORE keeps typed constraints separate from expression errors"
else
  fail "INSERT OR IGNORE is disconnected from checked conflict handling"
fi

# RETURNING binds the actual table name and materializes old row outputs
# before Core commands can be published by either public file engine.
if grep -q 'executeDeleteReturning state tableName alias stored where_ returning' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreReturning.prepare ctx columns.toList' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreReturning.deletionOutput stored ctx expressions commands' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreReturning.deletionOutput_length' SQLeanite/ProofAxioms.lean; then
  ok "DELETE RETURNING materializes validated old values before mutation"
else
  fail "DELETE RETURNING is detached from its validated materialization"
fi

# VALUES result metadata is replayed against the source, and its multi-row
# coroutine keeps a separate OFFSET evaluation rule from scalar SELECT.
if grep -q 'matchValuesBase query rows' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'the same first VALUES row' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'select.valueRows.isSome then executeValues state select' SQLeanite/CoreSQL.lean &&
   grep -q 'let row ← constantRow { select with valueRows := none }' SQLeanite/CoreSQL.lean &&
   grep -q 'SQLite.Values.directCount rows.toList' SQLeanite/CoreSQL.lean &&
   grep -q 'SQLite.Values.collations rows.toList wrappedValues' SQLeanite/CoreSQL.lean &&
   grep -q 'SQLite.Values.directCount_le_length' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreSQL.executeValues_preserves_state' SQLeanite/ProofAxioms.lean; then
  ok "VALUES queries use checked metadata and their own row-evaluation discipline"
else
  fail "VALUES parsing or row execution is disconnected from its checks"
fi

# INSERT SELECT evaluates a source snapshot, validates even empty projections,
# and routes evaluated values through the existing checked INSERT machinery.
if grep -q 'let selection ← executeSelect state query' SQLeanite/CoreSQL.lean &&
   grep -q 'checkInsertSelectColumns stored.schema columns selection.width' SQLeanite/CoreSQL.lean &&
   grep -q 'selection.result.rows.mapM selectedRowExpressions' SQLeanite/CoreSQL.lean &&
   grep -q '.insertSelect ..' SQLeanite/CoreFileEngine.lean &&
   grep -q 'CoreSQL.insertSelection_empty' SQLeanite/ProofAxioms.lean; then
  ok "INSERT SELECT validates source width and persists through ordinary INSERT execution"
else
  fail "INSERT SELECT is disconnected from checked insertion or persistence"
fi

# DROP shares the transaction/persistence machinery with other schema writes.
if grep -q 'CoreSchemaDrop.table state.database' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSchemaDrop.index stored' SQLeanite/CoreSQL.lean &&
   grep -q '.dropTable .. | .dropIndex ..' SQLeanite/CoreFileEngine.lean &&
   grep -q 'dropTable name ifExists => (prepareDropTable' SQLeanite/CoreSQL.lean &&
   grep -q 'dropIndex name ifExists => (prepareDropIndex' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreSchemaDrop.index_exact' SQLeanite/ProofAxioms.lean; then
  ok "DROP tables/indexes retains Core invariants and uses schema-write persistence"
else
  fail "DROP execution is disconnected from transaction persistence or its contracts"
fi

# Header-format restrictions must cover cold reads and in-transaction writes.
if grep -q 'CoreFileAdapter.requireReadable paths.main' SQLeanite/CoreFileEngine.lean &&
   grep -q 'CoreFileAdapter.requireReadable paths.main' SQLeanite/CoreLazyFileEngine.lean &&
   grep -q 'CoreFileAdapter.requireWritableFormat connection.paths.main' SQLeanite/CoreFileEngine.lean &&
   grep -q 'CoreFileAdapter.requireWritableFormat paths.main' SQLeanite/CoreLazyWrite.lean &&
   grep -q 'CoreWALFileAdapter.requireWritableFormat paths' SQLeanite/CoreWALFileEngine.lean &&
   grep -q 'SQLite.HeaderVersion.writeError? (← committedHeader paths)' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'SQLite.HeaderVersion.readError? header' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'HeaderVersion.unknown_write' SQLeanite/ProofAxioms.lean; then
  ok "file and WAL header versions gate optimized reads and transaction writes"
else
  fail "file-format version admission is disconnected from execution"
fi

# Physical strides include reserved tails; record decoders receive usable bytes.
if grep -q 'pageBytes whole pageBytes pageNumber).map (List.take usable.val)' SQLeanite/CoreFileAdapter.lean &&
   grep -q '(read pageNumber).map (List.take usable.val)' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'requireUnreservedWrite paths.main' SQLeanite/CoreFileAdapter.lean &&
   grep -q 'unsupported reserved-byte database writes' SQLeanite/CoreWALFileAdapter.lean &&
   grep -q 'headerUsablePageSize?_partition' SQLeanite/ProofAxioms.lean; then
  ok "reserved tails are excluded from decoding and unsupported writers fail before publication"
else
  fail "reserved-page geometry or unsupported-write guards are disconnected"
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
   grep -q 'no-primary-key|pass|' scripts/run-reverse-differential.sh; then
  ok "remaining unsupported file shapes fail closed and implicit-rowid tables are accepted"
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
  elif grep -q '^Error: file is not a database$' "$tmp/bad.err" &&
      ! grep -q 'uncaught exception' "$tmp/bad.err"; then
    ok "corrupt input rejection is a normal diagnostic, not a crash"
  else
    fail "corrupt input rejection still looks like an uncaught crash"
  fi
  rm -r -- "$tmp"
else
  printf 'skip - binary or configured SQLite reference unavailable\n'
fi


if grep -q 'import SQLeanite.CoreNullConflict' SQLeanite/CoreSQL.lean &&
   grep -q 'schemaInsertRows state tableName stored.schema' SQLeanite/CoreSQL.lean &&
   grep -q 'executeSchemaUpdate state tableName' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreNullConflict.prepare stored.schema values old.isSome' SQLeanite/CoreDefaultConflict.lean &&
   grep -q 'notNullConflict == column.notNullConflict' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'notNullConflictChars column.notNullConflict' SQLeanite/CanonicalSchemaSQL.lean &&
   grep -q 'Core.Column.restoreNotNullConflict' SQLeanite/ProofAxioms.lean; then
  echo 'ok - schema NOT NULL policies reach checked writes and invertible persistence'
else
  echo 'FAIL - schema NOT NULL policy wiring is incomplete'
  exit 1
fi

if grep -q 'CoreDefaultConflict.plan stored values' SQLeanite/CoreSQL.lean &&
   grep -q 'schemaReplacementRows state tableName' SQLeanite/CoreSQL.lean &&
   grep -q 'primaryConflict == column.conflict' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'primaryConflictChars column.primaryConflict' SQLeanite/CanonicalSchemaSQL.lean &&
   grep -q 'CanonicalSchemaSQL.primaryFromBase_inverse' SQLeanite/ProofAxioms.lean &&
   grep -q 'CoreDefaultConflict.commands_last' SQLeanite/ProofAxioms.lean; then
  echo 'ok - primary-key schema policies use checked Core traces and invertible SQL'
else
  echo 'FAIL - primary-key schema policy wiring is incomplete'
  exit 1
fi
if grep -q 'ColumnDefault.fromSource source' SQLeanite/CoreSQL.lean &&
   grep -q 'Core.Column.defaultForInsert' SQLeanite/CoreSQL.lean &&
   grep -q 'column.defaultForRecord.toOption' SQLeanite/CoreRecord.lean &&
   grep -q 'ColumnDefault.evaluate spec' SQLeanite/CoreNullConflict.lean &&
   grep -q 'ColumnDefault.fromSource' SQLeanite/CanonicalSchemaSQL.lean &&
   grep -q 'matchDefault expression source' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'ColumnDefault.fromSource_spec' SQLeanite/ProofAxioms.lean; then
  echo 'ok - checked DEFAULT SQL reaches writes, conflict replacement and old-record decoding'
else
  echo 'FAIL - column DEFAULT wiring is incomplete'
  exit 1
fi
if grep -q 'expectConstraintName' SQLeanite/Parser.lean &&
   grep -q 'matchConstraintName' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'matchTableConstraints constraints' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'position == constraints.size' SQLeanite/CoreTokenGrammar.lean; then
  echo 'ok - named constraints retain exact constraint checks and validated name grammar'
else
  echo 'FAIL - named constraint grammar wiring is incomplete'
  exit 1
fi
if grep -q 'SQLite.ColumnType.valid typ' SQLeanite/Parser.lean &&
   grep -q 'matchDeclaredType column.declaredType' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'actual == source' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'Core.Column.typed definition.name' SQLeanite/CoreSQL.lean &&
   grep -q 'column.explicitEmptyType then .numeric' SQLeanite/Core.lean &&
   grep -q 'typeCaseChars column.declaredType' SQLeanite/CanonicalSchemaSQL.lean &&
   grep -q 'Core.Column.typed_empty_affinity' SQLeanite/ProofAxioms.lean; then
  echo 'ok - exact column type syntax and empty-type affinity reach invertible persistence'
else
  echo 'FAIL - column type grammar or affinity wiring is incomplete'
  exit 1
fi
if grep -q 'indexedType : Core.IndexedType' SQLeanite/CoreSQL.lean &&
   grep -q 'SQLite.PrimaryKey.canonical key' SQLeanite/Core.lean &&
   grep -q 'some .null => .rowid row.rowid' SQLeanite/Core.lean &&
   grep -q 'parseIndexedBody rest' SQLeanite/CanonicalSchemaSQL.lean &&
   grep -q 'PrimaryKey.canonical_compare' SQLeanite/ProofAxioms.lean &&
   grep -q 'Core.Row.declaredKey_null_ne_nonnull' SQLeanite/ProofAxioms.lean; then
  echo 'ok - indexed primary types retain SQL metadata and disjoint exact numeric lookup keys'
else
  echo 'FAIL - indexed primary type or lookup wiring is incomplete'
  exit 1
fi
if grep -q 'CoreAutoIncrement.prepare stored counter values' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreAutoIncrement.finish next counter' SQLeanite/CoreSQL.lean &&
   grep -q 'CoreAutoIncrement.ensure next' SQLeanite/CoreSQL.lean &&
   grep -q 'sawAutoIncrement == column.autoIncrement' SQLeanite/CoreTokenGrammar.lean &&
   grep -q 'parseAutoBody rest' SQLeanite/CanonicalSchemaSQL.lean &&
   grep -q 'stored.schema.autoIncrement then return none' SQLeanite/CoreFileEngine.lean &&
   grep -q 'schema.hasHiddenRowid || schema.autoIncrement' SQLeanite/CoreLazyWrite.lean &&
   grep -q 'CoreAutoIncrement.allocate_greater_maximum' SQLeanite/ProofAxioms.lean; then
  echo 'ok - AUTOINCREMENT uses checked statement counters, delayed sequence writes and complete file publication'
else
  echo 'FAIL - AUTOINCREMENT SQL, sequence or file wiring is incomplete'
  exit 1
fi
if rg -q 'CoreSavepoint.push' SQLeanite/CoreSQL.lean &&
   rg -q 'CoreSavepoint.rollbackTo' SQLeanite/CoreSQL.lean &&
   rg -q 'CoreSavepoint.release' SQLeanite/CoreSQL.lean &&
   rg -q 'CoreSavepoint.releasesTransaction' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'savepoints := []' SQLeanite/CoreEngine.lean &&
   rg -q 'remaining name state.savepoints' SQLeanite/CoreSavepoint.lean &&
   rg -q 'theorem rollbackTo_snapshot' SQLeanite/CoreSavepoint.lean &&
   rg -F -q '.rollbackTo name => do' SQLeanite/CoreTokenGrammar.lean; then
  echo 'ok - SAVEPOINT keeps named snapshots and publishes only the transaction-owning RELEASE'
else
  echo 'FAIL - SAVEPOINT execution, grammar or publication guard is missing'
  exit 1
fi

if rg -q 'def transactionChanged' SQLeanite/CoreFileEngine.lean &&
   rg -F -q '.commit => transactionChanged state' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreSavepoint.releasesTransaction state name && transactionChanged state' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreFileAdapter.requireWritableAccess connection.paths.main' SQLeanite/CoreFileEngine.lean; then
  echo 'ok - unchanged transactions skip publication and write dispatch checks access'
else
  echo 'FAIL - read-only transaction publication or line classification is incomplete'
  exit 1
fi

if rg -q 'SQLite.Script.split sql' SQLeanite/CoreFileEngine.lean &&
   rg -q 'SQLite.Script.split sql' SQLeanite/CoreWALFileEngine.lean &&
   rg -q 'SQLite.Script.split sql' Main.lean &&
   rg -q 'CoreTokenGrammar.parseStatements chunk' SQLeanite/CoreFileEngine.lean &&
   rg -q 'CoreTokenGrammar.parseStatements chunk' SQLeanite/CoreWALFileEngine.lean &&
   rg -q 'theorem split_preserves_source' SQLeanite/SQLite/Script.lean; then
  echo 'ok - script chunks preserve source and admit each statement before execution'
else
  echo 'FAIL - certified incremental script execution is incomplete'
  exit 1
fi

if rg -q 'SQLite.Identifier.nameToken token' SQLeanite/Parser.lean &&
   rg -q 'SQLite.Identifier.aliasToken' SQLeanite/Parser.lean &&
   rg -q 'SQLite.Identifier.windowNameToken next' SQLeanite/Parser.lean &&
   rg -q 'SQLite.Identifier.nameToken' SQLeanite/CoreTokenGrammar.lean &&
   rg -q 'SQLite.Identifier.primaryToken' SQLeanite/Parser.lean &&
   rg -q 'SQLite.Identifier.primaryToken' SQLeanite/CoreTokenGrammar.lean &&
   rg -q 'SQLite.Identifier.aliasToken' SQLeanite/CoreTokenGrammar.lean &&
   rg -q 'expectDeclaredName alias' SQLeanite/CoreTokenGrammar.lean &&
   rg -q 'Identifier.aliasToken token' SQLeanite/SQLite/ColumnType.lean; then
  echo 'ok - SQLite name and implicit-alias grammars are shared and independently replayed'
else
  echo 'FAIL - identifier grammar or exact alias replay is incomplete'
  exit 1
fi

if rg -q 'let typeName ← parseCastType' SQLeanite/Parser.lean &&
   rg -F -q 'matchCastType (name.drop 5).toString' SQLeanite/CoreTokenGrammar.lean &&
   rg -q 'SQLite.CastType.check source' SQLeanite/Parser.lean &&
   rg -q 'SQLite.CastType.check source' SQLeanite/CoreTokenGrammar.lean &&
   rg -q 'def affinity := SQLite.CastType.affinity' SQLeanite/SQLite/Scalar.lean; then
  echo 'ok - CAST type spans are independently validated and use explicit expression affinity'
else
  echo 'FAIL - CAST grammar or affinity wiring is incomplete'
  exit 1
fi

if rg -F -q 'if requiresWriteAccess live.state statement then' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'if CoreFileEngine.requiresWriteAccess state statement then' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreFileAdapter.requireWritableAccess connection.paths.main' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreFileAdapter.requireWritableAccess paths.main' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreFileAdapter.requireWritableAccess paths.main' SQLeanite/CoreLazyWrite.lean &&
   rg -F -q 'CoreFileEngine.executeObserved connection line printCoreResults' Main.lean &&
   rg -F -q 'CoreWALFileEngine.executeObserved .system paths sql printCoreResults' Main.lean &&
   rg -F -q 'onResults results' SQLeanite/CoreWALFileEngine.lean; then
  echo 'ok - completed statements emit in order and actual write dispatch checks OS access'
else
  echo 'FAIL - statement output or runtime write-access wiring is incomplete'
  exit 1
fi

if rg -F -q 'private def parseTransactionSuffix' SQLeanite/Parser.lean &&
   rg -F -q 'private def matchTransactionSuffix' SQLeanite/CoreTokenGrammar.lean &&
   rg -F -q 'discard <| acceptKeyword "deferred"' SQLeanite/Parser.lean &&
   rg -F -q 'discard <| acceptKeyword "deferred"' SQLeanite/CoreTokenGrammar.lean; then
  echo 'ok - DEFERRED and ignored TRANSACTION names are independently replayed'
else
  echo 'FAIL - transaction suffix grammar is incomplete'
  exit 1
fi

if rg -F -q 'SQLite.Limit.resolve clause' SQLeanite/Parser.lean &&
   rg -F -q 'SQLite.Limit.resolve clause' SQLeanite/CoreTokenGrammar.lean &&
   rg -F -q 'matchExpr clause.count' SQLeanite/CoreTokenGrammar.lean &&
   rg -F -q 'SQLite.Limit.validate query.limitClause' SQLeanite/CoreSQL.lean &&
   rg -F -q 'Numeric.applyAffinity value' SQLeanite/SQLite/Limit.lean &&
   rg -F -q 'let skip ← if count == 0 then pure 0' SQLeanite/SQLite/Limit.lean; then
  echo 'ok - LIMIT expression tokens and normalized windows are independently checked'
else
  echo 'FAIL - LIMIT expression evaluation or token replay is disconnected'
  exit 1
fi

if rg -F -q '!dataWriteNoop live.state executed.state statement results' SQLeanite/CoreFileEngine.lean &&
   rg -F -q '!CoreFileEngine.dataWriteNoop state next statement results' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'current.database.contents == next.database.contents' SQLeanite/CoreFileEngine.lean; then
  echo 'ok - zero-row DML publication checks complete contents including sequence rows'
else
  echo 'FAIL - zero-row DML publication guard is disconnected'
  exit 1
fi

if rg -F -q 'SQLite.JoinType.classify words.toList' SQLeanite/Parser.lean &&
   rg -F -q 'SQLite.JoinType.classify words' SQLeanite/CoreTokenGrammar.lean &&
   rg -F -q 'source.crossJoin == kind.cross' SQLeanite/CoreTokenGrammar.lean &&
   rg -F -q 'rightSource.joinOn.mapM (fun expression => joinPredicate context expression (rightSource.leftJoin || rightSource.rightJoin))' SQLeanite/CoreSQL.lean; then
  echo 'ok - join keywords and optional ON reach the existing Core join semantics'
else
  echo 'FAIL - join-type replay or optional predicate lowering is disconnected'
  exit 1
fi

if rg -F -q 'return .coercedColumn aff reference' SQLeanite/CoreSQL.lean &&
   rg -F -q 'SQLite.PhysicalAffinity.comparison affinity (reference.value row)' SQLeanite/CoreJoin.lean &&
   rg -F -q '.coercedColumn affinity (joinColumnPath reference)' SQLeanite/CoreOptimizerBridge.lean &&
   rg -F -q 'SQLite.PhysicalAffinity.comparison affinity (row.lookup path)' SQLeanite/QuerySemantics.lean; then
  echo 'ok - stored join-column affinity is preserved through optimizer translation and execution'
else
  echo 'FAIL - join-column comparison conversion is disconnected'
  exit 1
fi

if rg -F -q 'CoreJoinUsing.columns leftSchema rightSchema rightSource' SQLeanite/CoreSQL.lean &&
   rg -F -q 'let sharedOn ← joinUsingPredicate context' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreJoinUsing.suppressesRight context.shared index' SQLeanite/CoreCreateTableAs.lean &&
   rg -F -q 'source.usingColumns.toList' SQLeanite/CoreTokenGrammar.lean; then
  echo 'ok - USING/NATURAL names, predicates, merged columns and CTAS share declared-column metadata'
else
  echo 'FAIL - shared join-column semantics are disconnected'
  exit 1
fi

if rg -q 'distinctRows query.columns rows' SQLeanite/CoreJoin.lean &&
   rg -q 'orderedRows rows.*drop query.offset' SQLeanite/CoreJoin.lean &&
   rg -q 'offset := select.offset' SQLeanite/CoreSQL.lean &&
   rg -q 'distinct := select.distinct' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem distinctRows_key_nodup' SQLeanite/CoreJoin.lean &&
   rg -q 'distinctScanOrder := joinDistinctScanOrder' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem Query.distinctInputRows_perm' SQLeanite/CoreJoin.lean; then
  echo 'ok - join DISTINCT retains original representatives before ordering and OFFSET/LIMIT'
else
  echo 'FAIL - join DISTINCT/window live-path audit failed' >&2
  status=1
fi

if rg -q 'let orderColumns ← joinOrderColumns context' SQLeanite/CoreSQL.lean &&
   rg -q 'CoreOrder.ordinal' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem joinOrderColumns_projection' SQLeanite/CoreSQL.lean &&
   rg -q 'a result star without an alias' SQLeanite/CoreTokenGrammar.lean; then
  echo 'ok - join ORDER BY aliases and positions use the exact expanded projection'
else
  echo 'FAIL - join ORDER BY name/position live-path audit failed' >&2
  status=1
fi

if rg -q 'let specification ← CoreOrder.specification term' SQLeanite/CoreSQL.lean &&
   rg -q 'CoreOrder.keyExpression expression' SQLeanite/CoreSQL.lean &&
   rg -q 'nullsFirst := some specification.nullsFirst' SQLeanite/CoreSQL.lean &&
   rg -q 'collation := specification.collation' SQLeanite/CoreSQL.lean &&
   rg -q 'orderedRowLe query.orderBy' SQLeanite/CoreJoin.lean &&
   rg -q 'SQLite.Collation.compareValue term.collation' SQLeanite/CoreJoin.lean; then
  echo 'ok - join ordering carries explicit NULL placement and collation into the stable sorter'
else
  echo 'FAIL - join NULL/collation ordering live-path audit failed' >&2
  status=1
fi

if rg -F -q 'joinResultExpr context (joinBindNames context column.expr)' SQLeanite/CoreSQL.lean &&
   rg -F -q 'match joinColumnAtom? bound with' SQLeanite/CoreSQL.lean &&
   rg -q 'columns : List Operand' SQLeanite/CoreJoin.lean &&
   rg -q 'theorem projectRow_columns' SQLeanite/CoreJoin.lean &&
   rg -q 'bindNamesFuel_preserves_collation' SQLeanite/CoreCollationRead.lean &&
   rg -q 'JoinOperandSyntax.bound context expression' SQLeanite/CoreSQLGrammar.lean; then
  echo 'ok - joined literal/name atoms preserve column values, grammar and projection collation'
else
  echo 'FAIL - joined literal/name atom live-path audit failed' >&2
  status=1
fi

if rg -F -q 'schema.column? name' SQLeanite/CoreSQL.lean &&
   rg -F -q 'ctx.schema.column? name' SQLeanite/CoreExpr.lean &&
   rg -F -q 'schema.declaredColumn? name' SQLeanite/CoreJoinUsing.lean &&
   rg -q 'theorem Schema.column_visible_or_rowid' SQLeanite/Core.lean &&
   rg -F -q 'schema.catalogColumns.findIdx?' SQLeanite/CoreSQL.lean; then
  echo 'ok - SQL column binding shares visible names and explicit rowid aliases'
else
  echo 'FAIL - SQL column visibility live-path audit failed' >&2
  status=1
fi

if rg -F -q 'CoreJoinUsing.nameCandidates sources none columnName' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreJoinUsing.nameCandidates context.sources qualifier name' SQLeanite/CoreCreateTableAs.lean &&
   rg -q 'theorem nameCandidates_declared' SQLeanite/CoreJoinUsing.lean &&
   rg -q 'let rows := query.lookupInputRows rows' SQLeanite/CoreJoin.lean &&
   rg -q 'let lookupScanOrder := joinLookupScanOrder' SQLeanite/CoreSQL.lean; then
  echo 'ok - joined declared-name priority is shared with CTAS metadata'
else
  echo 'FAIL - joined declared-name priority live-path audit failed' >&2
  status=1
fi

if rg -F -q 'let prepared := SQLite.Scalar.prepare (joinBindNames context expression)' SQLeanite/CoreSQL.lean &&
   rg -F -q 'SQLite.PhysicalAffinity.truth (operand.value row)' SQLeanite/CoreJoin.lean &&
   rg -F -q 'Numeric.truth (.textBytes value.bytes.toArray)' SQLeanite/SQLite/PhysicalAffinity.lean &&
   rg -F -q '.operandTruthy (joinOperand operand)' SQLeanite/CoreOptimizerBridge.lean &&
   rg -q 'JoinPredicateSyntax expression' SQLeanite/CoreSQLGrammar.lean; then
  echo 'ok - joined truth atoms share numeric-prefix conversion and a proved optimizer embedding'
else
  echo 'FAIL - joined truth atom live-path audit failed' >&2
  status=1
fi

if rg -F -q 'joinIsComparison context false left right' SQLeanite/CoreSQL.lean &&
   rg -F -q 'joinIsComparison context true left right' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem Predicate.isEqual_present' SQLeanite/CoreJoin.lean &&
   rg -q 'theorem Predicate.isTruth_null' SQLeanite/CoreJoin.lean &&
   rg -q 'joinIsComparisonSyntax_of_success' SQLeanite/CoreSQLGrammar.lean &&
   rg -F -q 'CoreJoin.Predicate.withCollation kind' SQLeanite/CoreSQL.lean &&
   rg -F -q 'isTruthKeyword? right' SQLeanite/CoreSQL.lean &&
   rg -q 'joinOperandAffinity_plus' SQLeanite/CoreSQL.lean; then
  echo 'ok - joined IS comparisons distinguish NULL-safe equality and keyword truth tests'
else
  echo 'FAIL - joined IS comparison live-path audit failed' >&2
  status=1
fi

if rg -F -q 'joinInList context argument values negated affinity' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreJoin.Predicate.membership kind left right' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem Predicate.membership_eval' SQLeanite/CoreJoin.lean &&
   rg -q 'theorem Predicate.membership_null' SQLeanite/CoreJoin.lean &&
   rg -q 'joinInListSyntax_of_success' SQLeanite/CoreSQLGrammar.lean; then
  echo 'ok - joined IN lists preserve left affinity, nullable equality and positive grammar'
else
  echo 'FAIL - joined IN-list live-path audit failed' >&2
  status=1
fi

if rg -F -q '| .isNull arg negated => prepareNullTest (prepare arg) negated' SQLeanite/SQLite/Scalar.lean &&
   rg -F -q '| .is, .literal .null _ => prepareNullTest a false' SQLeanite/SQLite/Scalar.lean &&
   rg -q 'theorem prepareNullTest_token' SQLeanite/SQLite/Scalar.lean &&
   rg -q 'theorem parserNonNullLiteral_collate' SQLeanite/SQLite/Scalar.lean; then
  echo 'ok - literal NULL tests use parser token classification before scalar admission'
else
  echo 'FAIL - literal NULL preparation live-path audit failed' >&2
  status=1
fi

if rg -F -q 'SQLite.StaticCondition.classify outer prepared' SQLeanite/CoreSQL.lean &&
   rg -F -q 'unless joinStaticAdmitted context prepared outer' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem staticTerms_correct' SQLeanite/SQLite/StaticCondition.lean &&
   rg -F -q 'abbrev ignoredForbidden := SQLite.StaticCondition.resolutionForbidden' SQLeanite/CoreAggregateOrdering.lean &&
   rg -q 'theorem Predicate.constant_eval' SQLeanite/CoreJoin.lean; then
  echo 'ok - static joined conditions retain resolution and code-generation checks'
else
  echo 'FAIL - static joined condition live-path audit failed' >&2
  status=1
fi

if rg -F -q 'let query ← joinAliasQuery select leftTable rightTable left.schema right.schema left.rows right.rows' SQLeanite/CoreSQL.lean &&
   rg -F -q '(CoreSQL.joinQueryWithZero select leftName rightName' SQLeanite/CoreLazyFileEngine.lean &&
   rg -F -q 'unless joinStaticAdmitted context prepared rightSource.leftJoin' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem joinZeroQuery_limit' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem Query.eval_limit_zero' SQLeanite/CoreJoin.lean; then
  echo 'ok - zero-LIMIT joins validate predicates without evaluating their values'
else
  echo 'FAIL - zero-LIMIT join live-path audit failed' >&2
  status=1
fi

if rg -F -q 'unless rightSource.leftJoin && (leftRows.isEmpty || rightRows.isEmpty)' SQLeanite/CoreSQL.lean &&
   rg -F -q 'unless joinStaticAdmitted context prepared true' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem Query.eval_empty_left' SQLeanite/CoreJoin.lean &&
   rg -q 'theorem Query.eval_empty_right_on' SQLeanite/CoreJoin.lean &&
   rg -q 'theorem joinQueryForRows_existing' SQLeanite/CoreSQL.lean; then
  echo 'ok - empty-side outer ON keeps validation and preserves the existing join path'
else
  echo 'FAIL - empty-side outer ON live-path audit failed' >&2
  status=1
fi

if rg -F -q 'let (columns, names) ← joinWrappedColumns context select.columns.toList' SQLeanite/CoreSQL.lean &&
   rg -F -q 'joinWrappedOrderBy context orderColumns names select.orderBy.toList' SQLeanite/CoreSQL.lean &&
   rg -F -q 'if query.distinct then query.distinctOutputRows rows else rows' SQLeanite/CoreJoin.lean &&
   rg -q 'theorem distinctCollatedRows_pairwise' SQLeanite/CoreJoin.lean &&
   rg -q 'theorem joinQueryComplete_existing' SQLeanite/CoreSQL.lean; then
  echo 'ok - joined projection wrappers retain DISTINCT and ORDER BY collations'
else
  echo 'FAIL - joined projection wrapper live-path audit failed' >&2
  status=1
fi

if rg -F -q 'if rightSource.rightJoin then return ← executeRightJoin state select leftSource rightSource' SQLeanite/CoreSQL.lean &&
   rg -F -q 'source.leftJoin == kind.left && source.rightJoin == kind.right' SQLeanite/CoreTokenGrammar.lean &&
   rg -F -q 'CoreOuterJoin.eval rightSource.leftJoin left.schema.columns.length query left.rows right.rows' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem unmatchedRights_member' SQLeanite/CoreOuterJoin.lean &&
   rg -q 'theorem eval_width' SQLeanite/CoreOuterJoin.lean &&
   rg -q 'theorem executeRightJoin_preserves_state' SQLeanite/CoreSQL.lean; then
  echo 'ok - RIGHT/FULL ON joins track unmatched right rows before WHERE filtering'
else
  echo 'FAIL - RIGHT/FULL join live-path audit failed' >&2
  status=1
fi

if rg -F -q 'preferRightShared := rightSource.rightJoin && !rightSource.leftJoin' SQLeanite/CoreSQL.lean &&
   rg -F -q '.column (joinMergedStar context reference)' SQLeanite/CoreSQL.lean &&
   rg -F -q 'starMetadata context qualifier sourceIndex index derived' SQLeanite/CoreCreateTableAs.lean &&
   rg -q 'theorem joinMergedStar_right' SQLeanite/CoreSQL.lean &&
   rg -q 'theorem starMetadata_name' SQLeanite/CoreCreateTableAs.lean; then
  echo 'ok - RIGHT shared-name binding selects right values and preserves star names'
else
  echo 'FAIL - RIGHT shared-name live-path audit failed' >&2
  status=1
fi

if rg -F -q 'coalesceShared := rightSource.rightJoin && rightSource.leftJoin' SQLeanite/CoreSQL.lean &&
   rg -F -q 'def joinNamedOperand' SQLeanite/CoreSQL.lean &&
   rg -F -q 'def joinStarOperand' SQLeanite/CoreSQL.lean &&
   rg -F -q 'joinFullOrderBy context orderColumns names select.orderBy.toList' SQLeanite/CoreSQL.lean &&
   rg -F -q 'term.compareValues (term.value left) (term.value right)' SQLeanite/CoreJoin.lean &&
   rg -F -q 'mergedExpression context named' SQLeanite/CoreCreateTableAs.lean &&
   rg -F -q 'CoreJoin.Operand.mergedColumn_missing' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreJoin.Operand.mergedColumn_present' SQLeanite/ProofAxioms.lean; then
  printf 'ok - FULL shared names coalesce values and retain source affinity and ordering\n'
else
  printf 'live-path check FAILED: FULL shared-column interpretation\n' >&2
  status=1
fi

if rg -F -q 'let query ← joinAliasQuery select leftTable rightTable left.schema right.schema left.rows right.rows' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreOrder.resolveAliasesWith (joinHasColumn context) select.columns.toList' SQLeanite/CoreSQL.lean &&
   rg -F -q 'match joinAliasQuery { select with orderBy := #[], offset := 0 }' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreOrder.resolveNamesFuelWith_source' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreOrder.resolveNamesFuelWith_alias' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreSQL.joinAliasQuery_existing' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreOrder.resolveJoinOnTerm_alias' SQLeanite/ProofAxioms.lean; then
  printf 'ok - joined ON/WHERE aliases preserve source priority and original result expressions\n'
else
  printf 'live-path check FAILED: joined predicate aliases\n' >&2
  status=1
fi

if rg -F -q 'columns := ← joinCompoundColumns context select.columns.toList' SQLeanite/CoreSQL.lean &&
   rg -F -q 'bindExpression := some (fun expression => joinCompoundBind context' SQLeanite/CoreSQL.lean &&
   rg -F -q 'if let some bind := arm.bindExpression then' SQLeanite/CoreCompoundTail.lean &&
   rg -F -q 'CoreSQL.joinCompoundStarColumns_projection' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreSQL.joinCompoundOperand_sides' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreSQL.joinCompoundOperand_merged' SQLeanite/ProofAxioms.lean; then
  printf 'ok - joined compound ORDER BY uses expanded result slots and bound source identities\n'
else
  printf 'live-path check FAILED: joined compound result binding\n' >&2
  status=1
fi

if rg -F -q 'let base ← executeSelectBaseComplete state { select with compounds := #[] }' SQLeanite/CoreSQL.lean &&
   rg -F -q '| .error _ => executeJoinScalar state select' SQLeanite/CoreSQL.lean &&
   rg -F -q 'let prepared ← joinScalarPrepare context' SQLeanite/CoreSQL.lean &&
   rg -F -q 'arguments.toList.findSome? effectiveName' SQLeanite/SQLite/ExprCollation.lean &&
   rg -F -q 'let collations ← resultCollationsFuel query.compoundHeight state query' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.executeJoinScalar_preserves_state' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreSQLReadText.executeSelectBaseComplete_eq_core' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreSQL.joinScalarRowsM_pure' SQLeanite/ProofAxioms.lean; then
  printf 'ok - joined expression fallback binds original sources and preserves existing Core reads\n'
else
  printf 'live-path check FAILED: joined expression fallback\n' >&2
  status=1
fi

if rg -F -q 'let source := joinScalarReducedSource context prepared originalRight' SQLeanite/CoreSQL.lean &&
   rg -F -q 'joinSearchRows context prepared source plan traversal.exchanged inner outer' SQLeanite/CoreSQL.lean &&
   rg -F -q 'joinScalarOnlySide context prepared outerSide term' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.joinScalarNullWalk_or' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreSQL.joinScalarReducedSource_no_new_outer' SQLeanite/ProofAxioms.lean; then
  printf 'ok - joined expression scans preserve source direction and conservative outer reduction\n'
else
  printf 'live-path check FAILED: joined expression scan planning\n' >&2
  status=1
fi

if rg -F -q '(joinScalarReadReport state select).toExcept' SQLeanite/CoreSQL.lean &&
   rg -F -q 'if state.stopped then state' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.observeJoinedSelect? state select' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreSQL.observeJoinedSelect? state select' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'onResults [observed.execution.result]' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'onResults [observed.execution.result]' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreFileEngine.executeObserved connection line printCoreResults' Main.lean &&
   rg -F -q 'CoreSQL.observeJoinedSelect_refines' SQLeanite/ProofAxioms.lean; then
  printf 'ok - joined streaming reads retain emitted prefixes and erase to ordinary Core execution\n'
else
  printf 'live-path check FAILED: joined read observation or streaming path\n' >&2
  status=1
fi

if rg -F -q 'joinSearchCandidates context prepared source exchanged outer plan.access inner' SQLeanite/CoreSQL.lean &&
   rg -F -q 'let plan := joinSearchPlan context prepared source traversal on' SQLeanite/CoreSQL.lean &&
   rg -F -q 'let outer ← match traversal.root with' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.joinSearchCandidates_point_error' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreSQL.joinSearchCandidates_automatic_empty' SQLeanite/ProofAxioms.lean; then
  printf 'ok - joined cursor initialization preserves computed key errors and empty scan termination\n'
else
  printf 'live-path check FAILED: joined cursor initialization\n' >&2
  status=1
fi

if rg -F -q 'joinSearchTransitiveRoot context prepared on' SQLeanite/CoreSQL.lean &&
   rg -F -q 'joinSearchRangeRoot context prepared outerSide on' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.joinRightBoundForRows_where_failure' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreSQL.joinEmptyOnQuery_where_failure' SQLeanite/ProofAxioms.lean; then
  printf 'ok - empty join adapters retain WHERE planning and propagate rowid bounds\n'
else
  printf 'live-path check FAILED: reduced join cursors and rowid bounds\n' >&2
  status=1
fi

if rg -F -q 'joinSearchNullFilterRoot context prepared on' SQLeanite/CoreSQL.lean &&
   rg -F -q 'if select.limit == some 0 || joinScalarKnownEmpty context prepared source' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.joinScalarNullRejectsVisit_unpeeled_notNull' SQLeanite/ProofAxioms.lean; then
  echo "ok - joined nonnull-rowid filters and ordered null-test preparation remain live"
else
  echo "not ok - joined null-filter preparation is not wired into execution"
  status=1
fi

if rg -F -q 'joinFixedMatches prepared input plan.fixed early' SQLeanite/CoreSQL.lean &&
   rg -F -q 'joinSearchMatches context prepared source plan row' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.joinFixedLookup_unfixed' SQLeanite/ProofAxioms.lean &&
   rg -F -q 'CoreSQL.joinSearchMatches_without_inner_filter' SQLeanite/ProofAxioms.lean; then
  echo "ok - joined fixed-column preparation and inner WHERE filters remain live"
else
  echo "not ok - joined fixed-column or inner filter execution is missing"
  status=1
fi

if rg -F -q 'joinSearchKeys context prepared side terms' SQLeanite/CoreSQL.lean &&
   rg -F -q 'joinSearchDerivedRightRoot context prepared leftRoot on' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.joinSearchKeyOrder_perm' SQLeanite/ProofAxioms.lean; then
  echo "ok - original and virtual joined search constraints preserve every candidate"
else
  echo "not ok - joined search term ordering is not wired into execution"
  status=1
fi

if rg -F -q 'joinScalarColumnNotNull context ref' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.joinScalarOriginallyNullable_outer' SQLeanite/ProofAxioms.lean; then
  echo "ok - declared non-null columns retain outer-source preparation metadata"
else
  echo "not ok - declared join nullability is not wired into execution"
  status=1
fi

if rg -F -q 'joinFixedConstantMatches context prepared source on' SQLeanite/CoreSQL.lean &&
   rg -F -q 'joinSearchNullFilterCount context prepared .right > joinSearchNullFilterCount context prepared .left' SQLeanite/CoreSQL.lean &&
   rg -F -q 'CoreSQL.joinFixedConstantMatches_outer' SQLeanite/ProofAxioms.lean; then
  echo "ok - fixed WHERE constants and retained null filters drive joined cursor preparation"
else
  echo "not ok - fixed WHERE or retained null-filter preparation is missing"
  status=1
fi

exit $status
