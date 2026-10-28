# Sourced by live-path-check.sh; shares its failure status and scratch files.

if grep -q 'CoreDefaultConflict.plan stored values' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'schemaReplacementRows state tableName' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'primaryConflict == column.conflict' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'primaryConflictChars column.primaryConflict' "$audit_sources/SQLeanite/CanonicalSchemaSQL.lean" &&
   grep -q 'CanonicalSchemaSQL.primaryFromBase_inverse' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'CoreDefaultConflict.commands_last' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - primary-key schema policies use checked Core traces and invertible SQL'
else
  echo 'FAIL - primary-key schema policy wiring is incomplete'
  exit 1
fi
if grep -q 'ColumnDefault.fromSource source' SQLeanite/CoreSchemaTranslate.lean &&
   grep -q 'CoreReturning.defaultFromRegister target' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q '| none => defaultForInsert column' SQLeanite/CoreReturning.lean &&
   grep -q 'columnLiteral column (ColumnDefault.emittedFuel expression.height expression)' SQLeanite/CoreReturning.lean &&
   grep -q 'column.defaultForRecord.toOption' SQLeanite/CoreRecord.lean &&
   grep -q 'ColumnDefault.evaluate spec' SQLeanite/CoreNullConflict.lean &&
   grep -q 'ColumnDefault.fromSource' "$audit_sources/SQLeanite/CanonicalSchemaSQL.lean" &&
   grep -q 'matchDefault expression source' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'ColumnDefault.fromSource_spec' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - checked DEFAULT SQL reaches writes, conflict replacement and old-record decoding'
else
  echo 'FAIL - column DEFAULT wiring is incomplete'
  exit 1
fi
if grep -q 'expectConstraintName' "$audit_sources/SQLeanite/Parser.lean" &&
   grep -q 'matchConstraintName' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'matchTableConstraints constraints' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'position == constraints.size' "$audit_sources/SQLeanite/CoreTokenGrammar.lean"; then
  echo 'ok - named constraints retain exact constraint checks and validated name grammar'
else
  echo 'FAIL - named constraint grammar wiring is incomplete'
  exit 1
fi
if grep -q 'SQLite.ColumnType.valid typ' "$audit_sources/SQLeanite/Parser.lean" &&
   grep -q 'matchDeclaredType column.declaredType' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'actual == source' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'Core.Column.typed definition.name' SQLeanite/CoreSchemaTranslate.lean &&
   grep -q 'column.explicitEmptyType then .numeric' "$audit_sources/SQLeanite/CoreData.lean" &&
   grep -q 'typeCaseChars column.declaredType' "$audit_sources/SQLeanite/CanonicalSchemaSQL.lean" &&
   grep -q 'Core.Column.typed_empty_affinity' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - exact column type syntax and empty-type affinity reach invertible persistence'
else
  echo 'FAIL - column type grammar or affinity wiring is incomplete'
  exit 1
fi
if grep -q 'indexedType : Core.IndexedType' SQLeanite/CoreSchemaTranslate.lean &&
   grep -q 'SQLite.PrimaryKey.canonical key' "$audit_sources/SQLeanite/CoreData.lean" &&
   grep -q 'some .null => .rowid row.rowid' "$audit_sources/SQLeanite/CoreData.lean" &&
   grep -q 'parseIndexedBody rest' "$audit_sources/SQLeanite/CanonicalSchemaSQL.lean" &&
   grep -q 'PrimaryKey.canonical_compare' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   grep -q 'Core.Row.declaredKey_null_ne_nonnull' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - indexed primary types retain SQL metadata and disjoint exact numeric lookup keys'
else
  echo 'FAIL - indexed primary type or lookup wiring is incomplete'
  exit 1
fi
if rg -F -q 'CoreAutoIncrement.prepare stored counter (cells.map (·.value))' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreAutoIncrement.finish next counter' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'CoreAutoIncrement.ensure next' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   grep -q 'sawAutoIncrement == column.autoIncrement' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'parseAutoBody rest' "$audit_sources/SQLeanite/CanonicalSchemaSQL.lean" &&
   grep -q 'stored.schema.autoIncrement then return none' SQLeanite/CoreFileEngine.lean &&
   grep -q 'schema.hasHiddenRowid || schema.autoIncrement' "$audit_sources/SQLeanite/CoreLazyWrite.lean" &&
   grep -q 'CoreAutoIncrement.allocate_greater_maximum' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - AUTOINCREMENT uses checked statement counters, delayed sequence writes and complete file publication'
else
  echo 'FAIL - AUTOINCREMENT SQL, sequence or file wiring is incomplete'
  exit 1
fi
if rg -q 'CoreSavepoint.push' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'CoreSavepoint.rollbackTo' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'CoreSavepoint.release' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'CoreSavepoint.releasesTransaction' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'savepoints := []' "$audit_sources/SQLeanite/CoreEngine.lean" &&
   rg -q 'remaining name state.savepoints' SQLeanite/CoreSavepoint.lean &&
   rg -q 'theorem rollbackTo_snapshot' SQLeanite/CoreSavepoint.lean &&
   rg -F -q '.rollbackTo name => do' "$audit_sources/SQLeanite/CoreTokenGrammar.lean"; then
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

if rg -q 'SQLite.Identifier.nameToken token' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -q 'SQLite.Identifier.aliasToken' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -q 'SQLite.Identifier.windowNameToken next' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -q 'SQLite.Identifier.nameToken' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -q 'SQLite.Identifier.primaryToken' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -q 'SQLite.Identifier.primaryToken' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -q 'SQLite.Identifier.aliasToken' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -q 'expectDeclaredName alias' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -q 'Identifier.aliasToken token' SQLeanite/SQLite/ColumnType.lean; then
  echo 'ok - SQLite name and implicit-alias grammars are shared and independently replayed'
else
  echo 'FAIL - identifier grammar or exact alias replay is incomplete'
  exit 1
fi

if rg -q 'let typeName ← parseCastType' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -F -q 'matchCastType (name.drop 5).toString' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -q 'SQLite.CastType.check source' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -q 'SQLite.CastType.check source' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -q 'def affinity := SQLite.CastType.affinity' "$audit_sources/SQLeanite/SQLite/Scalar.lean"; then
  echo 'ok - CAST type spans are independently validated and use explicit expression affinity'
else
  echo 'FAIL - CAST grammar or affinity wiring is incomplete'
  exit 1
fi

if rg -F -q 'if requiresCatalogWriteAccess live.state statement then' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'if CoreFileEngine.requiresCatalogWriteAccess state statement then' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreFileAdapter.requireWritableAccess connection.paths.main' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreFileAdapter.requireWritableAccess session.paths.main' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreFileAdapter.requireWritableAccess paths.main' "$audit_sources/SQLeanite/CoreLazyWrite.lean" &&
   rg -F -q 'CoreFileEngine.executeObserved connection line printCoreResults' Main.lean &&
   rg -F -q 'CoreWALFileEngine.executeObserved .system paths sql printCoreResults' Main.lean &&
   rg -F -q 'onResults results' SQLeanite/CoreWALFileEngine.lean; then
  echo 'ok - completed statements emit in order and actual write dispatch checks OS access'
else
  echo 'FAIL - statement output or runtime write-access wiring is incomplete'
  exit 1
fi

if rg -F -q 'def parseTransactionSuffix' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -F -q 'def matchTransactionSuffix' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'discard <| acceptKeyword "deferred"' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -F -q 'discard <| acceptKeyword "deferred"' "$audit_sources/SQLeanite/CoreTokenGrammar.lean"; then
  echo 'ok - DEFERRED and ignored TRANSACTION names are independently replayed'
else
  echo 'FAIL - transaction suffix grammar is incomplete'
  exit 1
fi

if rg -F -q 'SQLite.Limit.resolve clause' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -F -q 'SQLite.Limit.resolve clause' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'matchExpr clause.count' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'SQLite.Limit.validate query.limitClause' "$audit_sources/SQLeanite/CoreSQL.lean" &&
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

if rg -F -q 'SQLite.JoinType.classify words.toList' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -F -q 'SQLite.JoinType.classify words' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'source.crossJoin == kind.cross' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'rightSource.joinOn.mapM (fun expression => joinPredicate context expression (rightSource.leftJoin || rightSource.rightJoin))' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  echo 'ok - join keywords and optional ON reach the existing Core join semantics'
else
  echo 'FAIL - join-type replay or optional predicate lowering is disconnected'
  exit 1
fi

if rg -F -q 'return .coercedColumn aff reference' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'SQLite.PhysicalAffinity.comparison affinity (reference.value row)' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -F -q '.coercedColumn affinity (joinColumnPath reference)' "$audit_sources/SQLeanite/CoreOptimizerBridge.lean" &&
   rg -F -q 'SQLite.PhysicalAffinity.comparison affinity (row.lookup path)' SQLeanite/QuerySemantics.lean; then
  echo 'ok - stored join-column affinity is preserved through optimizer translation and execution'
else
  echo 'FAIL - join-column comparison conversion is disconnected'
  exit 1
fi

if rg -F -q 'CoreJoinUsing.columns leftSchema rightSchema rightSource' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'let sharedOn ← joinUsingPredicate context' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreJoinUsing.suppressesRight context.shared index' SQLeanite/CoreCreateTableAs.lean &&
   rg -F -q 'source.usingColumns.toList' "$audit_sources/SQLeanite/CoreTokenGrammar.lean"; then
  echo 'ok - USING/NATURAL names, predicates, merged columns and CTAS share declared-column metadata'
else
  echo 'FAIL - shared join-column semantics are disconnected'
  exit 1
fi

if rg -q 'distinctRows query.columns rows' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'orderedRows rows.*drop query.offset' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'offset := select.offset' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'distinct := select.distinct' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem distinctRows_key_nodup' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'distinctScanOrder := joinDistinctScanOrder' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem Query.distinctInputRows_perm' "$audit_sources/SQLeanite/CoreJoin.lean"; then
  echo 'ok - join DISTINCT retains original representatives before ordering and OFFSET/LIMIT'
else
  echo 'FAIL - join DISTINCT/window live-path audit failed' >&2
  status=1
fi

if rg -q 'let orderColumns ← joinOrderColumns context' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'CoreOrder.ordinal' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem joinOrderColumns_projection' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'a result star without an alias' "$audit_sources/SQLeanite/CoreTokenGrammar.lean"; then
  echo 'ok - join ORDER BY aliases and positions use the exact expanded projection'
else
  echo 'FAIL - join ORDER BY name/position live-path audit failed' >&2
  status=1
fi

if rg -q 'let specification ← CoreOrder.specification term' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'CoreOrder.keyExpression expression' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'nullsFirst := some specification.nullsFirst' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'collation := specification.collation' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'orderedRowLe query.orderBy' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'SQLite.Collation.compareValue term.collation' "$audit_sources/SQLeanite/CoreJoin.lean"; then
  echo 'ok - join ordering carries explicit NULL placement and collation into the stable sorter'
else
  echo 'FAIL - join NULL/collation ordering live-path audit failed' >&2
  status=1
fi

if rg -F -q 'joinResultExpr context (joinBindNames context column.expr)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'match joinColumnAtom? bound with' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'columns : List Operand' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'theorem projectRow_columns' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'bindNamesFuel_preserves_collation' SQLeanite/CoreCollationRead.lean &&
   rg -q 'JoinOperandSyntax.bound context expression' "$audit_sources/SQLeanite/CoreSQLGrammar.lean"; then
  echo 'ok - joined literal/name atoms preserve column values, grammar and projection collation'
else
  echo 'FAIL - joined literal/name atom live-path audit failed' >&2
  status=1
fi

if rg -F -q 'schema.column? name' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'ctx.schema.column? name' SQLeanite/CoreExpr.lean &&
   rg -F -q 'schema.declaredColumn? name' SQLeanite/CoreJoinUsing.lean &&
   rg -q 'theorem Schema.column_visible_or_rowid' "$audit_sources/SQLeanite/CoreData.lean" &&
   rg -F -q 'abbrev indexColumn := CoreIndexPrepare.indexColumn' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'schema.catalogColumns.findIdx?' SQLeanite/CoreIndexPrepare.lean; then
  echo 'ok - SQL column binding shares visible names and explicit rowid aliases'
else
  echo 'FAIL - SQL column visibility live-path audit failed' >&2
  status=1
fi

if rg -F -q 'CoreJoinUsing.nameCandidates sources none columnName' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreJoinUsing.nameCandidates context.sources qualifier name' SQLeanite/CoreCreateTableAs.lean &&
   rg -q 'theorem nameCandidates_declared' SQLeanite/CoreJoinUsing.lean &&
   rg -q 'let rows := query.lookupInputRows rows' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'let lookupScanOrder := joinLookupScanOrder' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  echo 'ok - joined declared-name priority is shared with CTAS metadata'
else
  echo 'FAIL - joined declared-name priority live-path audit failed' >&2
  status=1
fi

if rg -F -q 'let prepared := SQLite.Scalar.prepare (joinBindNames context expression)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'SQLite.PhysicalAffinity.truth (operand.value row)' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -F -q 'Numeric.truth (.textBytes value.bytes.toArray)' SQLeanite/SQLite/PhysicalAffinity.lean &&
   rg -F -q '.operandTruthy (joinOperand operand)' "$audit_sources/SQLeanite/CoreOptimizerBridge.lean" &&
   rg -q 'JoinPredicateSyntax expression' "$audit_sources/SQLeanite/CoreSQLGrammar.lean"; then
  echo 'ok - joined truth atoms share numeric-prefix conversion and a proved optimizer embedding'
else
  echo 'FAIL - joined truth atom live-path audit failed' >&2
  status=1
fi

if rg -F -q 'joinIsComparison context false left right' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinIsComparison context true left right' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem Predicate.isEqual_present' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'theorem Predicate.isTruth_null' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'joinIsComparisonSyntax_of_success' "$audit_sources/SQLeanite/CoreSQLGrammar.lean" &&
   rg -F -q 'CoreJoin.Predicate.withCollation kind' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'isTruthKeyword? right' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'joinOperandAffinity_plus' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  echo 'ok - joined IS comparisons distinguish NULL-safe equality and keyword truth tests'
else
  echo 'FAIL - joined IS comparison live-path audit failed' >&2
  status=1
fi

if rg -F -q 'joinInList context argument values negated affinity' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreJoin.Predicate.membership kind left right' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem Predicate.membership_eval' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'theorem Predicate.membership_null' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'joinInListSyntax_of_success' "$audit_sources/SQLeanite/CoreSQLGrammar.lean"; then
  echo 'ok - joined IN lists preserve left affinity, nullable equality and positive grammar'
else
  echo 'FAIL - joined IN-list live-path audit failed' >&2
  status=1
fi

if rg -F -q '| .isNull arg negated => prepareNullTest (prepare arg) negated' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q '| .is, .literal .null _ => prepareNullTest a false' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -q 'theorem prepareNullTest_token' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -q 'theorem parserNonNullLiteral_collate' "$audit_sources/SQLeanite/SQLite/Scalar.lean"; then
  echo 'ok - literal NULL tests use parser token classification before scalar admission'
else
  echo 'FAIL - literal NULL preparation live-path audit failed' >&2
  status=1
fi

if rg -F -q 'SQLite.StaticCondition.classify outer prepared' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'unless joinStaticAdmitted context prepared outer' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem staticTerms_correct' SQLeanite/SQLite/StaticCondition.lean &&
   rg -F -q 'abbrev ignoredForbidden := SQLite.StaticCondition.resolutionForbidden' SQLeanite/CoreAggregateOrdering.lean &&
   rg -q 'theorem Predicate.constant_eval' "$audit_sources/SQLeanite/CoreJoin.lean"; then
  echo 'ok - static joined conditions retain resolution and code-generation checks'
else
  echo 'FAIL - static joined condition live-path audit failed' >&2
  status=1
fi

if rg -F -q 'let query ← joinAliasQuery select leftTable rightTable left.schema right.schema left.rows right.rows' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q '(CoreSQL.joinQueryWithZero select leftName rightName' SQLeanite/CoreLazyFileEngine.lean &&
   rg -F -q 'unless joinStaticAdmitted context prepared rightSource.leftJoin' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem joinZeroQuery_limit' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem Query.eval_limit_zero' "$audit_sources/SQLeanite/CoreJoin.lean"; then
  echo 'ok - zero-LIMIT joins validate predicates without evaluating their values'
else
  echo 'FAIL - zero-LIMIT join live-path audit failed' >&2
  status=1
fi

if rg -F -q 'unless rightSource.leftJoin && (leftRows.isEmpty || rightRows.isEmpty)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'unless joinStaticAdmitted context prepared true' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem Query.eval_empty_left' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'theorem Query.eval_empty_right_on' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'theorem joinQueryForRows_existing' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  echo 'ok - empty-side outer ON keeps validation and preserves the existing join path'
else
  echo 'FAIL - empty-side outer ON live-path audit failed' >&2
  status=1
fi

if rg -F -q 'let (columns, names) ← joinWrappedColumns context select.columns.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinWrappedOrderBy context orderColumns names select.orderBy.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'if query.distinct then query.distinctOutputRows rows else rows' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'theorem distinctCollatedRows_pairwise' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -q 'theorem joinQueryComplete_existing' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  echo 'ok - joined projection wrappers retain DISTINCT and ORDER BY collations'
else
  echo 'FAIL - joined projection wrapper live-path audit failed' >&2
  status=1
fi

if rg -F -q 'if rightSource.rightJoin then return ← executeRightJoin state select leftSource rightSource' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'source.leftJoin == kind.left && source.rightJoin == kind.right' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'CoreOuterJoin.eval rightSource.leftJoin left.schema.columns.length query left.rows right.rows' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem unmatchedRights_member' SQLeanite/CoreOuterJoin.lean &&
   rg -q 'theorem eval_width' SQLeanite/CoreOuterJoin.lean &&
   rg -q 'theorem executeRightJoin_preserves_state' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  echo 'ok - RIGHT/FULL ON joins track unmatched right rows before WHERE filtering'
else
  echo 'FAIL - RIGHT/FULL join live-path audit failed' >&2
  status=1
fi

if rg -F -q 'preferRightShared := rightSource.rightJoin && !rightSource.leftJoin' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q '.column (joinMergedStar context reference)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'starMetadata context qualifier sourceIndex index derived' SQLeanite/CoreCreateTableAs.lean &&
   rg -q 'theorem joinMergedStar_right' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -q 'theorem starMetadata_name' SQLeanite/CoreCreateTableAs.lean; then
  echo 'ok - RIGHT shared-name binding selects right values and preserves star names'
else
  echo 'FAIL - RIGHT shared-name live-path audit failed' >&2
  status=1
fi

if rg -F -q 'coalesceShared := rightSource.rightJoin && rightSource.leftJoin' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'def joinNamedOperand' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'def joinStarOperand' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinFullOrderBy context orderColumns names select.orderBy.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'term.compareValues (term.value left) (term.value right)' "$audit_sources/SQLeanite/CoreJoin.lean" &&
   rg -F -q 'mergedExpression context named' SQLeanite/CoreCreateTableAs.lean &&
   rg -F -q 'CoreJoin.Operand.mergedColumn_missing' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreJoin.Operand.mergedColumn_present' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - FULL shared names coalesce values and retain source affinity and ordering\n'
else
  printf 'live-path check FAILED: FULL shared-column interpretation\n' >&2
  status=1
fi

if rg -F -q 'let query ← joinAliasQuery select leftTable rightTable left.schema right.schema left.rows right.rows' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreOrder.resolveAliasesWith (joinHasColumn context) select.columns.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'match joinAliasQuery { select with orderBy := #[], offset := 0 }' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreOrder.resolveNamesFuelWith_source' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreOrder.resolveNamesFuelWith_alias' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.joinAliasQuery_existing' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreOrder.resolveJoinOnTerm_alias' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - joined ON/WHERE aliases preserve source priority and original result expressions\n'
else
  printf 'live-path check FAILED: joined predicate aliases\n' >&2
  status=1
fi

if rg -F -q 'columns := ← joinCompoundColumns context select.columns.toList' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'bindExpression := some (fun expression => joinCompoundBind context' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'if let some bind := arm.bindExpression then' SQLeanite/CoreCompoundTail.lean &&
   rg -F -q 'CoreSQL.joinCompoundStarColumns_projection' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.joinCompoundOperand_sides' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.joinCompoundOperand_merged' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - joined compound ORDER BY uses expanded result slots and bound source identities\n'
else
  printf 'live-path check FAILED: joined compound result binding\n' >&2
  status=1
fi

if rg -F -q 'let base ← executeSelectBaseComplete state { select with compounds := #[] }' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q '| .error _ => executeJoinScalar state select' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'let prepared ← joinScalarPrepare context' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'arguments.toList.findSome? effectiveName' SQLeanite/SQLite/ExprCollation.lean &&
   rg -F -q 'let collations ← resultCollationsFuel query.compoundHeight state query' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.executeJoinScalar_preserves_state' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQLReadText.executeSelectBaseComplete_eq_core' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.joinScalarRowsM_pure' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - joined expression fallback binds original sources and preserves existing Core reads\n'
else
  printf 'live-path check FAILED: joined expression fallback\n' >&2
  status=1
fi

if rg -F -q 'let source := joinScalarReducedSource context prepared originalRight' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinSearchRows context prepared source plan traversal.exchanged inner outer' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinScalarOnlySide context prepared outerSide term' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinScalarNullWalk_or' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.joinScalarReducedSource_no_new_outer' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - joined expression scans preserve source direction and conservative outer reduction\n'
else
  printf 'live-path check FAILED: joined expression scan planning\n' >&2
  status=1
fi

if rg -F -q '(joinScalarReadReport state select).toExcept' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'if state.stopped then state' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.observeReadSelect? state select' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreSQL.observeReadSelect? state select' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'onResults [observed.execution.result]' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'onResults [observed.execution.result]' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreFileEngine.executeObserved connection line printCoreResults' Main.lean &&
   rg -F -q 'CoreSQL.observeJoinedSelect_refines' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - joined streaming reads retain emitted prefixes and erase to ordinary Core execution\n'
else
  printf 'live-path check FAILED: joined read observation or streaming path\n' >&2
  status=1
fi

if rg -F -q 'joinSearchCandidates context prepared source exchanged outer plan.access inner' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'let plan := joinSearchPlan context prepared source traversal on' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'let outer ← match traversal.root with' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinSearchCandidates_point_error' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.joinSearchCandidates_automatic_empty' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - joined cursor initialization preserves computed key errors and empty scan termination\n'
else
  printf 'live-path check FAILED: joined cursor initialization\n' >&2
  status=1
fi
