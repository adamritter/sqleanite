import SQLeanite.CanonicalSchemaSQL
import SQLeanite.Core
import SQLeanite.CoreChunkPageDelta
import SQLeanite.CoreChunkPageState
import SQLeanite.CoreDecode
import SQLeanite.CoreDurability
import SQLeanite.CoreFile
import SQLeanite.CoreFileAdapter
import SQLeanite.CoreJoin
import SQLeanite.CoreLazyFileEngine
import SQLeanite.CoreLocalizedRepresentation
import SQLeanite.CoreOptimizerBridge
import SQLeanite.CorePageCodec
import SQLeanite.CorePageLoad
import SQLeanite.CoreReadSemantics
import SQLeanite.CoreSQL
import SQLeanite.CoreSQLGrammar
import SQLeanite.CoreSQLReadText
import SQLeanite.CoreSQLText
import SQLeanite.CoreSQLTraceText
import SQLeanite.CoreSQLWriteText
import SQLeanite.CoreWALFileEngine
import SQLeanite.CoreWidePageInverse
import SQLeanite.CoreWriteSemantics
import SQLeanite.GrowableStorage
import SQLeanite.PageCache
import SQLeanite.PageReuse
import SQLeanite.PersistentPageTree
import SQLeanite.PhysicalCodec
import SQLeanite.QueryCost
import SQLeanite.RecursiveBPlusTree
import SQLeanite.RecursivePageBTree
import SQLeanite.RelationalAlgebra
import SQLeanite.RuntimeRefinement
import SQLeanite.SQLite.CLI
import SQLeanite.SerializedConnection
import SQLeanite.TornStorage
import SQLeanite.WidePageTree

#print axioms SQLeanite.SQLite.CLI.listTextBytes_length_le

#print axioms SQLeanite.SQLite.Scalar.bindNames_quoted

#print axioms SQLeanite.CoreSQL.selectNamesBound_compounds

#print axioms SQLeanite.CoreOrder.scan_limit_zero

#print axioms SQLeanite.CoreOrder.insertStable_length

#print axioms SQLeanite.SQLite.Collation.compareText_self

#print axioms SQLeanite.SQLite.Collation.noCase_nul

#print axioms SQLeanite.SQLite.Collation.rtrimBytes_space

#print axioms SQLeanite.SQLite.Scalar.hasFunction_collate

#print axioms SQLeanite.SQLite.Limits.check_success

#print axioms SQLeanite.SQLite.Limits.check_excess

#print axioms SQLeanite.SingletonPageTree.pack_entries

#print axioms SQLeanite.SingletonPageTree.build_entries

#print axioms SQLeanite.SingletonPageTree.store_represents

#print axioms SQLeanite.CoreChunkPageState.buildChunkTree_represents

#print axioms SQLeanite.SQLite.WALIndex.Header.prefix_size

#print axioms SQLeanite.SQLite.WALIndex.Header.encode_size

#print axioms SQLeanite.SQLite.WALIndex.append_empty

#print axioms SQLeanite.SQLite.WALAppend.Frame.encode_size

#print axioms SQLeanite.SQLite.WALAppend.prepare_empty

#print axioms SQLeanite.SQLite.Scalar.forbidden_tooManyArguments

#print axioms SQLeanite.SQLite.ExprCollation.name_collate

#print axioms SQLeanite.SQLite.ExprCollation.compare_text_self

#print axioms SQLeanite.CoreCollatedGroup.keys_subset

#print axioms SQLeanite.CoreCollatedGroup.members_subset

#print axioms SQLeanite.CoreCollatedGroup.representative_mem

#print axioms SQLeanite.CoreCollatedGroup.emit_width

#print axioms SQLeanite.CoreSQL.executeCollatedGroup_preserves_state

#print axioms SQLeanite.CoreCollatedGroup.evalWindow_limit_zero

#print axioms SQLeanite.SQLite.Scalar.bindNamesFuel_preserves_collation

#print axioms SQLeanite.CoreCompound.representativesCollated_subset

#print axioms SQLeanite.CoreCompound.combineCollated_binary

#print axioms SQLeanite.CoreCompound.combineCollated_unionAll

#print axioms SQLeanite.CoreCompound.combineCollated_subset

#print axioms SQLeanite.CoreSQLReadText.translatedRead_noCollation

#print axioms SQLeanite.CoreSQLReadText.translatedCompound_resultCollation_false

#print axioms SQLeanite.CoreSQLReadText.translatedRead_noDeclaredCollation

#print axioms SQLeanite.CoreSQLReadText.translatedCompound_declaredResultCollation_false

#print axioms SQLeanite.CoreCompoundTail.window_zero

#print axioms SQLeanite.CoreCompoundTail.window_subset

#print axioms SQLeanite.CoreCompoundTail.sort_perm

#print axioms SQLeanite.CoreCompoundTail.adjacentDistinct_subset

#print axioms SQLeanite.CoreCompoundTail.mergeFuel_subset

#print axioms SQLeanite.CoreCompoundTail.merge_subset

#print axioms SQLeanite.CoreSQL.executeCompoundTail_preserves_state

#print axioms SQLeanite.SQLite.Scalar.evalWith_literal_spelling

#print axioms SQLeanite.CoreCompoundTail.sameFuel_real_spelling

#print axioms SQLeanite.SQLite.NumericLiteral.signedHex_bounds

#print axioms SQLeanite.SQLite.NumericLiteral.signedHex_low

#print axioms SQLeanite.SQLite.NumericLiteral.signedHex_high

#print axioms SQLeanite.SQLite.NumericLiteral.digitSeparators_trailing

#print axioms SQLeanite.SQLite.Scalar.forbidden_negated_minimum_hex

#print axioms SQLeanite.SQLite.Scalar.negatedLiteral_decimal_minimum

#print axioms SQLeanite.CoreAggregateOrder.extend_preserves_expressions

#print axioms SQLeanite.CoreAggregateOrder.eraseBareFuel_aggregate

#print axioms SQLeanite.CoreAggregateHaving.retain_member

#print axioms SQLeanite.CoreAggregateHaving.Prepared.matches_none

#print axioms SQLeanite.CoreGrouped.insertRow_nil

#print axioms SQLeanite.CoreGrouped.emitOrdered_limit_zero

#print axioms SQLeanite.CoreOrder.resolveAliases_literal

#print axioms SQLeanite.CoreMultiFreelist.Layout.applicationId_preserved

#print axioms SQLeanite.CoreMultiFreelist.Layout.userVersion_preserved

#print axioms SQLeanite.SQLite.AggregateConcat.State.step_null

#print axioms SQLeanite.SQLite.AggregateConcat.State.first_separator_ignored

#print axioms SQLeanite.SQLite.AggregateConcat.run_nil

#print axioms SQLeanite.SQLite.UnicodeEscape.unistr_null

#print axioms SQLeanite.SQLite.UnicodeEscape.decodeFuel_source_nul

#print axioms SQLeanite.SQLite.UnicodeEscape.quote_blob

#print axioms SQLeanite.SQLite.Probability.input_likely

#print axioms SQLeanite.SQLite.Probability.probability_integer

#print axioms SQLeanite.CoreAggregate.Term.filteredRows_none

#print axioms SQLeanite.SQLite.ExprCollation.callArguments_map

#print axioms SQLeanite.AggregateOrder.decode_encode

#print axioms SQLeanite.CoreAggregateOrdering.sameOrdering_nil

#print axioms SQLeanite.SQLite.FunctionSignatures.matchesArity_exact

#print axioms SQLeanite.SQLite.Math.numeric_integer

#print axioms SQLeanite.SQLite.Math.rounding_integer

#print axioms SQLeanite.SQLite.Math.unary_null

#print axioms SQLeanite.SQLite.Format.evaluate_no_arguments

#print axioms SQLeanite.SQLite.Format.evaluate_null

#print axioms SQLeanite.SQLite.Format.field_count_ignored

#print axioms SQLeanite.CoreDecode.catalogFields_nil

#print axioms SQLeanite.CoreDecode.catalogWalk_empty

#print axioms SQLeanite.CoreDecode.catalogWalk_exhausted

#print axioms SQLeanite.SQLite.DatabaseSize.pageCount_zero

#print axioms SQLeanite.SQLite.DatabaseSize.pageCount_stale

#print axioms SQLeanite.SQLite.DatabaseSize.pageCount_current

#print axioms SQLeanite.CoreFileAdapter.headerUsablePageSize?_partition

#print axioms SQLeanite.SQLite.HeaderVersion.unknown_read

#print axioms SQLeanite.SQLite.HeaderVersion.unknown_write

#print axioms SQLeanite.SQLite.HeaderVersion.schema_low_byte

#print axioms SQLeanite.CoreSchemaDrop.table_exact

#print axioms SQLeanite.CoreSchemaDrop.table_member

#print axioms SQLeanite.CoreSchemaDrop.index_exact

#print axioms SQLeanite.CoreSQL.executeStatement_dropTable_noop

#print axioms SQLeanite.CoreSQL.executeStatement_dropIndex_noop

#print axioms SQLeanite.CoreSQL.insertSelection_empty

#print axioms SQLeanite.CoreSQL.checkInsertSelectColumns_all

#print axioms SQLeanite.CoreSQL.executeValues_preserves_state

#print axioms SQLeanite.SQLite.Values.directCount_le_length

#print axioms SQLeanite.CoreReturning.deletionOutput_length

#print axioms SQLeanite.CoreInsertIgnore.shouldInsert_no_conflict

#print axioms SQLeanite.CoreSQL.executeIgnoredInsert_skips

#print axioms SQLeanite.CoreUpdateIgnore.finish_skips

#print axioms SQLeanite.CoreUpdateIgnore.finish_inserts

#print axioms SQLeanite.CoreUpdateScan.byColumn_perm

#print axioms SQLeanite.SQLite.PlannerCost.add_comm

#print axioms SQLeanite.CoreUpdateReplace.plan_validated

#print axioms SQLeanite.CoreUpdateReplace.pending_length

#print axioms SQLeanite.CoreSQL.replacedUpdateRows_missing

#print axioms SQLeanite.CoreSQL.insertReturningRow_ignored

#print axioms SQLeanite.CoreSQL.insertReturningRows_length_le

#print axioms SQLeanite.CoreReturning.updatedOutput_zero

#print axioms SQLeanite.CoreSQL.updateReturningRow_missing

#print axioms SQLeanite.CoreSQL.updateReturningRows_length_le

#print axioms SQLeanite.SQLite.RowAssignment.bind_exact

#print axioms SQLeanite.SQLite.RowAssignment.bind_length

#print axioms SQLeanite.Core.Row.declaredKey_null

#print axioms SQLeanite.Core.Row.declaredKey_null_injective

#print axioms SQLeanite.Core.Row.declaredKey_nonnull

#print axioms SQLeanite.CoreDecode.ascendingCellPointers_leafPointers

#print axioms SQLeanite.CoreDecode.ascendingCellPointers_next

#print axioms SQLeanite.CoreSQL.markPrimaryColumn_size

#print axioms SQLeanite.CoreSQL.markPrimaryColumn_names

#print axioms SQLeanite.CoreSQL.tablePrimaryColumns_empty

#print axioms SQLeanite.CoreSQL.insertValueIndex_rowid

#print axioms SQLeanite.CoreSQL.insertValueIndex_ordinary

#print axioms SQLeanite.CoreSQL.evaluateInsertExpressions_evaluated

#print axioms SQLeanite.CoreSQL.inputRowValues_single

#print axioms SQLeanite.CanonicalSchemaSQL.parseBaseColumn_integerNotNull_append

#print axioms SQLeanite.CoreNames.table?_folded

#print axioms SQLeanite.CoreNames.tableName_resolves

#print axioms SQLeanite.CoreNames.indexName_found

#print axioms SQLeanite.CoreSchemaRename.columns_length

#print axioms SQLeanite.CoreSchemaRename.column_exact

#print axioms SQLeanite.CoreSchemaRename.table_exact

#print axioms SQLeanite.CoreSchemaRename.replace_exact

#print axioms SQLeanite.Core.Index.wellFormed_rename

#print axioms SQLeanite.CoreSchemaAdd.insertAt_length

#print axioms SQLeanite.CoreSchemaAdd.row_rowid

#print axioms SQLeanite.CoreSchemaAdd.table_exact

#print axioms SQLeanite.CoreRecord.completeFields_full

#print axioms SQLeanite.CoreRecord.completeFields_record

#print axioms SQLeanite.CoreSchemaDropColumn.removeAt_length

#print axioms SQLeanite.CoreSchemaDropColumn.row_rowid

#print axioms SQLeanite.CoreSchemaDropColumn.table_allowed

#print axioms SQLeanite.CoreSchemaDropColumn.table_exact

#print axioms SQLeanite.CoreSchemaSQL.firstTail_semicolon

#print axioms SQLeanite.CoreDecode.readIndexEntry_rowid

#print axioms SQLeanite.CoreDecode.readIndexEntry_accepted

#print axioms SQLeanite.CoreDecode.checkedIndex_contents

#print axioms SQLeanite.CoreSchemaPragma.tableRows_length

#print axioms SQLeanite.CoreSchemaPragma.indexRows_length

#print axioms SQLeanite.CoreSchemaPragma.execute_preserves_state

#print axioms SQLeanite.SQLite.PragmaSyntax.numeric_integer_spelling

#print axioms SQLeanite.CoreSchemaPragma.scopedRows_temp

#print axioms SQLeanite.CoreCreateTableAs.uniqueName_unoccupied

#print axioms SQLeanite.CoreSQL.executeCreateTableAs_trace

#print axioms SQLeanite.Core.Column.restoreNotNullConflict

#print axioms SQLeanite.CoreNullConflict.insert_skips

#print axioms SQLeanite.CoreNullConflict.update_skips

#print axioms SQLeanite.CanonicalSchemaSQL.primaryFromBase_inverse

#print axioms SQLeanite.CoreDefaultConflict.commands_last

#print axioms SQLeanite.CoreDefaultConflict.plan_skips_null

#print axioms SQLeanite.CoreSQL.executeSchemaRow_skips

#print axioms SQLeanite.ColumnDefault.fromSource_spec

#print axioms SQLeanite.Core.Column.defaultForInsert_rowid

#print axioms SQLeanite.CanonicalSchemaSQL.takeQuotedNat_quote

#print axioms SQLeanite.CanonicalSchemaSQL.parseKeyColumn_any_append

#print axioms SQLeanite.ColumnDefault.emitted_boolean

#print axioms SQLeanite.Core.Column.typed_empty_affinity

#print axioms SQLeanite.SQLite.PrimaryKey.canonical_compare

#print axioms SQLeanite.Core.Row.declaredKey_null_ne_nonnull

#print axioms SQLeanite.CanonicalSchemaSQL.fromIndexed_inverse

#print axioms SQLeanite.CanonicalSchemaSQL.parseIndexedBody_append

#print axioms SQLeanite.CoreAutoIncrement.allocate_greater_maximum

#print axioms SQLeanite.CoreAutoIncrement.advance_monotone

#print axioms SQLeanite.CoreAutoIncrement.finish_unchanged

#print axioms SQLeanite.CanonicalSchemaSQL.fromAuto_inverse

#print axioms SQLeanite.CanonicalSchemaSQL.parseAutoBody_append

#print axioms SQLeanite.CoreSavepoint.push_transaction

#print axioms SQLeanite.CoreSavepoint.release_push

#print axioms SQLeanite.CoreSavepoint.rollbackTo_push

#print axioms SQLeanite.CoreSavepoint.release_database

#print axioms SQLeanite.CoreSavepoint.rollbackTo_snapshot

#print axioms SQLeanite.CoreSavepoint.releasesTransaction_push

#print axioms SQLeanite.CoreFileEngine.transactionChanged_equivalent

#print axioms SQLeanite.CoreFileEngine.requiresPersistence_commit_unchanged

#print axioms SQLeanite.CoreFileEngine.requiresPersistence_release_unchanged

#print axioms SQLeanite.SQLite.Script.step_contents

#print axioms SQLeanite.SQLite.Script.split_preserves_source

#print axioms SQLeanite.SQLite.Script.semicolon_in_group

#print axioms SQLeanite.SQLite.Identifier.aliasToken_name

#print axioms SQLeanite.SQLite.Identifier.aliasToken_join

#print axioms SQLeanite.SQLite.Identifier.aliasToken_quoted

#print axioms SQLeanite.SQLite.Identifier.windowNameToken_quoted

#print axioms SQLeanite.SQLite.Identifier.primaryToken_quoted

#print axioms SQLeanite.SQLite.Identifier.primaryToken_string

#print axioms SQLeanite.SQLite.CastType.check_valid

#print axioms SQLeanite.SQLite.CastType.check_name
