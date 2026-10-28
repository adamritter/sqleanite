import SQLeanite.CanonicalSchemaSQL
import SQLeanite.Core
import SQLeanite.CoreChunkPageDelta
import SQLeanite.CoreChunkPageState
import SQLeanite.CoreDecode
import SQLeanite.CoreDecode.ValidateCanonicalIndexGroupsFromEncodeOverflowIndexTableGroups
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

#print axioms SQLeanite.CoreFileAdapter.IntegerIndexRouting.rangeEntries_exact

#print axioms SQLeanite.CoreDecode.AbstractIndexTree.equalityCandidates_exact

#print axioms SQLeanite.CoreDecode.AbstractIndexTree.IntegerOrdered.wellRouted

#print axioms SQLeanite.CoreDecode.decodeAbstractIndexTreeFrom_toList

#print axioms SQLeanite.CoreDecode.indexValueCandidatesFrom_decodeAbstract

#print axioms SQLeanite.CoreDecode.lookupIndexValueFrom_decodeAbstract_exact

#print axioms SQLeanite.CoreDecode.lookupIndexValueFrom_refines_full_decode

#print axioms SQLeanite.CoreDecode.lookupIndexValueFrom_all_matches

#print axioms SQLeanite.CoreDecode.indexValueCandidatesDecodedWith_eq_from

#print axioms SQLeanite.CoreDecode.lookupIndexValueDecodedWith_eq_from

#print axioms SQLeanite.CoreDecode.AbstractIndexTree.rangeCandidates_exact

#print axioms SQLeanite.CoreDecode.AbstractIndexTree.IntegerOrdered.rangeWellRouted

#print axioms SQLeanite.CoreDecode.indexRangeCandidatesFrom_decodeAbstract

#print axioms SQLeanite.CoreDecode.lookupIndexRangeFrom_decodeAbstract_exact

#print axioms SQLeanite.CoreDecode.lookupIndexRangeFrom_refines_full_decode

#print axioms SQLeanite.CoreDecode.lookupIndexValueFrom_certified_exact

#print axioms SQLeanite.CoreDecode.lookupIndexRangeFrom_certified_exact

#print axioms SQLeanite.CoreDecode.lookupIndexRangeFrom_all_matches

#print axioms SQLeanite.Core.executeUncertifiedQueryWithCandidates_eq_execute

#print axioms SQLeanite.CoreFileAdapter.takeExact_spec

#print axioms SQLeanite.Core.Value.orderKey_injective

#print axioms SQLeanite.Core.buildDeclaredKeyMap_get_of_hidden

#print axioms SQLeanite.Core.buildDeclaredKeyMap_represents

#print axioms SQLeanite.Core.Table.findDeclaredPrimary?_exact

#print axioms SQLeanite.Core.Table.nextGeneratedRowid?_greater

#print axioms SQLeanite.Core.Table.declaredKeyMap_insert_represents_orderedUpsert

#print axioms SQLeanite.Core.Table.declaredKeyMap_replace_represents_orderedUpsert

#print axioms SQLeanite.Core.declaredKeyMapAfterUpsert_represents

#print axioms SQLeanite.Core.Table.upsertGeneratedFresh_rows

#print axioms SQLeanite.CoreLocalizedRepresentation.TableIndexImageEq.ofDelta

#print axioms SQLeanite.CoreLocalizedRepresentation.updateState?_indexImagesAligned

#print axioms SQLeanite.CoreLocalizedRepresentation.DatabaseOnSource.updateStateApplyWritesBelow

#print axioms SQLeanite.CoreLocalizedRepresentation.DatabaseOnSource.updateStateApplyWritesBelowExtension

#print axioms SQLeanite.PersistentPageTree.Node.PathAgrees.pageIds_eq

#print axioms SQLeanite.PersistentPageTree.Node.PathAgrees.height_eq

#print axioms SQLeanite.PersistentPageTree.Store.insert_height_of_noAllocation

#print axioms SQLeanite.PersistentPageTree.Store.insert_pageIds_of_noAllocation

#print axioms SQLeanite.CoreChunkPageDelta.replaceManyFold_pageIds_of_noAllocation

#print axioms SQLeanite.CoreChunkPageDelta.replaceManyFold_height_of_noAllocation

#print axioms SQLeanite.CoreChunkPageDelta.replaceBetween?_pageIds_of_length_eq

#print axioms SQLeanite.CoreChunkPageDelta.replaceBetween?_height_of_length_eq

#print axioms SQLeanite.CoreChunkPageDelta.replaceBetween?_freedPageNumbers_of_length_eq

#print axioms SQLeanite.CoreChunkPageDelta.alignTables?_nextPage_none

#print axioms SQLeanite.CoreChunkPageDelta.alignTables?_selectedFreedPages_of_indexed

#print axioms SQLeanite.CoreChunkPageDelta.alignTables?_nextPage_changed_indexed

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_selectedPageIds_of_indexed

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_selectedHeight_eq_of_indexed

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_activePageIds_eq_of_indexed

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_freePages

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_nextPage_eq_of_indexed

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_freedPageNumbers_eq_nil_of_indexed

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_freePages_eq_of_indexed

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_allocationWellFormed_of_indexed

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_selected_mem

#print axioms SQLeanite.CoreChunkPageState.pageIds_disjoint_of_nodup

#print axioms SQLeanite.CoreDurability.OrdinaryLocalizedCommit.databaseOnSource

#print axioms SQLeanite.CoreDurability.OrdinaryLocalizedCommit.localizedRepresentation

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.ordinaryLocalizedCommit

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.ordinaryLocalizedCommitSingle

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.changedTableOnFinalWrites

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.changedTableOnFinalWritesIndexed

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.finalWrites_pageId_lt_of_indexed

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.baseWrites_pageId_pos_of_indexed

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.retainedTableOnFinalWritesIndexed

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.databaseOnFinalWritesIndexedSingle

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.databaseOnFinalWritesIndexedInline

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.localizedOnFinalWritesIndexedSingle

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.localizedOnFinalWritesIndexedInline

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.LocalizedLastIndexDelta.liveDeltaEquations

#print axioms SQLeanite.CoreFileAdapter.CommittedLocalizedDelta.trace_eq

#print axioms SQLeanite.CoreFileAdapter.CommittedLocalizedDelta.trace_eq_commitPlan

#print axioms SQLeanite.CoreFileAdapter.PreparedLocalizedWrites.base_mem

#print axioms SQLeanite.CoreFileAdapter.PreparedLocalizedWrites.sources

#print axioms SQLeanite.CoreFileAdapter.PreparedLocalizedWrites.added_disjoint_active

#print axioms SQLeanite.CoreFileAdapter.PreparedLocalizedWrites.added_disjoint_table_tree

#print axioms SQLeanite.CoreFileAdapter.PreparedLocalizedWrites.added_disjoint_encoded_table_tree

#print axioms SQLeanite.CoreFileAdapter.PreparedLocalizedWrites.added_pageZero_of_noFreePages

#print axioms SQLeanite.CoreFileAdapter.PreparedLocalizedWrites.pageZero_not_mem_of_stable

#print axioms SQLeanite.CoreChunkPageState.State.AllocationWellFormed.active_after_catalog

#print axioms SQLeanite.CoreChunkPageState.State.AllocationWellFormed.free_after_catalog

#print axioms SQLeanite.CoreChunkPageState.State.AllocationWellFormed.free_not_active

#print axioms SQLeanite.CoreDurability.PostImageCertificate.representsDatabase

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingle

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedInline

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedInlineOfRows

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedInlineOfInlineRows

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingleOfRowsInline

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingleOfInlineTree

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingleOfInlineRows

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_encodabilityPreserved

#print axioms SQLeanite.CoreDurability.postImageCertificate_of_preparedBulkImage

#print axioms SQLeanite.CoreDurability.CoreFileAdapter.PreparedBulkCommit.postImageCertificate

#print axioms SQLeanite.RecursiveBPlusTree.Node.last?_eq_getLast?

#print axioms SQLeanite.PersistentPageTree.Node.lookup_eq_erase

#print axioms SQLeanite.PersistentPageTree.Node.last?_eq_erase

#print axioms SQLeanite.Core.implicitPrimaryIndexes_areImplicit

#print axioms SQLeanite.Runtime.LowerBound.search_eq_findIdx

#print axioms SQLeanite.Runtime.CheckedOrder.monotone_of_checked

#print axioms SQLeanite.Runtime.TablePage.View.lowerBound_eq_linear

#print axioms SQLeanite.Runtime.TablePage.View.lowerBound_present

#print axioms SQLeanite.Runtime.Record.encodedSize_eq_length


#print axioms SQLeanite.SQLite.TextEncoding.fromStorage_utf8


#print axioms SQLeanite.SQLite.TextEncoding.toStorage_utf8


#print axioms SQLeanite.SQLite.TextEncoding.bind_utf8


#print axioms SQLeanite.CoreTextEncoding.fields_utf8


#print axioms SQLeanite.SQLite.Collation.forEncoding_utf8


#print axioms SQLeanite.CoreDecode.encodedIndexEntries_perm


#print axioms SQLeanite.CoreDecode.checkedEncodedIndex_utf8


#print axioms SQLeanite.CoreOrder.encodedSpecification_unencoded

#print axioms SQLeanite.Runtime.Record.decodeRowCell_eq_reference

#print axioms SQLeanite.Runtime.Record.readRowWithSource_eq_reference

#print axioms SQLeanite.SQLite.Numeric.fits_iff

#print axioms SQLeanite.SQLite.Numeric.integerPrefix_bounds

#print axioms SQLeanite.SQLite.Scalar.checkedInteger_exact

#print axioms SQLeanite.SQLite.Scalar.add_integer_exact

#print axioms SQLeanite.SQLite.Scalar.divide_integer_zero

#print axioms SQLeanite.SQLite.Scalar.arithmetic_null_left

#print axioms SQLeanite.SQLite.Scalar.arithmetic_null_right

#print axioms SQLeanite.SQLite.Scalar.shift_left_large

#print axioms SQLeanite.CoreSQL.executeConstantSelect_preserves_state

#print axioms SQLeanite.CoreSQL.executeConstantSelect_at_most_one_row

#print axioms SQLeanite.SQLite.FloatCodec.multiply128_reconstruct

#print axioms SQLeanite.SQLite.PhysicalAffinity.comparison_eq_self

#print axioms SQLeanite.SQLite.PhysicalAffinity.read_eq_self

#print axioms SQLeanite.SQLite.PhysicalAffinity.comparison_null

#print axioms SQLeanite.SQLite.PhysicalAffinity.write_null

#print axioms SQLeanite.Core.columnRead_eq_self

#print axioms SQLeanite.Core.columnComparison_eq_self

#print axioms SQLeanite.Core.readColumnValues_eq_self

#print axioms SQLeanite.CanonicalSchemaSQL.parseBaseColumn_typed_append

#print axioms SQLeanite.CanonicalSchemaSQL.parseColumn_any_append

#print axioms SQLeanite.CoreTokenGrammar.parseStatements_certified

#print axioms SQLeanite.SQLite.Text.slice_length_le

#print axioms SQLeanite.SQLite.Text.findSub_empty

#print axioms SQLeanite.SQLite.Text.substr_null

#print axioms SQLeanite.SQLite.Text.minmax_null

#print axioms SQLeanite.SQLite.Text.unhexCodes_empty

#print axioms SQLeanite.SQLite.Scalar.evalWith_column

#print axioms SQLeanite.SQLite.Scalar.evalWith_literal

#print axioms SQLeanite.CoreExpr.projectRow_width

#print axioms SQLeanite.CoreExpr.eval_column

#print axioms SQLeanite.Core.stableDeduplicate_nodup

#print axioms SQLeanite.Core.stableDeduplicate_map_injective

#print axioms SQLeanite.Core.Query.eval_distinct_limit

#print axioms SQLeanite.CoreReadSemantics.ofList_limitRows

#print axioms SQLeanite.CoreReadSemantics.ofList_stableDeduplicate

#print axioms SQLeanite.Core.mem_stableDistinctBy

#print axioms SQLeanite.Core.stableDistinctBy_subset

#print axioms SQLeanite.Core.stableDistinctBy_key_nodup

#print axioms SQLeanite.Core.stableDistinctBy_map

#print axioms SQLeanite.Core.Query.eval_distinct_key_nodup

#print axioms SQLeanite.CoreReadSemantics.ofList_stableDistinctBy

#print axioms SQLeanite.CoreReadSemantics.distinctRowKey_reorder

#print axioms SQLeanite.Core.stableDistinctBy_coverage

#print axioms SQLeanite.Core.mem_keys_stableDistinctBy

#print axioms SQLeanite.CoreCompound.combine_subset

#print axioms SQLeanite.CoreCompound.combine_keys_nodup

#print axioms SQLeanite.CoreSQL.combineRows_denotes

#print axioms SQLeanite.PhysicalQuery.compareValues_self

#print axioms SQLeanite.Core.chooseExtreme_tie

#print axioms SQLeanite.Core.extremeRepresentative_mem

#print axioms SQLeanite.Core.GroupQuery.representative_mem

#print axioms SQLeanite.Core.GroupQuery.representative_key

#print axioms SQLeanite.CoreExpr.scan_limit_zero

#print axioms SQLeanite.CoreExpr.scan_length_le

#print axioms SQLeanite.CoreSQL.executeFilteredSelect_preserves_state

#print axioms SQLeanite.CoreFileAdapter.indexTailMatches_exact

#print axioms SQLeanite.CoreSQL.rowUpdateCommands_length_le

#print axioms SQLeanite.CoreSQL.executeExpressionUpdate_eq_runCoreCommands

#print axioms SQLeanite.CoreSQL.executeExpressionDelete_eq_runCoreCommands

#print axioms SQLeanite.CoreSQL.rowDeleteCommands_length_le

#print axioms SQLeanite.SQLite.WALRead.decodeFrames_invalid

#print axioms SQLeanite.SQLite.WALRead.Replay.run_uncommitted

#print axioms SQLeanite.SQLite.WALRead.Snapshot.readPage_base

#print axioms SQLeanite.SQLite.WALRead.Snapshot.readPage_newest

#print axioms SQLeanite.SQLite.Scalar.evalInList_empty

#print axioms SQLeanite.CoreExpr.scanWindow_offset_zero

#print axioms SQLeanite.CoreExpr.scanWindow_limit_zero

#print axioms SQLeanite.SQLite.AggregateSum.State.step_null

#print axioms SQLeanite.SQLite.AggregateSum.accumulate_nulls

#print axioms SQLeanite.SQLite.AggregateSum.sum_nulls

#print axioms SQLeanite.SQLite.AggregateSum.average_nulls

#print axioms SQLeanite.CoreAggregate.countStar_exact

#print axioms SQLeanite.CoreAggregate.selectRows_length_le

#print axioms SQLeanite.CoreSQL.executeAggregateSelect_preserves_state

#print axioms SQLeanite.Core.Row.declaredKey_no_declared

#print axioms SQLeanite.Core.Row.create_set_rowid

#print axioms SQLeanite.AtomicFileReplacement.committed

#print axioms SQLeanite.AtomicFileReplacement.prefix_atomic

#print axioms SQLeanite.CoreSQL.rowRekeyBatch_changes_le

#print axioms SQLeanite.CoreSQL.executeRekeyUpdate_eq_runCoreCommands

#print axioms SQLeanite.SQLite.Scalar.roundPrecision_le

#print axioms SQLeanite.SQLite.Scalar.roundValue_null_left

#print axioms SQLeanite.SQLite.Scalar.roundValue_null_right

#print axioms SQLeanite.SQLite.Pattern.foldASCII_nonASCII

#print axioms SQLeanite.SQLite.Pattern.matches_empty

#print axioms SQLeanite.SQLite.Pattern.evaluate_null_input

#print axioms SQLeanite.Core.uniqueValueConflict_null_left

#print axioms SQLeanite.Core.uniqueValueConflict_null_right

#print axioms SQLeanite.Core.Table.insertValues_unique

#print axioms SQLeanite.CoreSQL.executeStatement_createTable_noop

#print axioms SQLeanite.CoreSQL.executeStatement_createIndex_noop

#print axioms SQLeanite.CoreAggregate.PreparedResults.accumulate_length

#print axioms SQLeanite.SQLite.Scalar.isTruth_null

#print axioms SQLeanite.SQLite.Scalar.bindBooleanKeywords_shadowed

#print axioms SQLeanite.SQLite.Text.fromBytes_invalid

#print axioms SQLeanite.CoreExpr.value_invalid_text

#print axioms SQLeanite.SQLite.CLI.listTextBytes_nul
