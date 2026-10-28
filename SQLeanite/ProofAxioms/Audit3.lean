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

#print axioms SQLeanite.Core.deduplicate_nodup

#print axioms SQLeanite.Core.Query.eval_nodup_of_distinct

#print axioms SQLeanite.Core.execute_query_exact

#print axioms SQLeanite.Core.execute_createTable_exact

#print axioms SQLeanite.Core.execute_createIndex_exact

#print axioms SQLeanite.Core.execute_insert_exact

#print axioms SQLeanite.Core.execute_replace_exact

#print axioms SQLeanite.Core.execute_deleteWhere_exact

#print axioms SQLeanite.Core.execute_updateWhere_exact

#print axioms SQLeanite.Core.execute_commit_exact

#print axioms SQLeanite.Core.countInteger_exact

#print axioms SQLeanite.Core.countRows_star

#print axioms SQLeanite.Core.execute_count_exact

#print axioms SQLeanite.Core.checkedInteger_exact

#print axioms SQLeanite.Core.addInteger_exact

#print axioms SQLeanite.Core.sumIntegerFrom_exact

#print axioms SQLeanite.Core.sumIntegers_exact

#print axioms SQLeanite.Core.execute_sum_exact

#print axioms SQLeanite.Core.chooseExtreme_eq_left_or_right

#print axioms SQLeanite.Core.extremeValues_mem_or_null

#print axioms SQLeanite.Core.execute_extreme_exact

#print axioms SQLeanite.Core.GroupQuery.groupKeys_nodup

#print axioms SQLeanite.Core.GroupQuery.mem_groupKeys_iff

#print axioms SQLeanite.Core.GroupQuery.eval_width

#print axioms SQLeanite.Core.execute_group_exact

#print axioms SQLeanite.Core.execute_join_exact

#print axioms SQLeanite.CoreJoin.Query.orderedRows_perm

#print axioms SQLeanite.CoreJoin.Query.eval_width

#print axioms SQLeanite.CoreJoin.mergeRowids_eq_spec

#print axioms SQLeanite.CoreJoin.rowidJoinSpec_filter_left_atMost

#print axioms SQLeanite.CoreJoin.mergeRowids_filter_left_atMost_eq_spec

#print axioms SQLeanite.CoreJoin.rowidJoinSpec_eq_matchingRows

#print axioms SQLeanite.CoreJoin.Query.evalPrimaryKeyCandidates_eq_eval

#print axioms SQLeanite.CoreJoin.Query.evalPrimaryKeyCandidates_empty_right_eq_eval

#print axioms SQLeanite.CoreJoin.Query.evalPlanned_eq_eval

#print axioms SQLeanite.CoreJoin.Predicate.eval_leftOnly

#print axioms SQLeanite.CoreJoin.matchingRows_pushLeft

#print axioms SQLeanite.CoreJoin.leftOuterRows_pushLeft

#print axioms SQLeanite.CoreJoin.leftOuterFor_nonempty

#print axioms SQLeanite.CoreJoin.leftOuterFor_eq_null_of_no_match

#print axioms SQLeanite.CoreJoin.leftOuterFor_eq_matches_of_some_match

#print axioms SQLeanite.CoreJoin.leftOuterFor_preserves_left

#print axioms SQLeanite.CoreSQL.runStatements_append

#print axioms SQLeanite.CoreSQL.mem_combineRows

#print axioms SQLeanite.CoreSQL.combineRows_nodup

#print axioms SQLeanite.CoreSQL.combineRows_width

#print axioms SQLeanite.CoreSQL.columnRef?_eq_some_iff

#print axioms SQLeanite.CoreSQL.literalSyntax_of_success

#print axioms SQLeanite.CoreSQL.predicateSyntax_of_success

#print axioms SQLeanite.CoreSQL.projectionSyntax_of_success

#print axioms SQLeanite.CoreSQL.orderingSyntax_of_success

#print axioms SQLeanite.CoreSQL.groupingSyntax_of_success

#print axioms SQLeanite.CoreSQL.groupOutputSyntax_of_success

#print axioms SQLeanite.CoreSQL.joinOperandSyntax_of_success

#print axioms SQLeanite.CoreSQL.joinPredicateSyntax_of_success

#print axioms SQLeanite.lex_sound

#print axioms SQLeanite.parse_success_tokenizes

#print axioms SQLeanite.CoreTokenGrammar.parseCertified_sound

#print axioms SQLeanite.CoreTokenGrammar.parseCertified_agrees_parse

#print axioms SQLeanite.CoreTokenGrammar.Parses.grammar

#print axioms SQLeanite.CoreTokenGrammar.Parses.agrees_parse

#print axioms SQLeanite.CoreSQL.statementForm_of_execute_success

#print axioms SQLeanite.CoreSQL.statementListForm_of_run_success

#print axioms SQLeanite.CoreSQL.ParsedSupportedText.tokenizes

#print axioms SQLeanite.CoreSQL.ParsedSupportedText.grammar

#print axioms SQLeanite.CoreSQL.execute_eq_runStatements_of_parsed

#print axioms SQLeanite.CoreSQL.parsedSupportedText_of_execute_success

#print axioms SQLeanite.CoreSQL.parsedSupportedText_execute_exact

#print axioms SQLeanite.RecursivePageBTree.IndexStore.build?_cells

#print axioms SQLeanite.RecursivePageBTree.IndexStore.retarget?_pageCount

#print axioms SQLeanite.RecursivePageBTree.IndexStore.retarget?_represents

#print axioms SQLeanite.RecursivePageBTree.IndexStore.insertAt?_pageCount

#print axioms SQLeanite.RecursivePageBTree.IndexStore.insertAt?_represents

#print axioms SQLeanite.CoreOptimizerBridge.compoundPlan_eval

#print axioms SQLeanite.CoreOptimizerBridge.optimize_compoundPlan_eval

#print axioms SQLeanite.CoreOptimizerBridge.optimizeCompoundOp_eq

#print axioms SQLeanite.CoreRecord.decodeRowValues_encode

#print axioms SQLeanite.CoreRecord.decodeRowCell_encode

#print axioms SQLeanite.CoreFile.replaceFirst_length

#print axioms SQLeanite.CoreFile.Image.fileBytes_length

#print axioms SQLeanite.CoreFreelist.Layout.pages_length

#print axioms SQLeanite.CoreFreelist.Layout.paddedImage_pageCount

#print axioms SQLeanite.CoreMultiFreelist.freelistPages_length

#print axioms SQLeanite.CoreMultiFreelist.nextTrunk_valid

#print axioms SQLeanite.CoreMultiFreelist.leafNumbers_valid

#print axioms SQLeanite.CoreMultiFreelist.Layout.pages_length

#print axioms SQLeanite.PhysicalCodec.widenSignedInteger_eight

#print axioms SQLeanite.CoreDecode.decodeOffsets_length

#print axioms SQLeanite.CoreDecode.pages_length

#print axioms SQLeanite.CoreFileAdapter.run_commitPlan

#print axioms SQLeanite.CoreFileAdapter.commit_crash_atomic

#print axioms SQLeanite.CoreDurability.imageBytes_storageImage

#print axioms SQLeanite.CoreDurability.decode_imageBytes_encodeBulk

#print axioms SQLeanite.CoreDurability.storageImage_encodeBulk_represents

#print axioms SQLeanite.CoreDurability.storageImage_padded_represents

#print axioms SQLeanite.CoreDurability.pageSourceRepresents_storageImage

#print axioms SQLeanite.CoreDurability.LocalizedRepresentation.representsDatabase

#print axioms SQLeanite.CoreDurability.sqliteHeaderMatches_of_pageZeroWrite

#print axioms SQLeanite.CoreDurability.catalogRead_of_pageZeroWrite

#print axioms SQLeanite.CoreDurability.localizedRepresentation_of_pageZeroWrite

#print axioms SQLeanite.CoreDurability.localizedRepresentation_of_components

#print axioms SQLeanite.CoreDurability.localizedRepresentation_of_certificates

#print axioms SQLeanite.CoreDurability.sqliteHeaderMatches_of_unchangedPageZero

#print axioms SQLeanite.CoreDurability.catalogRead_of_unchangedPageZero

#print axioms SQLeanite.CoreDurability.localizedRepresentation_of_unchangedPageZero

#print axioms SQLeanite.CoreDurability.indexesDecode_consLocalized

#print axioms SQLeanite.CoreDurability.localizedIndexReadable_of_onStorage

#print axioms SQLeanite.CoreDurability.localizedIndexReadable_of_encodedOnStorage

#print axioms SQLeanite.CoreDurability.localizedLastIndexDelta_cons

#print axioms SQLeanite.CoreDurability.rollbackWrites_represents_crash_atomic

#print axioms SQLeanite.CoreDurability.rollbackWrites_represents_returned_recovers_new

#print axioms SQLeanite.CoreDurability.rollbackWrites_represents_recovery_crash_trace_atomic

#print axioms SQLeanite.CoreEndToEnd.execute_write_exact

#print axioms SQLeanite.CoreEndToEnd.executeCommand_commit_crash_atomic

#print axioms SQLeanite.CoreEndToEnd.executeCommand_returned_recovers_new

#print axioms SQLeanite.CoreEndToEnd.executeCommand_recovery_crash_trace_atomic

#print axioms SQLeanite.CoreSQLWriteText.executeStatement_eq_core

#print axioms SQLeanite.CoreSQLWriteText.execute_eq_core

#print axioms SQLeanite.CoreSQLWriteText.executeText_commit_crash_atomic

#print axioms SQLeanite.CoreSQLWriteText.executeText_returned_recovers_new

#print axioms SQLeanite.CoreSQLWriteText.executeText_recovery_crash_trace_atomic

#print axioms SQLeanite.CoreSQL.insertRows_eq_runCoreCommands

#print axioms SQLeanite.CoreSQLWriteText.executeStatement_insertRows_eq_core

#print axioms SQLeanite.CoreSQLWriteText.executeWriteCommands_exact

#print axioms SQLeanite.CoreSQLWriteText.executeText_insertRows_commit_crash_atomic

#print axioms SQLeanite.CoreSQLWriteText.executeText_insertRows_returned_recovers_new

#print axioms SQLeanite.CoreSQLWriteText.executeText_insertRows_recovery_crash_trace_atomic

#print axioms SQLeanite.CoreSQLTraceText.execute_exact

#print axioms SQLeanite.CoreSQLTraceText.runStatements_eq_commands

#print axioms SQLeanite.CoreSQLTraceText.executeCommands_exact

#print axioms SQLeanite.CoreSQLTraceText.executeText_commit_crash_atomic

#print axioms SQLeanite.CoreSQLTraceText.executeText_localized_commit_crash_atomic

#print axioms SQLeanite.CoreSQLTraceText.executeText_committedLocalizedIndexedSingle_crash_atomic

#print axioms SQLeanite.CoreSQLTraceText.executeText_committedLocalizedIndexedSingleOfRowsInline_crash_atomic

#print axioms SQLeanite.CoreSQLTraceText.executeText_committedLocalizedIndexedInlineTables_crash_atomic

#print axioms SQLeanite.CoreSQLTraceText.executeText_committedLocalizedIndexedSingleOfInlineTree_crash_atomic

#print axioms SQLeanite.CoreSQLTraceText.executeText_committedLocalizedIndexedSingleOfInlineRows_crash_atomic

#print axioms SQLeanite.CoreSQLTraceText.executeText_committedLocalizedIndexedSingleYCSB_crash_atomic

#print axioms SQLeanite.CoreSQLTraceText.executeText_returned_recovers_new

#print axioms SQLeanite.CoreSQLTraceText.executeText_recovery_crash_trace_atomic

#print axioms SQLeanite.CoreSQLReadText.executeStatement_eq_core

#print axioms SQLeanite.CoreSQLReadText.execute_eq_core

#print axioms SQLeanite.CoreSQLReadText.executeSelectBase_eq_core

#print axioms SQLeanite.CoreSQLReadText.core_read_refines

#print axioms SQLeanite.CoreSQLReadText.executeStatement_binary_eq_core

#print axioms SQLeanite.CoreSQLReadText.executeText_binary_refines

#print axioms SQLeanite.CoreSQLReadText.executeSelectFuel_compound_refines

#print axioms SQLeanite.CoreSQLReadText.executeText_compound_refines

#print axioms SQLeanite.CoreSQLReadText.executeText_read_refines

#print axioms SQLeanite.CoreSQLReadText.executeText_count_refines

#print axioms SQLeanite.CoreSQLReadText.executeText_sum_refines

#print axioms SQLeanite.CoreSQLReadText.executeText_extreme_refines

#print axioms SQLeanite.CoreSQLReadText.executeText_group_refines

#print axioms SQLeanite.CoreSQLReadText.executeText_join_refines

#print axioms SQLeanite.CoreDurability.rollbackCommit_represents_crash_atomic

#print axioms SQLeanite.CoreDurability.rollbackCommit_padded_crash_atomic

#print axioms SQLeanite.CoreDurability.rollbackCommit_core_crash_atomic

#print axioms SQLeanite.CoreDurability.rollbackCommit_represents_returned_recovers_new

#print axioms SQLeanite.CoreDurability.rollbackCommit_padded_returned_recovers_new

#print axioms SQLeanite.CoreDurability.rollbackCommit_core_returned_recovers_new

#print axioms SQLeanite.CoreDurability.rollbackCommit_represents_repeated_recovery_atomic

#print axioms SQLeanite.CoreDurability.rollbackCommit_represents_recovery_crash_trace_atomic

#print axioms SQLeanite.CoreDurability.rollbackCommit_padded_recovery_crash_trace_atomic

#print axioms SQLeanite.CoreDurability.rollbackCommit_core_repeated_recovery_atomic

#print axioms SQLeanite.GrowableStorage.makeJournal_exactPreimages

#print axioms SQLeanite.GrowableStorage.recoverWithJournal_apply_recovery_subset

#print axioms SQLeanite.GrowableStorage.recoverWithJournal_after_recovery_trace

#print axioms SQLeanite.GrowableStorage.rollbackCommit_recovery_crash_trace_atomic

#print axioms SQLeanite.PhysicalJournalCodec.decodeChecked_makeJournal_exact

#print axioms SQLeanite.CoreFileAdapter.pageTransfers_toList

#print axioms SQLeanite.CoreFileAdapter.rowsForExpectedIndexEntries

#print axioms SQLeanite.CoreFileAdapter.rowsForExpectedValue_exact

#print axioms SQLeanite.CoreFileAdapter.rowsForExpectedRange_exact

#print axioms SQLeanite.CoreFileAdapter.CertifiedCandidates.result_exact

#print axioms SQLeanite.Core.Database.findTable?_eq_some_of_mem

#print axioms SQLeanite.Core.Database.table_eq_of_mem_of_name_eq

#print axioms SQLeanite.CoreFileAdapter.StoredIntegerIndex.retarget_value_exact

#print axioms SQLeanite.CoreFileAdapter.StoredIntegerIndex.retarget_range_exact

#print axioms SQLeanite.CoreFileEngine.requiresPersistence_write_in_transaction

#print axioms SQLeanite.CoreChunkPageDelta.splitInsert?_represents

#print axioms SQLeanite.CoreChunkPageDelta.splitInsert?_treePagesAccounted

#print axioms SQLeanite.CoreChunkPageDelta.splitInsert?_treePagesSelected

#print axioms SQLeanite.CoreChunkPageDelta.mergeDelete?_represents

#print axioms SQLeanite.CoreChunkPageDelta.mergeDelete?_treePagesAccounted

#print axioms SQLeanite.CoreChunkPageDelta.mergeDelete?_treePagesSelected

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_tablePagesSufficient

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_metadataAligned

#print axioms SQLeanite.CoreChunkPageDelta.replaceBetween?_rootId

#print axioms SQLeanite.CoreChunkPageDelta.replaceBetween?_catalogEntry

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_catalogEntries

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_identityWellFormed

#print axioms SQLeanite.CoreChunkPageDelta.updateStateCandidate?_endpoints

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_endpoints

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_treePagesAccounted

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_treePagesSelected

#print axioms SQLeanite.CoreChunkPageDelta.updateStateCandidate?_identityWellFormed

#print axioms SQLeanite.CoreChunkPageDelta.firstInserted_mem_after

#print axioms SQLeanite.CoreChunkPageDelta.firstDeleted_mem_before

#print axioms SQLeanite.CoreChunkPageDelta.writes_covers_pages

#print axioms SQLeanite.Core.indexedCandidates_filter_eq_scan
