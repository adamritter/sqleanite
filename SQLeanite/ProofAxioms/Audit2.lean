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

#print axioms SQLeanite.CoreWidePageInverse.decode_encodeBulkInline

#print axioms SQLeanite.CoreWideIndex.NodeDecodes.ofCells

#print axioms SQLeanite.CoreWideIndex.decodeIndexSubtreeFrom_encodePages

#print axioms SQLeanite.CoreWideIndex.IndexEncoding.decode_exact

#print axioms SQLeanite.CoreWideIndex.applyIndexesForOpen_encoded

#print axioms SQLeanite.CorePageCodec.decodeCanonicalRows_encodeLeaf

#print axioms SQLeanite.CorePageCodec.encodeChunkNode_eq_mapM

#print axioms SQLeanite.CorePageCodec.changedPhysicalChunkPagesFast_eq

#print axioms SQLeanite.CorePageCodec.encodeChangedChunkPages_subset

#print axioms SQLeanite.CorePageCodec.physicalChunkPages_accounted_of_pathAgrees

#print axioms SQLeanite.CorePageCodec.encodeChunkPath_accounts_of_pathAgrees

#print axioms SQLeanite.CorePageCodec.encodeChangedChunkPages_accounts

#print axioms SQLeanite.CorePageCodec.encodeChunkPath_subset_encodeChunkNode

#print axioms SQLeanite.CoreDecode.decodeRowCellFrom_encodeCell

#print axioms SQLeanite.CorePageCodec.interiorChildren_interiorPage_one

#print axioms SQLeanite.CorePageCodec.interiorChildren_interiorPage_two

#print axioms SQLeanite.CoreDecode.decodeRowsFrom_resolvedLeaf

#print axioms SQLeanite.CorePageCodec.decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow

#print axioms SQLeanite.CorePageCodec.encodeChunkNode_pageNumbers

#print axioms SQLeanite.CorePageCodec.encodeChunkTables_pageNumbers

#print axioms SQLeanite.CorePageCodec.encodeChunkNodeWithOverflow_pageNumbers

#print axioms SQLeanite.CorePageCodec.encodeChunkNodeWithOverflow_nextPage

#print axioms SQLeanite.CorePageCodec.encodeChunkTablesWithOverflow_pageNumbers

#print axioms SQLeanite.CorePageCodec.encodeChunkTablesWithOverflow_nextPage

#print axioms SQLeanite.CoreChunkPageState.flatten_chunks

#print axioms SQLeanite.CoreChunkPageState.entries?_sorted

#print axioms SQLeanite.CoreChunkPageState.buildTree_rows

#print axioms SQLeanite.CoreChunkPageState.State.build?_represents

#print axioms SQLeanite.CoreChunkPageState.State.build?_allocationWellFormed

#print axioms SQLeanite.CoreChunkPageDelta.replace?_represents

#print axioms SQLeanite.CoreChunkPageDelta.replace?_treePagesAccounted

#print axioms SQLeanite.CoreChunkPageDelta.replace?_treePagesSelected

#print axioms SQLeanite.CoreChunkPageDelta.replaceMany?_represents

#print axioms SQLeanite.CoreChunkPageDelta.replaceMany?_treePagesAccounted

#print axioms SQLeanite.CoreChunkPageDelta.replaceMany?_treePagesSelected

#print axioms SQLeanite.CoreChunkPageDelta.insert?_represents

#print axioms SQLeanite.CoreChunkPageDelta.insert?_treePagesAccounted

#print axioms SQLeanite.CoreChunkPageDelta.insert?_treePagesSelected

#print axioms SQLeanite.CoreChunkPageDelta.delete?_represents

#print axioms SQLeanite.CoreChunkPageDelta.delete?_treePagesAccounted

#print axioms SQLeanite.CoreChunkPageDelta.delete?_treePagesSelected

#print axioms SQLeanite.CoreChunkPageDelta.retainMany?_represents

#print axioms SQLeanite.CoreChunkPageDelta.retainMany?_treePagesAccounted

#print axioms SQLeanite.CoreChunkPageDelta.retainMany?_treePagesSelected

#print axioms SQLeanite.CoreChunkPageDelta.replaceBetween?_treePagesAccounted

#print axioms SQLeanite.CoreChunkPageDelta.replaceBetween?_treePagesSelected

#print axioms SQLeanite.CoreChunkPageDelta.replaceBetween?_sameData

#print axioms SQLeanite.CoreChunkPageDelta.expectedIndexEntries_eq_sortSource

#print axioms SQLeanite.CoreChunkPageDelta.TableDelta.tablePagesSufficient_indexImage

#print axioms SQLeanite.CorePageLoad.load?_represents

#print axioms SQLeanite.CoreFileAdapter.preparedCommitPlan_eq_persistentCommitPlan

#print axioms SQLeanite.POSIXVFS.run_persistentCommitPlan

#print axioms SQLeanite.SyscallVFS.completedPersistentCommit_refines

#print axioms SQLeanite.Core.Row.treeKey_lt_iff

#print axioms SQLeanite.Core.Table.findRowid?_some_eq

#print axioms SQLeanite.Core.Table.findRowid?_eq_some_iff

#print axioms SQLeanite.Core.orderedInsert_treeEntries

#print axioms SQLeanite.Core.Table.insertValues_exact

#print axioms SQLeanite.Core.Table.replaceValues_rows

#print axioms SQLeanite.Core.Table.retainRows_exact

#print axioms SQLeanite.Core.Table.patchRows_exact

#print axioms SQLeanite.Core.Table.withIndexes_exact

#print axioms SQLeanite.RecursivePageBTree.build_toCells

#print axioms SQLeanite.RecursivePageBTree.build_balanced

#print axioms SQLeanite.RecursivePageBTree.Plan.withCells?_pageCount

#print axioms SQLeanite.RecursivePageBTree.Plan.withCells?_toCells

#print axioms SQLeanite.RecursivePageBTree.Plan.references_bounded

#print axioms SQLeanite.RecursivePageBTree.Plan.encodePagesFrom_length

#print axioms SQLeanite.RecursivePageBTree.encodeSingleTable_pageCount

#print axioms SQLeanite.RecursivePageBTree.encodeTable_refines

#print axioms SQLeanite.RecursivePageBTree.encodeTable_pages_length

#print axioms SQLeanite.RecursivePageBTree.encodeTables_tables

#print axioms SQLeanite.RecursivePageBTree.encode_tables_aligned

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.popMax_toCells

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.ofPlan_toCells

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.withCells?_pageCount

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.withCells?_toCells

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.insertAt?_toCells

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.insertAt?_pageCount

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.insertAt?_balanced

#print axioms SQLeanite.RecursivePageBTree.buildIndex_toCells

#print axioms SQLeanite.RecursivePageBTree.buildIndex_balanced

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.references_bounded

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.encodePagesFrom_length

#print axioms SQLeanite.RecursivePageBTree.encodeIndex_refines

#print axioms SQLeanite.RecursivePageBTree.encodeIndex_pages_length

#print axioms SQLeanite.GrowableStorage.recover_makeJournal_apply_subset

#print axioms SQLeanite.GrowableStorage.rollbackCommit_crash_atomic

#print axioms SQLeanite.GrowableStorage.applyWrites_pageCount_eq_of_forall_lt

#print axioms SQLeanite.GrowableStorage.rollbackCommit_committed_recovers_new

#print axioms SQLeanite.GrowableStorage.crash_can_roll_back_growth

#print axioms SQLeanite.PhysicalCodec.decodeValueField_recordField

#print axioms SQLeanite.PhysicalCodec.decodeRowCell_encode

#print axioms SQLeanite.PhysicalCodec.decodeCells_encode

#print axioms SQLeanite.PhysicalCodec.decodeDataPage_encode

#print axioms SQLeanite.PhysicalCodec.decodeImage_encode

#print axioms SQLeanite.PhysicalCodec.decodeFile_encode

#print axioms SQLeanite.PhysicalCodec.apply_transactionWrites_equiv

#print axioms SQLeanite.PhysicalCodec.rollbackCommit_database_crash_atomic

#print axioms SQLeanite.PhysicalCodec.rollbackCommit_database_committed_recovers_new

#print axioms SQLeanite.PhysicalCodec.Database.appendChecked_rows

#print axioms SQLeanite.PhysicalCodec.orderedUpsert_sorted

#print axioms SQLeanite.PhysicalCodec.Row.treeKey_lt_iff

#print axioms SQLeanite.PhysicalCodec.Database.tree_insert_rows

#print axioms SQLeanite.PhysicalCodec.Database.tree_delete_rows

#print axioms SQLeanite.PhysicalCodec.Database.upsertChecked_rows

#print axioms SQLeanite.PhysicalCodec.Database.insertChecked_rows

#print axioms SQLeanite.PhysicalCodec.Database.insertMany_rows

#print axioms SQLeanite.PhysicalCodec.Database.upsertMany_rows

#print axioms SQLeanite.PhysicalCodec.Database.deleteRowid_rows

#print axioms SQLeanite.PhysicalCodec.Database.updatePayload_rows

#print axioms SQLeanite.PhysicalCodec.Database.patchPayload_rows

#print axioms SQLeanite.PhysicalCodec.Database.patchSelected_rows

#print axioms SQLeanite.PhysicalCodec.Database.retainRows_rows

#print axioms SQLeanite.PhysicalCodec.Database.lookupRowid_eq_filter

#print axioms SQLeanite.PhysicalQuery.mem_matchingRows_iff

#print axioms SQLeanite.PhysicalQuery.matchingRows_id_equal

#print axioms SQLeanite.PhysicalQuery.Query.orderedRows_perm

#print axioms SQLeanite.PhysicalQuery.Query.eval_width

#print axioms SQLeanite.PhysicalQuery.Query.selectedRows_length_le_limit

#print axioms SQLeanite.PhysicalQuery.Query.evalDatabase_eq_eval

#print axioms SQLeanite.Serialization.runSchedule_completionIds

#print axioms SQLeanite.Serialization.runSchedule_append

#print axioms SQLeanite.Serialization.sequential_satisfies_contract

#print axioms SQLeanite.WALConcurrency.WAL.pending_is_invisible

#print axioms SQLeanite.WALConcurrency.WAL.commit_publishes

#print axioms SQLeanite.WALConcurrency.WAL.checkpoint_preserves_visible

#print axioms SQLeanite.WALConcurrency.WriterProtocolState.step_preserves_safe

#print axioms SQLeanite.WALConcurrency.runWriterProtocol_preserves_safe

#print axioms SQLeanite.WALConcurrency.writerProtocol_completes

#print axioms SQLeanite.WALConcurrency.accepted_schedules_are_serializable

#print axioms SQLeanite.WALConcurrency.some_nontrivial_interleaving_is_accepted

#print axioms SQLeanite.WALConcurrency.lost_update_schedule_is_rejected

#print axioms SQLeanite.WALConcurrency.Multi.build_readers_perm

#print axioms SQLeanite.WALConcurrency.Multi.serialObserved_build

#print axioms SQLeanite.WALConcurrency.Multi.accepted_schedules_are_serializable

#print axioms SQLeanite.WALConcurrency.Multi.two_nonoverlapping_writers_are_accepted

#print axioms SQLeanite.WALConcurrency.Multi.overlapping_writers_are_rejected

#print axioms SQLeanite.GroupCommit.WAL.commitGroup_eq_commitSequential

#print axioms SQLeanite.GroupCommit.WAL.commitGroup_visible_eq_newest

#print axioms SQLeanite.GroupCommit.WAL.sync_absorbPending_visible

#print axioms SQLeanite.GroupCommit.syncCount_groupProtocol

#print axioms SQLeanite.PageCache.ReadCache.read_refines

#print axioms SQLeanite.PageCache.ReadCache.insert_coherent

#print axioms SQLeanite.PageCache.WriteBuffer.read_put_same

#print axioms SQLeanite.PageReuse.takeReusable_sound

#print axioms SQLeanite.PageReuse.takeReusable_pending_none

#print axioms SQLeanite.PageReuse.active_reader_blocks_reuse

#print axioms SQLeanite.PhysicalTableBTree.Tree.toList_eq

#print axioms SQLeanite.PhysicalMultiPageCodec.decodeFile_fileBytes

#print axioms SQLeanite.PhysicalFreelist.Layout.pages_length

#print axioms SQLeanite.PhysicalFreelist.Layout.fileBytes_length

#print axioms SQLeanite.GrowableStorage.apply_replaceWrites_equiv

#print axioms SQLeanite.GrowableStorage.apply_deltaWrites_equiv

#print axioms SQLeanite.GrowableStorage.changedWritesGo_eq

#print axioms SQLeanite.GrowableStorage.changedWrites_eq_changedWritesTR

#print axioms SQLeanite.GrowableStorage.recoverWithJournal_idempotent

#print axioms SQLeanite.GrowableStorage.rollbackCommit_repeated_recovery_crash_atomic

#print axioms SQLeanite.POSIXVFS.run_commitPlan

#print axioms SQLeanite.POSIXVFS.Execution.commit_refines

#print axioms SQLeanite.SyscallVFS.completedCommit_refines

#print axioms SQLeanite.PhysicalMultiPageCodec.rollbackCommit_database_crash_atomic

#print axioms SQLeanite.PhysicalJournalCodec.decode_encode

#print axioms SQLeanite.PhysicalJournalCodec.decodeChecked_encode

#print axioms SQLeanite.PhysicalJournalCodec.encodeCheckedBytes_toList

#print axioms SQLeanite.PhysicalJournalCodec.decodeChecked_encodeBytes

#print axioms SQLeanite.PhysicalJournalCodec.decodePersistent_inactive

#print axioms SQLeanite.PhysicalJournalCodec.decodePersistent_initialInactive

#print axioms SQLeanite.PhysicalJournalCodec.decodePersistent_encode

#print axioms SQLeanite.PhysicalJournalCodec.decodePersistent_encodeBytes

#print axioms SQLeanite.PhysicalJournalCodec.decodeChecked_accepts_only_matching

#print axioms SQLeanite.PhysicalJournalRecovery.decodeImage_imageBytes

#print axioms SQLeanite.PhysicalJournalRecovery.rollbackCommit_recovery_bytes_atomic

#print axioms SQLeanite.ProcessLock.acquire_establishes_owner

#print axioms SQLeanite.ProcessLock.release_requires_owner

#print axioms SQLeanite.ProcessLock.overlapping_critical_sections_rejected

#print axioms SQLeanite.ProcessLock.run_successfulTrace

#print axioms SQLeanite.ProcessLock.CompletedCriticalSection.exclusive

#print axioms SQLeanite.PhysicalFileAdapter.run_commitPlan

#print axioms SQLeanite.PhysicalFileAdapter.run_commitImagePlan

#print axioms SQLeanite.PhysicalFileAdapter.commitImage_crash_atomic

#print axioms SQLeanite.PhysicalWAL.decodeWords_encode

#print axioms SQLeanite.PhysicalWAL.Header.checksum_bytes

#print axioms SQLeanite.PhysicalWAL.decodeHeader_encode

#print axioms SQLeanite.PhysicalWAL.decodeFrame_encode

#print axioms SQLeanite.PhysicalWAL.decode_encode

#print axioms SQLeanite.PhysicalWALRecovery.frames_toWrites

#print axioms SQLeanite.PhysicalWALRecovery.recover_frames_equiv

#print axioms SQLeanite.Core.orderedUpsert_sorted

#print axioms SQLeanite.Core.Table.insertValues_exact

#print axioms SQLeanite.Core.Table.retainRows_exact

#print axioms SQLeanite.Core.Table.patchRows_exact

#print axioms SQLeanite.Core.Table.addIndex_exact

#print axioms SQLeanite.Core.Database.createTable_exact

#print axioms SQLeanite.Core.Database.updateTable_target

#print axioms SQLeanite.Core.Database.updateTable_frame

#print axioms SQLeanite.Core.Table.patchRowid_exact

#print axioms SQLeanite.Core.Table.findDeclaredTextRowid?_some_mem

#print axioms SQLeanite.Core.Table.updateWhere_exact

#print axioms SQLeanite.Core.Query.eval_width
