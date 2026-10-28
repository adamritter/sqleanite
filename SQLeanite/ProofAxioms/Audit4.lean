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

#print axioms SQLeanite.Core.Query.eval_indexed

#print axioms SQLeanite.CellPagination.flatten_paginateCells

#print axioms SQLeanite.CellPagination.paginateCells_fits

#print axioms SQLeanite.CellPagination.fastFit_iff

#print axioms SQLeanite.Core.orderedUpsert_eq_orderedUpsertTR

#print axioms SQLeanite.Core.mem_orderedUpsert_self

#print axioms SQLeanite.Core.mem_orderedUpsert_of_mem

#print axioms SQLeanite.Core.mem_orderedUpsert_iff

#print axioms SQLeanite.Core.orderedUpsert_perm

#print axioms SQLeanite.Core.length_orderedUpsert_of_fresh

#print axioms SQLeanite.CoreFile.tableLeaves_storedCells

#print axioms SQLeanite.CoreFile.tableLeaves_fit

#print axioms SQLeanite.CoreFile.sortedIndexRows_perm

#print axioms SQLeanite.CoreFile.integerIndexRowLe_trans

#print axioms SQLeanite.CoreFile.integerIndexRowLe_total

#print axioms SQLeanite.CoreFile.textIndexRowLe_trans

#print axioms SQLeanite.CoreFile.textIndexRowLe_total

#print axioms SQLeanite.CorePageLoad.open?_represents

#print axioms SQLeanite.CorePageLoad.loadNode_decodes

#print axioms SQLeanite.CorePageLoad.loadOpenTable?_decode

#print axioms SQLeanite.CorePageLoad.open?_decode

#print axioms SQLeanite.CorePageLoad.openGenerated?_represents

#print axioms SQLeanite.CoreDecode.rebuildCanonicalDatabase_overflowEncoded

#print axioms SQLeanite.CoreFileAdapter.certifyIndexEncoding?_exact

#print axioms SQLeanite.CoreFileAdapter.indexPageWrites_length

#print axioms SQLeanite.CoreFileAdapter.ValidatedOpenState.retarget?_state

#print axioms SQLeanite.CoreFileAdapter.ValidatedOpenState.retarget?_indexImage

#print axioms SQLeanite.CoreFileAdapter.generatedOpenState?_database

#print axioms SQLeanite.CoreFileAdapter.generatedOpenState?_allocationWellFormed

#print axioms SQLeanite.CoreFileAdapter.retainGeneratedState?_state

#print axioms SQLeanite.CoreFileAdapter.retainGeneratedState?_allocationWellFormed

#print axioms SQLeanite.CoreFileAdapter.changedPageWrites_sublist

#print axioms SQLeanite.CoreFileAdapter.omitted_changedPageWrites_matches

#print axioms SQLeanite.CoreFileAdapter.indexPageWrites_covers

#print axioms SQLeanite.CoreFileAdapter.indexPageWrites_eq_of_pageId_eq

#print axioms SQLeanite.CoreFileAdapter.deletedRowsOrdered?_length

#print axioms SQLeanite.CoreFileAdapter.certifyDecodedIndex?_source

#print axioms SQLeanite.CoreFileAdapter.certifyDecodedIndex?_exact

#print axioms SQLeanite.CoreFileAdapter.headerUsablePageSize?_val

#print axioms SQLeanite.CoreWAL.recover_forCoreImage

#print axioms SQLeanite.CoreWAL.decode_encode_forCoreImage

#print axioms SQLeanite.CoreWALFileEngine.needsWriter_false_member

#print axioms SQLeanite.Core.Query.eval_plannedRows

#print axioms SQLeanite.Core.Query.eval_primaryKey

#print axioms SQLeanite.Core.Table.chooseAccessPath_estimatedRows_le

#print axioms SQLeanite.Core.Predicate.optimize_eval

#print axioms SQLeanite.Core.Query.eval_optimize

#print axioms SQLeanite.CanonicalSchemaSQL.parseChars_tableChars

#print axioms SQLeanite.CanonicalIndexSQL.parseIntegerCertified_print

#print axioms SQLeanite.CoreFile.parseIntegerCertified_indexSQL

#print axioms SQLeanite.RuntimeRefinement.lockDiscipline_writersOrdered

#print axioms SQLeanite.RuntimeRefinement.tenureEvents_run

#print axioms SQLeanite.RuntimeRefinement.LiveHistory.serializable

#print axioms SQLeanite.CoreDecode.decodeCanonicalFile_encode

#print axioms SQLeanite.CoreDecode.decodeCatalogForOpen_schemaPageForEntries

#print axioms SQLeanite.CoreDecode.PageSourceRepresents.decode

#print axioms SQLeanite.CoreDecode.PageSourceDecodes.decode

#print axioms SQLeanite.CoreDecode.PageSourceDecodes.represents

#print axioms SQLeanite.CoreDecode.rebuildCanonicalDatabase_fixed

#print axioms SQLeanite.CorePageLoad.open?_pageSourceDecodes

#print axioms SQLeanite.CorePageLoad.open?_pageSourceRepresents

#print axioms SQLeanite.CorePageSource.readPage_applyWrites_of_not_written

#print axioms SQLeanite.CorePageSource.readPage_applyWrites_of_mem

#print axioms SQLeanite.CorePageSource.readPage_write_same

#print axioms SQLeanite.CorePageSource.readPage_write_other

#print axioms SQLeanite.CoreLocalizedRepresentation.pageSourceContains_applyWrites

#print axioms SQLeanite.CoreLocalizedRepresentation.readsPagesFrom_applyWrites_of_covered

#print axioms SQLeanite.CoreLocalizedRepresentation.readsPagesFrom_applyWrites

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexesDecode.consEncoded

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesDecode.mapM

#print axioms SQLeanite.CoreLocalizedRepresentation.TableOnSource.decode

#print axioms SQLeanite.CoreLocalizedRepresentation.TableOnSource.treeBounds

#print axioms SQLeanite.CoreLocalizedRepresentation.TableOnSource.transport

#print axioms SQLeanite.CoreLocalizedRepresentation.TableOnSource.retarget

#print axioms SQLeanite.CoreLocalizedRepresentation.TableOnSource.applyWritesOfUntouched

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesOnSource.tablesDecode

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesOnSource.entries_eq

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesOnSource.exists_table

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesOnSource.alignTables_none

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesOnSource.alignTables_none_mem

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesOnSource.alignTables_changed

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesOnSource.updateStateCandidate

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesOnSource.updateState

#print axioms SQLeanite.CoreChunkPageDelta.updateStateCandidate?_alignment

#print axioms SQLeanite.CoreChunkPageDelta.updateState?_alignment

#print axioms SQLeanite.CoreChunkPageState.State.tables_nodup

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesOnSource.ofEncodedTables

#print axioms SQLeanite.CoreLocalizedRepresentation.exists_tablesOnSource_encodeBulk_in

#print axioms SQLeanite.CoreDurability.exists_tablesOnStorage_encodeBulk

#print axioms SQLeanite.CoreLocalizedRepresentation.DatabaseOnSource.pageSourceRepresents

#print axioms SQLeanite.CoreLocalizedRepresentation.DatabaseOnSource.exists_table

#print axioms SQLeanite.CoreLocalizedRepresentation.DatabaseOnSource.pageCount_pos_of_table

#print axioms SQLeanite.CoreLocalizedRepresentation.DatabaseOnSource.decode

#print axioms SQLeanite.CoreLocalizedRepresentation.DatabaseOnSource.restate

#print axioms SQLeanite.CoreLocalizedRepresentation.DatabaseOnSource.updateState

#print axioms SQLeanite.CoreLocalizedRepresentation.DatabaseOnSource.updateStateIndexless

#print axioms SQLeanite.CoreDurability.localizedRepresentation_of_databaseOnSource

#print axioms SQLeanite.CoreLocalizedRepresentation.indexCertificates_encodeIndexes

#print axioms SQLeanite.CoreLocalizedRepresentation.indexGroupCertificates_encodeIndexTableGroups

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexOnSource.physical

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexGroupsOnSource.decode

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexOnSource.applyWritesBelow

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexGroupsOnSource.applyWritesBelow

#print axioms SQLeanite.CoreLocalizedRepresentation.exists_databaseOnSource_encodeBulk_in

#print axioms SQLeanite.CoreDurability.pageSource_storageImage

#print axioms SQLeanite.CoreDurability.exists_databaseOnStorage_encodeBulk

#print axioms SQLeanite.CoreDurability.exists_databaseOnStorage_padded

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexesDecode.validateForTable

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexGroupsDecode.validate

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexMetadataDecode.decode

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexMetadataDecode.retargetSchema

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexMetadataDecode.entries_nil

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexMetadataGroups.rebuild

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexMetadataGroups.retarget

#print axioms SQLeanite.CoreLocalizedRepresentation.IndexMetadataGroups.entries_nil_of_indexless

#print axioms SQLeanite.CoreLocalizedRepresentation.applyIndexesForOpen_of_indexGroups

#print axioms SQLeanite.CoreLocalizedRepresentation.applyIndexesForOpen_of_index_certificates

#print axioms SQLeanite.CoreLocalizedRepresentation.pageSourceContains_tableDeltaPages

#print axioms SQLeanite.CoreLocalizedRepresentation.decodeTableFrom_applyWrites

#print axioms SQLeanite.CoreLocalizedRepresentation.TablesDecode.consOverflowEncoded

#print axioms SQLeanite.CorePageSource.write_ofStorageImage

#print axioms SQLeanite.CorePageSource.applyWrites_ofStorageImage

#print axioms SQLeanite.CoreFileAdapter.byteArrayPageSource_eq_storageImage

#print axioms SQLeanite.CoreLocalizedRepresentation.pageSourceContains_tableDeltaComplete

#print axioms SQLeanite.CoreLocalizedRepresentation.pageSourceContains_tableDeltaComplete_extension

#print axioms SQLeanite.CoreLocalizedRepresentation.pageSourceContains_updateStateTree

#print axioms SQLeanite.CoreLocalizedRepresentation.pageSourceContains_updateStateTree_extension

#print axioms SQLeanite.CoreLocalizedRepresentation.pageSourceContains_updateStateCandidateTree

#print axioms SQLeanite.CoreLocalizedRepresentation.pageSourceContains_updateStateCandidateTree_extension

#print axioms SQLeanite.CoreLocalizedRepresentation.TableOnSource.updateStateInline

#print axioms SQLeanite.CoreLocalizedRepresentation.TableOnSource.updateStateInlineExtension

#print axioms SQLeanite.CoreLocalizedRepresentation.TableOnSource.updateStateCandidateInline

#print axioms SQLeanite.CoreLocalizedRepresentation.TableOnSource.updateStateCandidateInlineExtension

#print axioms SQLeanite.CorePageCodec.decodeFromPageSource_encodeBulk

#print axioms SQLeanite.CorePageCodec.decodeFromPageSource_encodeBulk_in

#print axioms SQLeanite.CorePageCodec.pageSourceRepresents_encodeBulk_in

#print axioms SQLeanite.CorePageCodec.decode_encodeBulk

#print axioms SQLeanite.CoreFreelistCodec.decodeFromPageSource_padded

#print axioms SQLeanite.CoreFreelistCodec.pageSourceRepresents_padded

#print axioms SQLeanite.CoreFreelistCodec.decode_paddedImage

#print axioms SQLeanite.CoreWriteBytes.decode_encoded_database

#print axioms SQLeanite.CoreWriteBytes.execute_createTable_to_bytes

#print axioms SQLeanite.CoreWriteBytes.execute_createIndex_to_bytes

#print axioms SQLeanite.CoreWriteBytes.execute_insert_to_bytes

#print axioms SQLeanite.CoreWriteBytes.execute_replace_to_bytes

#print axioms SQLeanite.CoreWriteBytes.execute_delete_to_bytes

#print axioms SQLeanite.CoreWriteBytes.execute_update_to_bytes

#print axioms SQLeanite.CoreWriteBytes.execute_commit_to_bytes

#print axioms SQLeanite.CoreWriteBytes.localized_state_represents_database

#print axioms SQLeanite.CorePageCodec.encodeBulkWithState_image

#print axioms SQLeanite.CorePageCodec.encodeBulkWithState_represents

#print axioms SQLeanite.CorePageCodec.decode_encodeChecked

#print axioms SQLeanite.CorePageCodec.encodeBulk_generatedHeader

#print axioms SQLeanite.CorePageCodec.encodeChunkNodeWithOverflow_noOverflow

#print axioms SQLeanite.CoreOverflow.resolvePlans_pages_eq_nil_of_payload_le

#print axioms SQLeanite.CoreOverflow.ycsbRow_inline

#print axioms SQLeanite.CoreOverflow.YCSBRow.inline

#print axioms SQLeanite.CorePageCodec.nodeRowsInline_of_mem_rows

#print axioms SQLeanite.CorePageCodec.tableStateRowsInline_of_rows

#print axioms SQLeanite.CorePageCodec.YCSBTableState.rowsInline

#print axioms SQLeanite.CorePageCodec.encodeChunkNodeWithOverflow_inline

#print axioms SQLeanite.CorePageCodec.encodeChunkNodeWithOverflow_of_inline

#print axioms SQLeanite.CorePageCodec.exists_encodeChunkNode_of_changed

#print axioms SQLeanite.CorePageCodec.exists_encodeChunkNode_of_pathAgrees

#print axioms SQLeanite.CorePageCodec.lookupTableRowidFrom_encodeChunkNodeWithOverflow

#print axioms SQLeanite.CoreDecode.AbstractTableTree.rangeCandidates_exact

#print axioms SQLeanite.CoreDecode.lookupTableRangeFrom_decodeAbstract_exact

#print axioms SQLeanite.CorePageCodec.decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow

#print axioms SQLeanite.CorePageCodec.lookupTableRangeFrom_encodeChunkNodeWithOverflow_exact

#print axioms SQLeanite.CoreDecode.decodeIndexCell_indexCell

#print axioms SQLeanite.CoreDecode.decodePackedIndexCellsFrom_resolvePlans

#print axioms SQLeanite.CoreDecode.decodeIndexLeafFrom_resolvedLeaf

#print axioms SQLeanite.RecursivePageBTree.IndexPlan.withCells?_balanced

#print axioms SQLeanite.CoreDecode.IndexPlanDecodes.of_cells

#print axioms SQLeanite.CoreDecode.decodeIndexSubtreeFrom_encodePagesFrom

#print axioms SQLeanite.CoreDecode.decodeIndexSubtreeFrom_encodeIndex

#print axioms SQLeanite.CoreFile.sortedIndexRows_pairwise_valueLe

#print axioms SQLeanite.CoreDecode.AbstractIndexTree.IntegerOrdered.of_pairwise

#print axioms SQLeanite.CoreDecode.decodeAbstractIndexTreeFrom_encodePagesFrom

#print axioms SQLeanite.CoreDecode.existsCertifiedIntegerIndex_of_encodeIndex

#print axioms SQLeanite.CoreDecode.lookupIndexValueFrom_encodeIndex_exact

#print axioms SQLeanite.CoreFile.sortedIndexRows_pairwise_valueLe_text

#print axioms SQLeanite.CoreDecode.AbstractIndexTree.wellRouted_of_pairwise_text

#print axioms SQLeanite.CoreDecode.lookupIndexValueFrom_text_encodeIndex_exact

#print axioms SQLeanite.CoreDecode.AbstractIndexTree.take_toList_eq_take_leftmostLeaf

#print axioms SQLeanite.CoreDecode.lookupIndexPrefixFrom_decodeAbstract_exact

#print axioms SQLeanite.CoreDecode.lookupIndexPrefixFrom_text_encodeIndex_exact

#print axioms SQLeanite.CoreDecode.AbstractIndexTree.cursorPrefix_eq_take

#print axioms SQLeanite.CoreDecode.indexPrefixFrom_decodeAbstract_exact

#print axioms SQLeanite.CoreDecode.indexPrefixFrom_text_encodeIndex_exact

#print axioms SQLeanite.CoreDecode.lookupIndexRangeFrom_encodeIndex_exact

#print axioms SQLeanite.CoreDecode.AbstractIndexTree.branchChain_toList

#print axioms SQLeanite.CoreDecode.decodeWideAbstractIndexTreeFrom_toList

#print axioms SQLeanite.CoreDecode.CertifiedWideIntegerIndex.valueEntries_exact

#print axioms SQLeanite.CoreDecode.CertifiedWideIntegerIndex.rangeEntries_exact

#print axioms SQLeanite.CoreDecode.CertifiedWideTextIndex.valueEntries_exact

#print axioms SQLeanite.CoreDecode.CertifiedWideTextIndex.rangeEntries_exact

#print axioms SQLeanite.CoreDecode.CertifiedAllValueIndex.valueEntries_exact

#print axioms SQLeanite.CoreDecode.CertifiedAllValueIndex.rangeEntries_exact

#print axioms SQLeanite.CoreFileAdapter.IntegerIndexRouting.valueEntries_exact
