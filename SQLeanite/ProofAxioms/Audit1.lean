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

#print axioms SQLeanite.QuerySemantics.predicatePushdown_eval

#print axioms SQLeanite.Binary64.compareBits_self

#print axioms SQLeanite.Binary64.compareBits_zero_signs

#print axioms SQLeanite.Binary64.compareInteger_zero

#print axioms SQLeanite.FileFormat.encodeU32_decode

#print axioms SQLeanite.FileFormat.decodeU32Bytes_sound

#print axioms SQLeanite.FileFormat.decodeHeaderPrefix_sound

#print axioms SQLeanite.FileFormat.decodeU32Values_sound

#print axioms SQLeanite.FileFormat.decodeDatabaseHeader_sound

#print axioms SQLeanite.CoreDurability.SQLiteHeaderMatches.firstPage

#print axioms SQLeanite.CoreDurability.SQLiteHeaderMatches.firstPage_of_freelistEmpty

#print axioms SQLeanite.CoreDurability.sqliteHeaderMatches_storageImage_encodeBulk

#print axioms SQLeanite.CoreDurability.sqliteHeaderMatches_storageImage_encodeBulk_freelistEmpty

#print axioms SQLeanite.CoreDurability.exists_framedDatabaseOnStorage_encodeBulk

#print axioms SQLeanite.CoreDurability.SQLiteHeaderMatches.applyWritesOfUnchangedPageZero

#print axioms SQLeanite.CoreDurability.SQLiteHeaderMatches.FreelistEmpty.applyWritesOfUnchangedPageZero

#print axioms SQLeanite.PhysicalQuery.sqlEquals_real_zero

#print axioms SQLeanite.PhysicalQuery.compareValue_eq_of_sqlEquals_true

#print axioms SQLeanite.CoreOverflow.CellPlan.local_append_overflow

#print axioms SQLeanite.CoreOverflow.CellPlan.pointer_substitution_preserves_length

#print axioms SQLeanite.CoreOverflow.overflowPageBytes_length

#print axioms SQLeanite.CoreOverflow.resolvePlans_cells_length

#print axioms SQLeanite.CoreOverflow.resolvePlans_nextPage

#print axioms SQLeanite.CoreOverflow.resolvePlans_noOverflow

#print axioms SQLeanite.CoreOverflow.CellPlan.overflowBytes_eq_nil_of_cellBytes_none

#print axioms SQLeanite.CoreOverflow.resolvePlans_of_cellBytes_none

#print axioms SQLeanite.CoreDecode.readOverflowFrom_generated

#print axioms SQLeanite.CoreDecode.readOverflowFrom_generated_fuel

#print axioms SQLeanite.CoreDecode.decodeRowCellsFrom_resolvePlans

#print axioms SQLeanite.QuerySemantics.constantFolding_eval

#print axioms SQLeanite.QuerySemantics.projectionElimination_eval

#print axioms SQLeanite.QuerySemantics.filterFusion_eval

#print axioms SQLeanite.QuerySemantics.joinRows_append_left

#print axioms SQLeanite.QuerySemantics.leftJoinRows_append_left

#print axioms SQLeanite.QuerySemantics.leftOuterOnRows_append_left

#print axioms SQLeanite.QuerySemantics.unionDistribution_eval

#print axioms SQLeanite.KRelation.select_unionAll

#print axioms SQLeanite.KRelation.swap_join

#print axioms SQLeanite.KRelation.project_unionAll

#print axioms SQLeanite.KRelation.groupSum_unionAll

#print axioms SQLeanite.KRelation.distinct_idempotent

#print axioms SQLeanite.RelationalAlgebra.ofList_append

#print axioms SQLeanite.RelationalAlgebra.ofList_bagIntersect

#print axioms SQLeanite.RelationalAlgebra.ofList_bagExcept

#print axioms SQLeanite.RelationalAlgebra.ofList_deduplicate

#print axioms SQLeanite.RelationalAlgebra.ofList_whereRows

#print axioms SQLeanite.RelationalAlgebra.ofList_joinRows

#print axioms SQLeanite.RelationalAlgebra.project_ofList

#print axioms SQLeanite.RelationalAlgebra.ofList_groupCountRows

#print axioms SQLeanite.RelationalAlgebra.ofList_groupSumRows

#print axioms SQLeanite.RelationalAlgebra.materializeCount_eval

#print axioms SQLeanite.RelationalAlgebra.materializeSum_eval

#print axioms SQLeanite.RelationalAlgebra.coreGroup_keyCount_eq_multiplicity

#print axioms SQLeanite.RelationalAlgebra.materializedCountRows_eq_coreGroup

#print axioms SQLeanite.RelationalAlgebra.coreGroup_keyRows_length_eq_keyCount

#print axioms SQLeanite.RelationalAlgebra.coreGroup_countStar_refines_materialized

#print axioms SQLeanite.RelationalAlgebra.coreGroup_sumColumn_refines_integerSum

#print axioms SQLeanite.RelationalAlgebra.core_sumIntegers_none_iff

#print axioms SQLeanite.RelationalAlgebra.coreGroup_sumColumn_null_iff

#print axioms SQLeanite.RelationalAlgebra.coreGroup_outputValue_refines

#print axioms SQLeanite.RelationalAlgebra.coreGroup_evalOutputs_refines

#print axioms SQLeanite.RelationalAlgebra.coreGroup_evalKeys_refines

#print axioms SQLeanite.RelationalAlgebra.coreGroup_eval_refines

#print axioms SQLeanite.RelationalAlgebra.joinedRows_eval

#print axioms SQLeanite.RelationalAlgebra.innerJoin_true_eval

#print axioms SQLeanite.RelationalAlgebra.permute_eval

#print axioms SQLeanite.RelationalAlgebra.permute_symm_eval

#print axioms SQLeanite.RelationalAlgebra.ofList_map_permute

#print axioms SQLeanite.RelationalAlgebra.distinct_permute

#print axioms SQLeanite.RelationalAlgebra.joinedLeftOuterRows_eval

#print axioms SQLeanite.RelationalAlgebra.listMultiplicity_leftOuterOnRows

#print axioms SQLeanite.RelationalAlgebra.joinedLeftOuterOn_eval

#print axioms SQLeanite.RelationalAlgebra.listMultiplicity_leftOuterOnRowsWith

#print axioms SQLeanite.RelationalAlgebra.joinedLeftOuterOnWith_eval

#print axioms SQLeanite.RelationalAlgebra.ofPlan?_eval

#print axioms SQLeanite.RelationalAlgebra.selectProductLeft_eval

#print axioms SQLeanite.RelationalAlgebra.selectUnionAll_eval

#print axioms SQLeanite.RelationalAlgebra.productUnionAllLeft_eval

#print axioms SQLeanite.RelationalAlgebra.productUnionAllRight_eval

#print axioms SQLeanite.RelationalAlgebra.selectFusion_eval

#print axioms SQLeanite.RelationalAlgebra.distinctIdempotent_eval

#print axioms SQLeanite.RelationalAlgebra.swapProduct_eval

#print axioms SQLeanite.RelationalAlgebra.reassociateProduct_eval

#print axioms SQLeanite.RelationalAlgebra.project_unionAll

#print axioms SQLeanite.RelationalAlgebra.groupCountUnionAll_eval

#print axioms SQLeanite.RelationalAlgebra.groupSumUnionAll_eval

#print axioms SQLeanite.RelationalAlgebra.selectLeftOuterLeft_eval

#print axioms SQLeanite.RelationalAlgebra.leftOuter_unmatched

#print axioms SQLeanite.RelationalAlgebra.leftOuter_matched

#print axioms SQLeanite.QuerySemantics.rewrite_sound

#print axioms SQLeanite.QuerySemantics.rewrite_sound_ordered

#print axioms SQLeanite.QuerySemantics.optimizePlan_eval

#print axioms SQLeanite.QuerySemantics.foldConstants_comparisonCount_le

#print axioms SQLeanite.QuerySemantics.profile_rows

#print axioms SQLeanite.QuerySemantics.projectionElimination_cost_le

#print axioms SQLeanite.QuerySemantics.projectionElimination_strict_on_nonempty_rows

#print axioms SQLeanite.QuerySemantics.constantFolding_cost_le

#print axioms SQLeanite.QuerySemantics.rewriteRoot_cost_le

#print axioms SQLeanite.QuerySemantics.optimizePlan_cost_le

#print axioms SQLeanite.QuerySemantics.filterFusion_not_unconditionally_cost_safe

#print axioms SQLeanite.CoreOptimizerBridge.toSemantics_eval

#print axioms SQLeanite.CoreOptimizerBridge.optimize_eval

#print axioms SQLeanite.CoreOptimizerBridge.optimize_innerJoinPlan_eval

#print axioms SQLeanite.CoreOptimizerBridge.optimize_leftOuterJoinPlan_eval

#print axioms SQLeanite.CoreOptimizerBridge.optimizeJoin_eval

#print axioms SQLeanite.CoreReadSemantics.optimize_tableFilterPlan_eval

#print axioms SQLeanite.CoreReadSemantics.query_eval_denotes

#print axioms SQLeanite.CoreReadSemantics.execute_query_denotes

#print axioms SQLeanite.CoreReadSemantics.optimize_joinPlan_eval

#print axioms SQLeanite.CoreReadSemantics.join_eval_denotes

#print axioms SQLeanite.CoreReadSemantics.execute_join_denotes

#print axioms SQLeanite.CoreReadSemantics.execute_group_denotes

#print axioms SQLeanite.CoreReadSemantics.execute_count_denotes

#print axioms SQLeanite.CoreReadSemantics.execute_sum_denotes

#print axioms SQLeanite.CoreReadSemantics.execute_extreme_denotes

#print axioms SQLeanite.CoreReadSemantics.compound_denotes

#print axioms SQLeanite.CoreReadSemantics.reorderValues_invert

#print axioms SQLeanite.CoreReadSemantics.reorderValues_invert_symm

#print axioms SQLeanite.CoreReadSemantics.permutedColumns_map_value

#print axioms SQLeanite.CoreReadSemantics.permuted_projection_denotes

#print axioms SQLeanite.RelationalAlgebra.ofList_cons

#print axioms SQLeanite.RelationalAlgebra.ofList_perm

#print axioms SQLeanite.CoreWriteSemantics.tableDenotation_orderedUpsert

#print axioms SQLeanite.CoreWriteSemantics.tableDenotation_orderedUpsert_fresh

#print axioms SQLeanite.CoreWriteSemantics.execute_insert_denotes

#print axioms SQLeanite.CoreWriteSemantics.execute_insert_multiplicity

#print axioms SQLeanite.CoreWriteSemantics.execute_deleteWhere_denotes

#print axioms SQLeanite.CoreWriteSemantics.canonicalize_findTable?

#print axioms SQLeanite.CoreWriteSemantics.insert_bytes_reopen_denotes

#print axioms SQLeanite.CoreWriteSemantics.insert_bytes_reopen_query_denotes

#print axioms SQLeanite.CoreWriteSemantics.insert_bytes_reopen_selects_row

#print axioms SQLeanite.CoreWriteSemantics.writeEffect_insert_bytes_reopen_denotes

#print axioms SQLeanite.CoreWriteSemantics.insertText_bytes_reopen_readText_denotes

#print axioms SQLeanite.PagedBTree.Tree.toList_insert

#print axioms SQLeanite.PagedBTree.Tree.toList_delete

#print axioms SQLeanite.PagedBTree.Tree.toList_sorted

#print axioms SQLeanite.PagedBTree.OverflowLeafPage.split_preserves_toList

#print axioms SQLeanite.PagedBTree.Tree.insert_wellFormed

#print axioms SQLeanite.TornStorage.pageAtomic_is_sectorOutcome

#print axioms SQLeanite.TornStorage.tornWitness_is_outcome

#print axioms SQLeanite.TornStorage.tornWitness_not_pageAtomic

#print axioms SQLeanite.RecursiveBPlusTree.Node.toList_insert

#print axioms SQLeanite.RecursiveBPlusTree.Node.toList_delete

#print axioms SQLeanite.RecursiveBPlusTree.Node.delete_rootValid

#print axioms SQLeanite.RecursiveBPlusTree.Node.checkRootValid_iff

#print axioms SQLeanite.RecursiveBPlusTree.Node.insert_balanced

#print axioms SQLeanite.RecursiveBPlusTree.Node.insertStep_valid

#print axioms SQLeanite.RecursiveBPlusTree.Node.insert_rootValid

#print axioms SQLeanite.RecursiveBPlusTree.Node.insertAll_rootValid

#print axioms SQLeanite.RecursiveBPlusTree.Node.checkBalanced_iff

#print axioms SQLeanite.RecursiveBPlusTree.Node.rangeScan_eq_range

#print axioms SQLeanite.RecursiveBPlusTree.Node.lookup_some_mem

#print axioms SQLeanite.RecursiveBPlusTree.Node.lookup_of_mem

#print axioms SQLeanite.PersistentPageTree.Node.insertStep_erases

#print axioms SQLeanite.PersistentPageTree.Node.insert_erases

#print axioms SQLeanite.PersistentPageTree.Node.deleteCandidate_rootId

#print axioms SQLeanite.PersistentPageTree.Node.insert_pathAgrees_of_noAllocation

#print axioms SQLeanite.PersistentPageTree.Store.insert_rootId

#print axioms SQLeanite.PersistentPageTree.Store.insert_represents

#print axioms SQLeanite.PersistentPageTree.Store.delete?_rootId

#print axioms SQLeanite.PersistentPageTree.Store.delete?_toList

#print axioms SQLeanite.PersistentPageTree.Store.reuseFresh?_rootId

#print axioms SQLeanite.PersistentPageTree.Store.reuseFresh_getD_rootId

#print axioms SQLeanite.PersistentPageTree.Store.reuseFresh?_toList

#print axioms SQLeanite.PersistentPageTree.Store.build_represents

#print axioms SQLeanite.PersistentPageTree.identifyFrom_pageIds

#print axioms SQLeanite.WidePageTree.interiorFanout_pageFit

#print axioms SQLeanite.WidePageTree.allocatedPage_ne_pendingBytePage

#print axioms SQLeanite.WidePageTree.numberedLeaves_root_ne_pendingBytePage

#print axioms SQLeanite.WidePageTree.numberedBranches_root_ne_pendingBytePage

#print axioms SQLeanite.WidePageTree.buildNumberedWithFanout_toList

#print axioms SQLeanite.WidePageTree.buildNumberedWithFanout_after_ge

#print axioms SQLeanite.CoreWideIndex.interiorFanoutFor_pos

#print axioms SQLeanite.WidePageTree.flatten_groups

#print axioms SQLeanite.WidePageTree.groups_eq_groupsTR

#print axioms SQLeanite.WidePageTree.build_toList

#print axioms SQLeanite.WidePageTree.build_valid

#print axioms SQLeanite.WidePageTree.buildNumbered_toList

#print axioms SQLeanite.WidePageTree.Store.build?_toList

#print axioms SQLeanite.WidePageTree.appendStep_toList

#print axioms SQLeanite.WidePageTree.appendStep_firstRootId

#print axioms SQLeanite.WidePageTree.Store.replaceLast?_toList

#print axioms SQLeanite.WidePageTree.Store.replaceLast?_rootId

#print axioms SQLeanite.WidePageTree.keysAdjacent_iff_pairwise

#print axioms SQLeanite.WidePageTree.Node.lastEntry?_witness

#print axioms SQLeanite.CoreWidePageState.buildTree_rows

#print axioms SQLeanite.CoreWidePageState.State.build?_represents

#print axioms SQLeanite.CoreWidePageCodec.encodeBulkInlineWithState_represents

#print axioms SQLeanite.CoreWidePageCodec.encodeChunkRoot_pageNumber

#print axioms SQLeanite.CoreWidePageLoad.load?_represents

#print axioms SQLeanite.CoreWidePageLoad.loadNode_decodes

#print axioms SQLeanite.CoreWidePageLoad.loadTable?_decodes

#print axioms SQLeanite.CoreWidePageDelta.entry_key_lt_of_rows_after

#print axioms SQLeanite.CoreWidePageDelta.replaceLast_rows

#print axioms SQLeanite.CoreWidePageDelta.append_rows

#print axioms SQLeanite.CoreWidePageDelta.append?_represents

#print axioms SQLeanite.CoreWidePageInverse.interiorChildren_interiorPage

#print axioms SQLeanite.CoreWidePageInverse.decodeSubtreeRowsFrom_encodeChunkNode

#print axioms SQLeanite.CoreWidePageInverse.decodeTableFrom_encodeTable

#print axioms SQLeanite.CoreWidePageInverse.pageSourceRepresents_encodeBulkInlineWithState
