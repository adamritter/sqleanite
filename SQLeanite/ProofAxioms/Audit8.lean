import SQLeanite.CoreTriggerProgram.Rows
import SQLeanite.CoreTriggerSQL
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

#print axioms SQLeanite.SQLite.JsonGroup.State.finish_nonempty_binary_array

#print axioms SQLeanite.SQLite.JsonGroup.State.append_depth_error

#print axioms SQLeanite.CoreInsertPrepare.bindingFuel_literal

#print axioms SQLeanite.CoreInsertPrepare.check_default

#print axioms SQLeanite.SQLite.JsonReplace.argument_null

#print axioms SQLeanite.SQLite.JsonReplace.argument_ordinary_text

#print axioms SQLeanite.SQLite.JsonReplace.argument_admitted_blob

#print axioms SQLeanite.SQLite.JsonReplace.argument_invalid_blob

#print axioms SQLeanite.SQLite.JsonReplace.changes_none

#print axioms SQLeanite.SQLite.JsonReplace.changes_null_path

#print axioms SQLeanite.SQLite.JsonReplace.evaluate_no_arguments

#print axioms SQLeanite.SQLite.JsonReplace.evaluate_even

#print axioms SQLeanite.CoreReturning.Cell.writeAffinity_value

#print axioms SQLeanite.CoreReturning.defaultFromRegister_reuse

#print axioms SQLeanite.SQLite.JsonInsert.adjust_unchanged

#print axioms SQLeanite.SQLite.JsonInsert.lookup_insert_existing

#print axioms SQLeanite.SQLite.JsonInsert.substructure_empty_tail

#print axioms SQLeanite.SQLite.JsonInsert.changes_none

#print axioms SQLeanite.SQLite.JsonInsert.changes_null_path

#print axioms SQLeanite.SQLite.JsonInsert.evaluate_no_arguments

#print axioms SQLeanite.SQLite.JsonInsert.evaluate_even

#print axioms SQLeanite.CoreCatalogSQL.parse_print

#print axioms SQLeanite.CoreCatalogSQL.parse_text

#print axioms SQLeanite.CoreCatalogSQL.text_retain

#print axioms SQLeanite.CoreCatalogSQL.retain_text

#print axioms SQLeanite.Core.Table.parse_catalogSQL

#print axioms SQLeanite.Core.Table.withCatalogSQL_preserves

#print axioms SQLeanite.Core.Table.rebuildFromCatalog_exact

#print axioms SQLeanite.Core.Table.rebuildFromCatalog_catalogSQL

#print axioms SQLeanite.Core.Table.rebuild_withoutIndexes_fixed

#print axioms SQLeanite.Core.Table.rebuildFromCatalog_withoutIndexes_fixed

#print axioms SQLeanite.Core.Table.Equiv.catalogSQL_eq

#print axioms SQLeanite.CoreSourceSQL.retain_effect

#print axioms SQLeanite.CoreSourceSQL.executeStatement_create_noop

#print axioms SQLeanite.CoreSourceSQL.executeStatement_create_trace

#print axioms SQLeanite.CoreSourceSQL.executeStatement_error

#print axioms SQLeanite.CoreSourceSQL.executeStatement_add_trace

#print axioms SQLeanite.CoreSourceSQL.executeStatement_add_incomplete

#print axioms SQLeanite.CoreSourceSQL.executeStatement_renameTable_trace

#print axioms SQLeanite.CoreSourceSQL.executeStatement_renameColumn_trace

#print axioms SQLeanite.CoreSourceSQL.executeStatement_dropColumn_trace

#print axioms SQLeanite.SQLite.Version.version_value

#print axioms SQLeanite.SQLite.Version.source_value

#print axioms SQLeanite.SQLite.Scalar.builtin_version

#print axioms SQLeanite.SQLite.Scalar.builtin_source

#print axioms SQLeanite.SQLite.Scalar.resolutionErrorFuel_call_arguments

#print axioms SQLeanite.SQLite.Scalar.resolutionErrorFuel_pending_literal

#print axioms SQLeanite.SQLite.DateTime.parseValue_null

#print axioms SQLeanite.SQLite.DateTime.arguments_null

#print axioms SQLeanite.SQLite.DateTime.evaluate_unknown

#print axioms SQLeanite.SQLite.DateDifference.align_stopped

#print axioms SQLeanite.SQLite.DateDifference.align_exhausted

#print axioms SQLeanite.SQLite.DateDifference.difference_null_left

#print axioms SQLeanite.SQLite.DateTime.evaluate_null_argument

#print axioms SQLeanite.SQLite.DateDifference.evaluate_null_left

#print axioms SQLeanite.SQLite.DateDifference.evaluate_null_right

#print axioms SQLeanite.CoreLazyFileEngine.collectReads_scalar_miss

#print axioms SQLeanite.CoreLazyFileEngine.parseReadChunks_parse_error

#print axioms SQLeanite.CoreLazyFileEngine.parseReadChunks_shape_miss

#print axioms SQLeanite.CoreSchemaPragma.pragmaListRows_length

#print axioms SQLeanite.CoreSchemaPragma.result_unknown_schema

#print axioms SQLeanite.CoreSourceSQL.errorMessage_pragma_schema

#print axioms SQLeanite.CoreHeaderPragma.persistentWrites_unknown_schema

#print axioms SQLeanite.CoreSizedPageCodec.flatten_paginate

#print axioms SQLeanite.CoreSizedPageCodec.tablePlan?_contents

#print axioms SQLeanite.CoreSizedPageCodec.indexPlan?_contents

#print axioms SQLeanite.CoreSizedPageCodec.indexPlan?_balanced

#print axioms SQLeanite.CoreSizedPageCodec.local_overflow_reassembles

#print axioms SQLeanite.SQLite.IndexCatalog.rollback_restores

#print axioms SQLeanite.SQLite.IndexCatalog.rollbackTo_savepoint

#print axioms SQLeanite.SQLite.IndexCatalog.commit_preserves_sources

#print axioms SQLeanite.CoreConnectionSQL.account_database

#print axioms SQLeanite.CoreConnectionSQL.account_total

#print axioms SQLeanite.CoreDerivedSQL.executeRead_preserves_state

#print axioms SQLeanite.CoreDerivedSQL.enqueue_all_keeps_rows

#print axioms SQLeanite.CoreLastInsert.bind_call

#print axioms SQLeanite.CoreConnectionSQL.account_lastInsertRowid

#print axioms SQLeanite.CoreSQL.insertRegisterRows_limit_zero

#print axioms SQLeanite.CorePragmaTable.bindHidden_empty

#print axioms SQLeanite.SQLite.JsonTable.evaluate_null

#print axioms SQLeanite.CoreWindow.insert_length

#print axioms SQLeanite.SQLite.AggregateSum.State.inverse_null

#print axioms SQLeanite.CoreScalarQuery.scalarLimit_zero

#print axioms SQLeanite.SQLite.Scalar.evalTypedQueryFuelWithConstants_subquery

#print axioms SQLeanite.CoreUpsertSQL.choose_mem

#print axioms SQLeanite.CoreUpsertSQL.update_nothing

#print axioms SQLeanite.CoreCatalogImage.Checked.applied_decode

#print axioms SQLeanite.CoreCatalogImage.Checked.recovery

#print axioms SQLeanite.CoreFileAdapter.CommittedCatalog.trace_eq

#print axioms SQLeanite.CoreAutomaticIndex.contains_declared

#print axioms SQLeanite.CoreDecode.decodeCanonicalIndex_missing_primary

#print axioms SQLeanite.CoreSchemaRead.execute_preserves_state

#print axioms SQLeanite.CoreFileAdapter.utf8TextEncoding_iff

#print axioms SQLeanite.CoreCheck.failure_empty

#print axioms SQLeanite.CoreCatalogSQL.retain_compiledChecks

#print axioms SQLeanite.Core.Table.createRow_checks

#print axioms SQLeanite.CoreDerivedSQL.streamingValues_ordered

#print axioms SQLeanite.CoreCheck.forUpdate_insert

#print axioms SQLeanite.CoreCheck.forUpdate_member

#print axioms SQLeanite.CoreUpdateRow.install_rows

#print axioms SQLeanite.CoreUpdateRow.publish_lastInsertRowid

#print axioms SQLeanite.SQLite.Scalar.hasFunction_scalarSubquery

#print axioms SQLeanite.SQLite.Scalar.hasFunction_existsSubquery

#print axioms SQLeanite.CoreFileAdapter.headerOrEmpty_empty

#print axioms SQLeanite.CoreFileAdapter.headerOrEmpty_short_nonempty

#print axioms SQLeanite.CoreFileAdapter.headerOrEmpty_singleton

#print axioms SQLeanite.CoreScalarQuery.scan_limit_zero

#print axioms SQLeanite.CoreScalarQuery.setTruth_empty

#print axioms SQLeanite.CoreTokenGrammar.inTableNames?_where

#print axioms SQLeanite.CoreCheck.requireRows_checked

#print axioms SQLeanite.CoreCatalogSQL.retain_compiledForeignKeys

#print axioms SQLeanite.Core.State.recordForeignWrite_database

#print axioms SQLeanite.CoreForeignKey.requireTransition_clause

#print axioms SQLeanite.CoreForeignKey.pragma_set_in_transaction

#print axioms SQLeanite.CoreForeignKeyData.referenceSatisfied_null

#print axioms SQLeanite.SQLite.SchemaHash.insert_length

#print axioms SQLeanite.SQLite.SchemaHash.rollback_unchanged

#print axioms SQLeanite.SQLite.ForeignKeyCatalog.rewrite_no_targets

#print axioms SQLeanite.CoreForeignKeyRename.execute_unrelated

#print axioms SQLeanite.CoreForeignKeySyntax.collect_no_tables

#print axioms SQLeanite.CoreStrictSyntax.accepts_any

#print axioms SQLeanite.CoreStrictSyntax.require_checked

#print axioms SQLeanite.CoreCatalogSQL.retain_compiledStrictColumns

#print axioms SQLeanite.CoreStrictSyntax.lowerColumn_any

#print axioms SQLeanite.CoreSourceSQL.executeStatement_strict_trace

#print axioms SQLeanite.CoreGeneratedSyntax.order_empty

#print axioms SQLeanite.CoreGeneratedSyntax.affected_empty

#print axioms SQLeanite.CoreCatalogSQL.retain_compiledGeneratedColumns

#print axioms SQLeanite.CoreGeneratedSQL.calculate_empty

#print axioms SQLeanite.CoreSourceSQL.requireStoredEmpty_rejects_nonempty

#print axioms SQLeanite.CoreSQL.prepareInsertTargets_ordinary

#print axioms SQLeanite.SQLite.Scalar.functionError_boundValue

#print axioms SQLeanite.SQLite.ExprCollation.explicit_overrides_declared

#print axioms SQLeanite.SQLite.ExprCollation.effective_declared_column

#print axioms SQLeanite.CoreCollationSyntax.forTable_binary

#print axioms SQLeanite.CoreCatalogSQL.retain_compiledCollations

#print axioms SQLeanite.CoreDeclaredCollationSQL.tableUses_canonical

#print axioms SQLeanite.CoreScalarQuery.membershipCollation_explicit_right

#print axioms SQLeanite.CoreScalarQuery.membershipCollation_default_left

#print axioms SQLeanite.CoreSQL.requiresCompoundCollation_no_compounds

#print axioms SQLeanite.CoreScalarQuery.membershipOperand_last

#print axioms SQLeanite.CoreDerivedSQL.carryCollations_names

#print axioms SQLeanite.CoreDerivedSQL.enqueueCollated_all_keeps_rows

#print axioms SQLeanite.CoreDerivedSQL.enqueueCollated_duplicate

#print axioms SQLeanite.CoreScalarQuery.identitySources_input

#print axioms SQLeanite.CoreSQL.JoinSearchKey.collation_original

#print axioms SQLeanite.SQLite.StaticCondition.resolutionForbidden_declared

#print axioms SQLeanite.CoreCatalogData.view_decoded

#print axioms SQLeanite.CoreCatalogData.View.definition_of_text_eq

#print axioms SQLeanite.CoreCatalogData.State.acknowledge_unchanged

#print axioms SQLeanite.CoreViewSQL.transition_database

#print axioms SQLeanite.CoreViewSQL.orderDatabase_tables_perm

#print axioms SQLeanite.CoreViewRename.execute_unrelated

#print axioms SQLeanite.CoreCatalogImage.attachObjects_matches

#print axioms SQLeanite.CoreFileEngine.requiresPublication_table_only

-- Trigger catalog source and statement-completion boundaries.
#print axioms SQLeanite.SQLite.Script.trigger_body_semicolon
#print axioms SQLeanite.SQLite.Script.trigger_final_semicolon
#print axioms SQLeanite.CoreCatalogData.trigger_decoded
#print axioms SQLeanite.CoreCatalogData.triggerAtOwner_owner
#print axioms SQLeanite.CoreCatalogData.Trigger.definition_of_text_eq
#print axioms SQLeanite.CoreTriggerSQL.removeDroppedOwners_database
#print axioms SQLeanite.CoreDecode.catalogFromPageSource_shallow
#print axioms SQLeanite.CoreSchemaRead.currentRecords_durable

#print axioms SQLeanite.CoreTriggerProgram.programs_empty
#print axioms SQLeanite.CoreTriggerProgram.bindEntryChanges_other
#print axioms SQLeanite.CoreTriggerProgram.restoreFrame_database
#print axioms SQLeanite.CoreTriggerProgram.restoreFrame_registers
#print axioms SQLeanite.CoreTriggerProgram.restoreFrame_total
#print axioms SQLeanite.CoreTriggerProgram.capture_insert

#print axioms SQLeanite.CoreTriggerProgram.inheritConflict_default
#print axioms SQLeanite.CoreTriggerProgram.selectInput_ordinary_insert
#print axioms SQLeanite.CoreTriggerProgram.streamingInput_ordered

#print axioms SQLeanite.CoreTriggerProgram.effectiveAssignments_empty
#print axioms SQLeanite.CoreTriggerProgram.restoreFrame_context
#print axioms SQLeanite.CorePragmaTable.executeWith_schemaProgram

#print axioms SQLeanite.CoreTriggerProgram.withoutDeleteOutput_empty

#print axioms SQLeanite.CoreTriggerProgram.ForeignCounter.decrement_zero
#print axioms SQLeanite.CoreTriggerProgram.ForeignCounter.decrement_nonzero
#print axioms SQLeanite.CoreTriggerProgram.ForeignCounter.require_ok

#print axioms SQLeanite.CoreTriggerProgram.registerExpression_zero
#print axioms SQLeanite.CoreDerivedSQL.executeTriggerPoint_restores
