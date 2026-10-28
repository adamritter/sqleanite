import SQLeanite.CanonicalSchemaSQL
import SQLeanite.Core
import SQLeanite.CoreChunkPageDelta
import SQLeanite.CoreChunkPageState
import SQLeanite.CoreDecode
import SQLeanite.CoreDecode.DecodeCanonicalTableStepEncoded
import SQLeanite.CoreDurability
import SQLeanite.CoreEngine.ExecuteRollbackRestoresHeaders
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
import SQLeanite.CoreSQL.JoinStreamPrepared
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
import SQLeanite.SQLite.Scalar.TestBetweenArgumentError
import SQLeanite.SerializedConnection
import SQLeanite.TornStorage
import SQLeanite.WidePageTree

#print axioms SQLeanite.SQLite.CastType.affinity_empty

#print axioms SQLeanite.SQLite.CastType.affinity_nonempty

#print axioms SQLeanite.CoreFileEngine.requiresWriteAccess_readOnly

#print axioms SQLeanite.CoreFileEngine.requiresWriteAccess_schemaNoop

#print axioms SQLeanite.SQLite.Limit.integer_of_fits

#print axioms SQLeanite.SQLite.Limit.resolve_zero

#print axioms SQLeanite.CoreFileEngine.dataWriteNoop_insertSelect

#print axioms SQLeanite.CoreFileEngine.dataWriteNoop_commit

#print axioms SQLeanite.CoreFileEngine.dataWriteNoop_release

#print axioms SQLeanite.SQLite.JoinType.classify_length

#print axioms SQLeanite.CoreJoin.matchingRows_unconstrained

#print axioms SQLeanite.CoreJoin.leftOuterFor_unconstrained_empty

#print axioms SQLeanite.CoreJoin.Operand.coercedColumn_null

#print axioms SQLeanite.CoreOptimizerBridge.joinOperand_value

#print axioms SQLeanite.CoreOptimizerBridge.fromJoinOperand_joinOperand

#print axioms SQLeanite.CoreJoinUsing.declaredColumn_visible

#print axioms SQLeanite.CoreJoin.distinctRows_keys

#print axioms SQLeanite.CoreJoin.distinctRows_key_nodup

#print axioms SQLeanite.CoreJoin.Query.finishRows_limit_zero

#print axioms SQLeanite.CoreJoin.Query.distinctInputRows_perm

#print axioms SQLeanite.CoreSQL.joinOrderColumns_projection

#print axioms SQLeanite.CoreJoin.OrderTerm.compareValues_null_left

#print axioms SQLeanite.CoreJoin.OrderTerm.compareValues_null_right

#print axioms SQLeanite.CoreJoin.projectRow_columns

#print axioms SQLeanite.Core.Schema.declaredColumn_visible

#print axioms SQLeanite.Core.Schema.column_visible_or_rowid

#print axioms SQLeanite.CoreJoinUsing.nameCandidates_declared

#print axioms SQLeanite.CoreJoin.Query.lookupInputRows_perm

#print axioms SQLeanite.CoreJoin.Predicate.truthy_null

#print axioms SQLeanite.CoreJoin.Predicate.isEqual_null_left

#print axioms SQLeanite.CoreJoin.Predicate.isEqual_present

#print axioms SQLeanite.CoreJoin.Predicate.isTruth_null

#print axioms SQLeanite.SQLite.Scalar.isTruthKeyword_collate

#print axioms SQLeanite.CoreSQL.joinOperandAffinity_plus

#print axioms SQLeanite.CoreJoin.Predicate.withCollation_binary

#print axioms SQLeanite.CoreJoin.Predicate.membership_eval

#print axioms SQLeanite.CoreJoin.Predicate.membership_null

#print axioms SQLeanite.SQLite.Scalar.prepareNullTest_token

#print axioms SQLeanite.SQLite.Scalar.parserNonNullLiteral_collate

#print axioms SQLeanite.SQLite.StaticCondition.testTerm_static

#print axioms SQLeanite.SQLite.StaticCondition.staticTerms_correct

#print axioms SQLeanite.CoreJoin.Predicate.constant_eval

#print axioms SQLeanite.SQLite.StaticCondition.Decision.result_correct

#print axioms SQLeanite.CoreJoin.Query.eval_limit_zero

#print axioms SQLeanite.CoreSQL.joinZeroQuery_limit

#print axioms SQLeanite.CoreSQL.joinQueryWithZero_existing

#print axioms SQLeanite.CoreJoin.Query.eval_empty_left

#print axioms SQLeanite.CoreJoin.Query.eval_empty_right_on

#print axioms SQLeanite.CoreSQL.joinQueryForRows_existing

#print axioms SQLeanite.CoreJoin.distinctCollatedRows_subset

#print axioms SQLeanite.CoreJoin.distinctCollatedRows_pairwise

#print axioms SQLeanite.CoreSQL.joinQueryComplete_existing

#print axioms SQLeanite.CoreOuterJoin.unmatchedRights_member

#print axioms SQLeanite.CoreOuterJoin.joinedRows_empty_left

#print axioms SQLeanite.CoreOuterJoin.joinedRows_full_empty_right

#print axioms SQLeanite.CoreOuterJoin.eval_width

#print axioms SQLeanite.CoreSQL.executeRightJoin_preserves_state

#print axioms SQLeanite.CoreSQL.joinMergedStar_right

#print axioms SQLeanite.CoreCreateTableAs.starMetadata_name

#print axioms SQLeanite.CoreJoin.Operand.mergedColumn_missing

#print axioms SQLeanite.CoreJoin.Operand.mergedColumn_present

#print axioms SQLeanite.CoreOrder.resolveNamesFuelWith_source

#print axioms SQLeanite.CoreOrder.resolveNamesFuelWith_alias

#print axioms SQLeanite.CoreSQL.joinAliasQuery_existing

#print axioms SQLeanite.CoreOrder.resolveJoinOnTerm_alias

#print axioms SQLeanite.CoreSQL.joinCompoundOperand_sides

#print axioms SQLeanite.CoreSQL.joinCompoundOperand_merged

#print axioms SQLeanite.CoreSQL.joinCompoundStarColumns_projection

#print axioms SQLeanite.SQLite.ExprCollation.argumentsKind_first

#print axioms SQLeanite.SQLite.ExprCollation.argumentsKind_column

#print axioms SQLeanite.CoreSQL.executeSelectBaseComplete_existing

#print axioms SQLeanite.CoreSQL.joinScalarRowsM_pure

#print axioms SQLeanite.CoreSQL.executeJoinScalar_preserves_state

#print axioms SQLeanite.CoreSQLReadText.executeSelectBaseComplete_eq_core

#print axioms SQLeanite.CoreSQL.joinScalarNullWalk_or

#print axioms SQLeanite.CoreSQL.joinScalarNullRejects_and

#print axioms SQLeanite.CoreSQL.joinScalarReducedSource_no_new_outer

#print axioms SQLeanite.CoreSQL.joinStreamStep_stopped

#print axioms SQLeanite.CoreSQL.joinStreamRight_stopped

#print axioms SQLeanite.CoreSQL.joinStreamSuffix_stopped

#print axioms SQLeanite.CoreSQL.joinStreamLeft_stopped

#print axioms SQLeanite.CoreSQL.executeSelectBaseObserved_refines

#print axioms SQLeanite.CoreSQL.executeSelect_without_compounds

#print axioms SQLeanite.CoreSQL.observeJoinedSelect_refines

#print axioms SQLeanite.CoreSQL.joinScalarRowsM_exchange_inner

#print axioms SQLeanite.CoreSQL.joinSearchCandidates_point_error

#print axioms SQLeanite.CoreSQL.joinSearchCandidates_scan_empty

#print axioms SQLeanite.CoreSQL.joinSearchCandidates_automatic_empty

#print axioms SQLeanite.CoreSQL.JoinSearchKey.retarget_value

#print axioms SQLeanite.CoreSQL.joinRightBoundForRows_where_failure

#print axioms SQLeanite.CoreSQL.joinEmptyOnQuery_where_failure

#print axioms SQLeanite.CoreSQL.joinScalarNullRejectsVisit_unpeeled_notNull

#print axioms SQLeanite.CoreSQL.joinFixedLookup_unfixed

#print axioms SQLeanite.CoreSQL.joinSearchMatches_without_inner_filter

#print axioms SQLeanite.CoreSQL.joinSearchKeyOrder_perm

#print axioms SQLeanite.CoreSQL.joinScalarOriginallyNullable_outer

#print axioms SQLeanite.CoreSQL.joinFixedConstantMatches_outer

#print axioms SQLeanite.SQLite.StaticCondition.Decision.test_and_stops

#print axioms SQLeanite.SQLite.Scalar.evalBetween_argument_error

#print axioms SQLeanite.SQLite.Scalar.testBetween_argument_error

#print axioms SQLeanite.CoreExpr.scanObserved_refines

#print axioms SQLeanite.CoreExpr.scanWindowObserved_refines

#print axioms SQLeanite.CoreSQL.observeSingleSelect_refines

#print axioms SQLeanite.CoreSQL.observeReadSelect_refines

#print axioms SQLeanite.CoreSQL.observeSingleSelect_direct

#print axioms SQLeanite.CoreSQL.joinSearchRangeTerms_between

#print axioms SQLeanite.CoreSQL.joinFixedReady_between_marked

#print axioms SQLeanite.SQLite.StaticCondition.Decision.testWith_scalar

#print axioms SQLeanite.SQLite.ApplicationHeader.signed_bounds

#print axioms SQLeanite.SQLite.ApplicationHeader.Metadata.get_set

#print axioms SQLeanite.SQLite.ApplicationHeader.Schemas.temporary_preserves_main

#print axioms SQLeanite.CoreHeaderPragma.execute_preserves_tables

#print axioms SQLeanite.CoreHeaderPragma.execute_read_preserves_state

#print axioms SQLeanite.CoreHeaderPragma.persistentWrites_temp

#print axioms SQLeanite.Core.execute_rollback_restores_headers

#print axioms SQLeanite.CoreSQL.joinUsingIndexEligible_without_shared

#print axioms SQLeanite.SQLite.JsonValid.evaluate_invalidMask

#print axioms SQLeanite.SQLite.JsonValid.evaluate_null_validMask

#print axioms SQLeanite.SQLite.JsonValid.textValid_standard_implies_json5

#print axioms SQLeanite.SQLite.JsonValid.blobLooks_requires_header

#print axioms SQLeanite.SQLite.Scalar.admissionErrorFuel_binary_left

#print axioms SQLeanite.SQLite.JsonAccess.load_null

#print axioms SQLeanite.SQLite.JsonAccess.evaluateType_null

#print axioms SQLeanite.SQLite.JsonAccess.evaluateLength_null

#print axioms SQLeanite.SQLite.JsonAccess.evaluateType_missing

#print axioms SQLeanite.SQLite.JsonAccess.arrayCountLoop_truncated

#print axioms SQLeanite.SQLite.Diagnostic.ofBytes_utf8

#print axioms SQLeanite.SQLite.Diagnostic.bytes_ordinary

#print axioms SQLeanite.SQLite.Diagnostic.ofBytes_nonutf8

#print axioms SQLeanite.CoreFileEngine.dataWriteNoop_update_payload

#print axioms SQLeanite.SQLite.Scalar.nameError_collapsed

#print axioms SQLeanite.SQLite.JsonEscape.unescape_short

#print axioms SQLeanite.SQLite.JsonPosition.evaluate_null

#print axioms SQLeanite.SQLite.JsonPosition.binary_depth

#print axioms SQLeanite.SQLite.JsonPosition.binary_missing_header

#print axioms SQLeanite.SQLite.JsonPosition.binaryChildren_odd_finished

#print axioms SQLeanite.SQLite.JsonPosition.textError_valid

#print axioms SQLeanite.SQLite.Percentile.fraction_median

#print axioms SQLeanite.SQLite.Percentile.finish_empty

#print axioms SQLeanite.SQLite.Percentile.step_invalid_fraction

#print axioms SQLeanite.SQLite.Percentile.run_empty

#print axioms SQLeanite.CoreAggregate.Accumulator.apply_countStar

#print axioms SQLeanite.CoreGrouped.emitOrderedObserved_limit_zero

#print axioms SQLeanite.CoreAggregate.accumulateSelectedRows_rejected

#print axioms SQLeanite.CoreAggregate.accumulateSelectedRows_predicate_error

#print axioms SQLeanite.CoreSQL.joinAggregateStreamFinish_error

#print axioms SQLeanite.SQLite.JsonBinary.evaluate_null

#print axioms SQLeanite.SQLite.JsonBinary.evaluate_admitted_blob

#print axioms SQLeanite.SQLite.JsonBinary.evaluate_invalid_text

#print axioms SQLeanite.SQLite.JsonBinary.stringKind_empty

#print axioms SQLeanite.SQLite.JsonPretty.evaluate_null

#print axioms SQLeanite.SQLite.JsonPretty.quoted_empty

#print axioms SQLeanite.SQLite.JsonPretty.hexNumber_empty

#print axioms SQLeanite.SQLite.JsonPretty.render_truncated

#print axioms SQLeanite.SQLite.JsonExtract.evaluate_no_arguments

#print axioms SQLeanite.SQLite.JsonExtract.evaluate_one_argument

#print axioms SQLeanite.SQLite.JsonExtract.integerValue_empty

#print axioms SQLeanite.SQLite.JsonExtract.valueAt_truncated

#print axioms SQLeanite.SQLite.JsonArrow.evaluate_null

#print axioms SQLeanite.SQLite.JsonArrow.abbreviated_root

#print axioms SQLeanite.SQLite.JsonArrow.abbreviated_zero

#print axioms SQLeanite.SQLite.JsonArrow.evaluate_null_path

#print axioms SQLeanite.SQLite.JsonEscape.unescape_invalid_separator

#print axioms SQLeanite.SQLite.JsonRemove.evaluate_no_arguments

#print axioms SQLeanite.SQLite.JsonRemove.evaluate_null

#print axioms SQLeanite.SQLite.JsonRemove.evaluate_identity

#print axioms SQLeanite.SQLite.JsonRemove.locate_target

#print axioms SQLeanite.SQLite.JsonPatch.evaluate_null

#print axioms SQLeanite.SQLite.JsonPatch.evaluate_null_patch

#print axioms SQLeanite.SQLite.JsonPatch.enlarged_zero

#print axioms SQLeanite.SQLite.JsonPatch.findMember_end

#print axioms SQLeanite.SQLite.JsonText.json_subtype

#print axioms SQLeanite.SQLite.JsonText.evaluate_null

#print axioms SQLeanite.SQLite.JsonText.arrow_null

#print axioms SQLeanite.SQLite.JsonText.extract_no_arguments

#print axioms SQLeanite.SQLite.JsonText.extract_one_argument

#print axioms SQLeanite.SQLite.JsonText.remove_no_arguments

#print axioms SQLeanite.SQLite.JsonText.patch_null

#print axioms SQLeanite.SQLite.Scalar.evalTyped_unary_plus

#print axioms SQLeanite.SQLite.Scalar.evalTyped_collate

#print axioms SQLeanite.SQLite.Scalar.evalTypedWith_column


#print axioms SQLeanite.CoreExpr.lookupScalar_value


#print axioms SQLeanite.CoreDecode.finishRowRead_unobserved


#print axioms SQLeanite.CoreSQL.executeCompoundTail_encoding_preserves_state


#print axioms SQLeanite.CoreCompoundTail.aliasName_encoded_input


#print axioms SQLeanite.SQLite.Scalar.compareTyped_binary


#print axioms SQLeanite.SQLite.Scalar.concatTyped_utf8


#print axioms SQLeanite.CoreAggregate.Result.scalar_value

#print axioms SQLeanite.CoreAggregate.Accumulator.apply_minimum_first

#print axioms SQLeanite.CoreAggregate.Accumulator.apply_maximum_first
#print axioms SQLeanite.SQLite.Scalar.evalInListTyped_empty


#print axioms SQLeanite.SQLite.Scalar.testBetweenTyped_argument_error


#print axioms SQLeanite.SQLite.Scalar.builtinTyped_stored_representation



#print axioms SQLeanite.CoreReturning.withValues_physical

#print axioms SQLeanite.CoreReturning.lookup_rowid

#print axioms SQLeanite.SQLite.JsonConstruct.finish_subtype

#print axioms SQLeanite.SQLite.JsonConstruct.quote_null

#print axioms SQLeanite.SQLite.JsonConstruct.append_tagged_text

#print axioms SQLeanite.SQLite.JsonConstruct.append_invalid_blob

#print axioms SQLeanite.SQLite.JsonConstruct.array_empty

#print axioms SQLeanite.SQLite.JsonConstruct.object_odd

#print axioms SQLeanite.SQLite.JsonConstruct.object_null_label

#print axioms SQLeanite.SQLite.JsonGroup.finish_empty_text_array

#print axioms SQLeanite.SQLite.JsonGroup.finish_empty_text_object

#print axioms SQLeanite.SQLite.JsonGroup.finish_empty_binary_array

#print axioms SQLeanite.SQLite.JsonGroup.finish_empty_binary_object

#print axioms SQLeanite.SQLite.JsonGroup.State.finish_error

#print axioms SQLeanite.SQLite.JsonGroup.State.step_null_label

#print axioms SQLeanite.SQLite.JsonGroup.State.append_pending

#print axioms SQLeanite.SQLite.JsonGroup.State.append_blob_error
