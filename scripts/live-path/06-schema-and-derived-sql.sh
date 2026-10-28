# Sourced by live-path-check.sh; shares its failure status and scratch files.

if rg -F -q 'joinSearchTransitiveRoot context prepared on' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinSearchRangeRoot context prepared outerSide on' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinRightBoundForRows_where_failure' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.joinEmptyOnQuery_where_failure' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - empty join adapters retain WHERE planning and propagate rowid bounds\n'
else
  printf 'live-path check FAILED: reduced join cursors and rowid bounds\n' >&2
  status=1
fi

if rg -F -q 'joinSearchNullFilterRoot context prepared on' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'if select.limit == some 0 || joinScalarKnownEmpty context prepared source' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinScalarNullRejectsVisit_unpeeled_notNull' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo "ok - joined nonnull-rowid filters and ordered null-test preparation remain live"
else
  echo "not ok - joined null-filter preparation is not wired into execution"
  status=1
fi

if rg -F -q 'joinFixedMatches prepared input plan.fixed early' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinSearchMatches context prepared source plan row' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinFixedLookup_unfixed' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.joinSearchMatches_without_inner_filter' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo "ok - joined fixed-column preparation and inner WHERE filters remain live"
else
  echo "not ok - joined fixed-column or inner filter execution is missing"
  status=1
fi

if rg -F -q 'joinSearchKeys context prepared side terms' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinSearchDerivedRightRoot context prepared leftRoot on' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinSearchKeyOrder_perm' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo "ok - original and virtual joined search constraints preserve every candidate"
else
  echo "not ok - joined search term ordering is not wired into execution"
  status=1
fi

if rg -F -q 'joinScalarColumnNotNull context ref' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinScalarOriginallyNullable_outer' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo "ok - declared non-null columns retain outer-source preparation metadata"
else
  echo "not ok - declared join nullability is not wired into execution"
  status=1
fi

if rg -F -q 'joinFixedConstantMatches context prepared source on' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinSearchNullFilterCount context prepared .right > joinSearchNullFilterCount context prepared .left' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinFixedConstantMatches_outer' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo "ok - fixed WHERE constants and retained null filters drive joined cursor preparation"
else
  echo "not ok - fixed WHERE or retained null-filter preparation is missing"
  status=1
fi

if rg -F -q 'decision.testWith (fun atom wanted =>' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q '!joinScalarTrivialNotNull context prepared term' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'StaticCondition.Decision.test_and_stops' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo "ok - outer ON uses predicate truth and trivial non-null guards precede constant substitution"
else
  echo "not ok - NULL predicate preparation is not wired into execution"
  status=1
fi

if rg -F -q '.call "__sqlean_between" #[lhs, lower, upper] false' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -F -q 'BETWEEN syntax, not an internal function call' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'evalBetweenTyped eval operandAffinity argument lower upper' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'testBetween evaluate operandAffinity argument lower upper wanted' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'testEvaluatedTypedFuel eval operandAffinity false condition.height true condition' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'SQLite.Scalar.evalBetween_argument_error' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'SQLite.Scalar.testBetween_argument_error' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo "ok - BETWEEN retains its source boundary and shared tested operand"
else
  echo "not ok - BETWEEN expression semantics are not wired into execution"
  status=1
fi

if rg -F -q 'ctx.scanWindowObserved select.where_ expressions' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q '(filteredSelectReadReport state select source stored).toExcept' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'if report.error = some message then' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreExpr.scanWindowObserved_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.observeSingleSelect_direct' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.observeSingleSelect_refines' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.observeReadSelect_refines' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - single-source scalar reads retain prefixes with unchanged success/error execution\n'
else
  printf 'live-path check FAILED: single-source read observation\n' >&2
  status=1
fi

if rg -F -q '(joinSearchRangeTerms (SQLite.Scalar.conditionTerms expression)).any' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinSearchBetweenPair context prepared side (whereTerms ++ terms)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'let leftRange := joinSearchRowidRangeReduction context prepared .left on' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinSearchScanFilterRoot context prepared on' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinSearchRangeTerms_between' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.joinFixedReady_between_marked' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'StaticCondition.Decision.testWith_scalar' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - BETWEEN bounds drive cursor initialization and preserve outer markings\n'
else
  printf 'live-path check FAILED: BETWEEN cursor planning\n' >&2
  status=1
fi

if rg -F -q 'CoreHeaderPragma.execute state name argument schema' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreHeaderPragma.persistentWrites name argument schema' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'transactionHeadersChanged current' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'session next.database (some next.headers.main)' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreWALFileAdapter.reopenWithMetadata paths' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'Core.execute_rollback_restores_headers' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - application header PRAGMAs share transaction and persistent snapshot state\n'
else
  printf 'live-path check FAILED: application header transaction persistence\n' >&2
  status=1
fi

if rg -F -q 'context.shared.any (fun column => column.right == context.rightSchema.primaryKey)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'joinSearchRowidRangeReduction context prepared .right prepared.select.where_ > 20' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'let sharedRight := joinUsingAutomaticProbe context prepared .right' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'USING affinity requires executable cursor planning' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinUsingIndexEligible_without_shared' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'joinSearchIndependentRangeRoot context prepared .right on' "$audit_sources/SQLeanite/CoreSQL.lean"; then
  printf 'ok - joined rowid ordering and USING automatic-index sort boundaries\n'
else
  printf 'live-path check FAILED: joined range and USING cursor ordering\n' >&2
  status=1
fi

if rg -F -q '| "json_valid", [value] => JsonValid.evaluate value' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q '| "json_valid", [value, flags] => JsonValid.evaluate value (some flags)' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'SQLite.Scalar.resolutionError (fun q n => (ctx.column? q n).isSome) expression' SQLeanite/CoreExpr.lean &&
   rg -F -q 'let initial := (admissionErrorFuel 1 expression).orElse (fun _ => message)' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'JsonValid.textValid_standard_implies_json5' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Scalar.admissionErrorFuel_binary_left' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'JsonValid.evaluate_invalidMask' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - JSON validity uses the pure byte parser and pre-evaluation admission\n'
else
  printf 'live-path check FAILED: JSON validity admission\n' >&2
  status=1
fi

if rg -F -q '| "json_type", [value, path] => JsonAccess.evaluateType value (some path)' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q '| "json_array_length", [value, path] => JsonAccess.evaluateLength value (some path)' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'JsonAccess.evaluateType_missing' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'JsonAccess.arrayCountLoop_truncated' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - JSON type and array length use the pure path interpreter\n'
else
  printf 'live-path check FAILED: JSON access interpreter\n' >&2
  status=1
fi

if rg -F -q 'SQLite.Diagnostic.bytes message' Main.lean &&
   rg -F -q 'Diagnostic.ofBytes' SQLeanite/SQLite/JsonAccess.lean &&
   rg -F -q 'updatePayloadOnly current table assignments' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreFileEngine.dataWriteNoop_update_payload' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - byte diagnostics and unchanged non-key UPDATE persistence\n'
else
  printf 'live-path check FAILED: byte diagnostics or unchanged UPDATE persistence\n' >&2
  status=1
fi

if rg -F -q 'JsonEscape.unescape input finish fuel pos' SQLeanite/SQLite/JsonValid.lean &&
   rg -F -q 'JsonEscape.unescape input finish (input.size+1) pos' SQLeanite/SQLite/JsonAccess.lean &&
   rg -F -q 'JsonEscape.unescape_short' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - JSONB validation and label lookup share bounded escape decoding\n'
else
  printf 'live-path check FAILED: shared JSON escape decoding\n' >&2
  status=1
fi

if rg -F -q '| "json_error_position", [value] => pure (JsonPosition.evaluate value)' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'JsonPosition.binaryChildren_odd_finished' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'JsonPosition.textError_valid' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'JsonEscape.unescape input finish (input.size+1) pos' SQLeanite/SQLite/JsonPosition.lean; then
  printf 'ok - JSON error positions use the pure text and binary diagnostic parsers\n'
else
  printf 'live-path check FAILED: JSON error position parser\n' >&2
  status=1
fi

if rg -F -q '| "median" => some (.percentile .median)' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'state.percentile.step kind input.value input.second' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'SQLite.Percentile.step_invalid_fraction' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Float.fma (right-left) (index-Float.ofNat first) left' SQLeanite/SQLite/Percentile.lean; then
  printf 'ok - ordinary percentile aggregates use the shared pure accumulator\n'
else
  printf 'live-path check FAILED: percentile accumulator\n' >&2
  status=1
fi

if rg -F -q 'prepared.accumulateChecked ctx rows' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'state.ingest term ctx row' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'CoreGrouped.observe ctx select' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'Scalar.aggregateMisuse (ctx.bindNames expression)' SQLeanite/CoreExpr.lean &&
   rg -F -q 'CoreGrouped.emitOrderedObserved_limit_zero' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - aggregate steps interleave and ordered group reads retain emitted rows\n'
else
  printf 'live-path check FAILED: aggregate schedule or grouped read observation\n' >&2
  status=1
fi

if rg -F -q 'unless ← ctx.matches row condition do' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'prepared.results.accumulateSelected ctx select.where_' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreAggregate.accumulateSelectedRows_predicate_error' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - ungrouped WHERE and aggregate steps share the source-row scan\n'
else
  printf 'live-path check FAILED: ungrouped aggregate predicate scheduling\n' >&2
  status=1
fi

if rg -F -q 'joinAggregateStreamResult context prepared source traversal on left.rows right.rows' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'accumulator.ingest term ctx input' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreGrouped.observe prepared.context prepared.select inputs' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.joinAggregateStreamFinish_error' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - joined aggregates step during the shared join cursor loop\n'
else
  printf 'live-path check FAILED: joined aggregate streaming\n' >&2
  status=1
fi

if rg -F -q '| "jsonb", [value] => JsonBinary.evaluate value' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'JsonBinary.evaluate_admitted_blob' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'JsonBinary.evaluate_invalid_text' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  printf 'ok - JSONB encoding uses the pure byte encoder and shallow blob admission\n'
else
  printf 'live-path check FAILED: JSONB encoding\n' >&2
  status=1
fi

if rg -F -q '| "json_pretty", [value] => JsonPretty.evaluate value' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'let encoded ← JsonBinary.evaluate value' SQLeanite/SQLite/JsonPretty.lean &&
   rg -F -q 'JsonPretty.render_truncated' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - JSON pretty rendering uses pure binary translation and local validation'
else
  echo 'error - JSON pretty renderer is disconnected from public SQL' >&2
  status=1
fi
if rg -F -q '| "jsonb_extract", values => JsonExtract.evaluate values' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'let encoded ← JsonBinary.evaluate value' SQLeanite/SQLite/JsonExtract.lean &&
   rg -F -q 'JsonExtract.valueAt_truncated' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - JSON binary extraction uses pure lookup and SQL value conversion'
else
  echo 'error - JSON binary extraction is disconnected from public SQL' >&2
  status=1
fi
if rg -F -q '| .arrowText => JsonArrow.evaluate a b' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'let value ← JsonExtract.valueAt input pos' SQLeanite/SQLite/JsonArrow.lean &&
   rg -F -q 'JsonArrow.abbreviated_root' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - JSON SQL-value arrow uses pure abbreviated lookup and byte conversion'
else
  echo 'error - JSON SQL-value arrow is disconnected from public SQL' >&2
  status=1
fi
if rg -F -q '| "jsonb_remove", values => JsonRemove.evaluate values' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'let pos ← JsonAccess.select input (some pathValue)' SQLeanite/SQLite/JsonRemove.lean &&
   rg -F -q 'JsonRemove.evaluate_identity' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - JSON binary removal uses pure lookup, deletion and ancestor resizing'
else
  echo 'error - JSON binary removal is disconnected from public SQL' >&2
  status=1
fi
if rg -F -q '| "jsonb_patch", [target, patch] => JsonPatch.evaluate target patch' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'let result ← merge input patch 0 0 0' SQLeanite/SQLite/JsonPatch.lean &&
   rg -F -q 'JsonPatch.findMember_end' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - JSON binary merge patch uses pure label matching and byte edits'
else
  echo 'error - JSON binary merge patch is disconnected from public SQL' >&2
  status=1
fi
if rg -F -q '(·.value) <$> evalTypedFuelWithConstants' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'subtype : UInt8 := 0' SQLeanite/SQLite/ScalarValue.lean &&
   rg -F -q 'let value ← Scalar.builtin name values' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'Scalar.evalTyped_unary_plus' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - public SQL carries runtime subtypes through scalar expression evaluation'
else
  echo 'error - typed scalar evaluation is disconnected from public SQL' >&2
  status=1
fi
if rg -F -q 'let input := (← term.argument.mapM (ctx.evalTyped row))' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'SQLite.Scalar.evalTypedWith (lookup values row)' SQLeanite/CoreAggregateHaving.lean &&
   rg -F -q 'CoreNullConflict.prepareWith (·.value) defaultValue' SQLeanite/CoreReturning.lean &&
   rg -F -q 'CoreReturning.withValues cells row.values' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreReturning.withValues_physical' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - aggregate results and RETURNING retain runtime tags before physical storage'
else
  echo 'error - subtype metadata is disconnected at an aggregate or write boundary' >&2
  status=1
fi
if rg -F -q '| "json_array",_ => JsonConstruct.array false arguments.toList' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'if input.subtype == 74 then bytes else JsonPretty.quoted bytes' SQLeanite/SQLite/JsonConstruct.lean &&
   rg -F -q 'JsonExtract.unchecked bytes (4*bytes.size+4)' SQLeanite/SQLite/JsonConstruct.lean &&
   rg -F -q 'JsonConstruct.append_tagged_text' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'JsonConstruct.object_null_label' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - JSON constructors consume actual runtime tags and use pure byte rendering'
else
  echo 'error - JSON constructors are disconnected from runtime values or their contracts' >&2
  status=1
fi
if rg -F -q 'json := ← state.json.step kind' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'second := second.value' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'secondSubtype := second.subtype' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'let result ← state.json.finish kind binary' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'JsonGroup.State.step_null_label' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'JsonGroup.State.finish_nonempty_binary_array' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - JSON aggregates retain actual argument tags and use the shared ordered accumulator'
else
  echo 'error - JSON aggregate runtime or state contracts are disconnected' >&2
  status=1
fi
if test "$(rg -F -c 'if let .inl rows := source then CoreInsertPrepare.check stored.schema columns rows' "$audit_sources/SQLeanite/CoreSQL.lean")" = 2 &&
   rg -F -q 'Scalar.aggregateMisuseFuel column.expr.height column.expr' SQLeanite/CoreReturning.lean &&
   rg -F -q 'CoreInsertPrepare.check_default' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - INSERT VALUES preparation precedes named RETURNING aggregate diagnostics'
else
  echo 'error - INSERT source preparation or RETURNING binding is disconnected' >&2
  status=1
fi
if rg -F -q '| "json_replace",_ => JsonReplace.evaluate false arguments.toList' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'if input.subtype == 74 then' SQLeanite/SQLite/JsonReplace.lean &&
   rg -F -q 'JsonPatch.edit input pos (header+size) insert true' SQLeanite/SQLite/JsonReplace.lean &&
   rg -F -q 'JsonReplace.changes_null_path' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'JsonReplace.argument_ordinary_text' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - JSON replacement uses actual runtime tags and pure ancestor byte edits'
else
  echo 'error - JSON replacement runtime or contracts are disconnected' >&2
  status=1
fi
if rg -F -q 'insertReturningStep state tableName schema columns conflict' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'ctx projection counter inputs evaluateAll defaults' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreReturning.defaultFromRegister target' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'input.writeAffinity target.affinity' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreReturning.defaultFromRegister_reuse' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreReturning.Cell.writeAffinity_value' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - INSERT defaults retain statement register state and numeric coercion updates runtime tags'
else
  echo 'error - default-register or affinity metadata path is disconnected' >&2
  status=1
fi
if rg -F -q '| "json_insert",_ => JsonInsert.evaluate .insert false arguments.toList' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q '| "jsonb_set",_ => JsonInsert.evaluate .set true arguments.toList' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q '| "json_array_insert",_ => JsonInsert.evaluate .arrayInsert false arguments.toList' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'let insert ← JsonReplace.argument value' SQLeanite/SQLite/JsonInsert.lean &&
   rg -F -q 'JsonInsert.lookup_insert_existing' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'JsonInsert.substructure_empty_tail' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - JSON insertion and setting use pure path creation and actual argument metadata'
else
  echo 'error - JSON insertion runtime or contracts are disconnected' >&2
  status=1
fi
if rg -F -q 'def parseTableSchema := CoreCatalogSQL.parse' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'decoded : parse text = some schema' SQLeanite/CoreCatalogSQL.lean &&
   rg -F -q 'table.catalogSQL' "$audit_sources/SQLeanite/CoreFile.lean" &&
   rg -F -q 'Core.Table.rebuildFromCatalog schema [] rows sql' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'before.catalogSQL = after.catalogSQL' "$audit_sources/SQLeanite/CoreChunkPageDelta.lean" &&
   rg -F -q 'let next ← retainCreateTableAsSQL next name' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'Core.Table.withCatalogSQL_preserves' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreCatalogSQL.retain_text' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  echo 'ok - catalog SQL is schema-checked and retained across encoding, decoding and data writes'
else
  echo 'error - catalog source validation, CTAS formatting or preservation is disconnected' >&2
  status=1
fi

# Pinned SQLite identity functions and resolver diagnostics are on the Core path.
if rg -F -q 'match Version.value? name, args.isEmpty with' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'if Version.recognizes function then !arguments.isEmpty' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'SQLite.Scalar.resolutionError (fun _ _ => false) expression' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'Scalar.resolutionErrorFuel_call_arguments' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Scalar.resolutionErrorFuel_pending_literal' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'SQLite.Version.version_value' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'SQLite.Scalar.builtin_source' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "pinned SQLite identities and resolver diagnostics use the audited Core scalar path"
else
  fail "SQLite identity dispatch or resolver diagnostic wiring is missing"
fi


# Deterministic date/time functions stay in the pure scalar layer.
if rg -F -q 'if let some result := DateTime.evaluate? name args.toList then return ← result' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'else if DateTime.names.contains n then true' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'match arguments inputs with' SQLeanite/SQLite/DateTime.lean &&
   rg -F -q 'formatBytes state (Text.bytes format).toList' SQLeanite/SQLite/DateTime.lean &&
   rg -F -q 'SQLite.DateTime.arguments_null' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'SQLite.DateTime.evaluate_unknown' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "deterministic date/time parsing, modifiers and byte formatting use the Core scalar path"
else
  fail "date/time scalar routing or its audited boundary is missing"
fi


if rg -F -q '| "timediff", [left, right] => DateDifference.evaluate left right' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'else if n == "timediff" then args.size == 2' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'align forward (a.jd.getD 0) 24' SQLeanite/SQLite/DateDifference.lean &&
   rg -F -q 'DateDifference.align_stopped' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'DateDifference.align_exhausted' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'DateDifference.difference_null_left' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "calendar timediff uses the bounded Core scalar alignment and explicit NULL boundary"
else
  fail "timediff routing or audited alignment boundary is missing"
fi


if rg -F -q 'else if values.any Text.isNull then some (.ok .null)' SQLeanite/SQLite/DateTime.lean &&
   rg -F -q 'checkHost (if name == "strftime" then values.drop 1 else values)' SQLeanite/SQLite/DateTime.lean &&
   rg -F -q 'DateTime.evaluate_null_argument' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'DateDifference.evaluate_null_left' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'DateDifference.evaluate_null_right' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "date NULL values precede host-service rejection after ordinary argument evaluation"
else
  fail "date NULL and host diagnostic ordering is missing"
fi


if rg -F -q 'parseReadChunks (SQLite.Script.split sql) []' SQLeanite/CoreLazyFileEngine.lean &&
   rg -F -q 'CoreTokenGrammar.parseStatements chunk' SQLeanite/CoreLazyFileEngine.lean &&
   rg -F -q 'let next ← collectReads reversed statements.toList' SQLeanite/CoreLazyFileEngine.lean &&
   rg -F -q 'CoreLazyFileEngine.parseReadChunks_parse_error' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreLazyFileEngine.parseReadChunks_shape_miss' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "cold-read planning certifies source chunks and stops before unsupported statements"
else
  fail "cold-read chunk certification or early miss contracts are missing"
fi

if rg -F -q 'if name.toLower == "pragma_list" then pure pragmaListRows' SQLeanite/CoreSchemaPragma.lean &&
   rg -F -q 'SQLite.PragmaSyntax.knownNames.map fun name => [.text name]' SQLeanite/CoreSchemaPragma.lean &&
   rg -F -q 'CoreSchemaPragma.pragmaListRows_length' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSchemaPragma.result_unknown_schema' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'match pragmaSchemaToken source with' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'CoreSourceSQL.errorMessage_pragma_schema' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreHeaderPragma.persistentWrites_unknown_schema' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q '(schema.map (fun name => name.toLower == "main")).getD true' SQLeanite/CoreHeaderPragma.lean; then
  ok "PRAGMA listing follows recognized names and unknown-schema diagnostics preserve names"
else
  fail "PRAGMA list or exact schema rejection is disconnected"
fi

# Certified OVER capture must reach the production read-only window evaluator.
if grep -q 'the captured window specification' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'CoreWindow.execute temporary query' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   grep -q 'CoreWindow.insert_length' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "captured window syntax reaches the production evaluator and ordering proof"
else
  fail "window evaluation is disconnected from captured syntax or its proof"
fi

# Scalar subqueries retain token evidence and reach a lazy production callback.
if grep -q 'the captured scalar subquery' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   grep -q 'executeScalar fuel temporary bindings query' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreScalarQuery.executePrepared' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   grep -q 'scalarQuery := some evaluateQuery' SQLeanite/CoreScalarQuery.lean &&
   grep -q 'CoreScalarQuery.scalarLimit_zero' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "scalar query preparation and lazy callbacks remain connected to production reads"
else
  fail "scalar subquery preparation, callback or proof is disconnected"
fi

if rg -F -q 'CoreUpsertSQL.execute state base alias clauses' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q '| .upsert source alias clauses =>' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'CoreUpsertSQL.choose_mem' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreUpsertSQL.update_nothing' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "UPSERT token replay reaches checked Core writes and audited clause selection"
else
  fail "UPSERT replay, execution or clause contracts are disconnected"
fi

if rg -F -q 'CoreFileAdapter.commitCatalog connection.syncOps' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreCatalogImage.check old database image' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   rg -F -q 'writeMainPages paths.main checked.writes' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   rg -F -q 'CoreCatalogImage.Checked.recovery' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreFileAdapter.CommittedCatalog.trace_eq' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "retained index catalogs use checked components and the exact proved journal writes"
else
  fail "retained catalog validation, journal writes or proof is disconnected"
fi

if rg -F -q 'CoreSchemaRead.execute state select records' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreSchemaRead.execute state select records' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreSchemaRead.execute_preserves_state' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'sqlIsNull := CoreAutomaticIndex.contains table index' SQLeanite/CoreSizedPageCodec.lean &&
   rg -F -q 'CoreAutomaticIndex.find table entry.name' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'CoreAutomaticIndex.contains_declared' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "automatic UNIQUE indexes retain declaration metadata and schema reads preserve state"
else
  fail "automatic index metadata or physical schema-read routing is disconnected"
fi
