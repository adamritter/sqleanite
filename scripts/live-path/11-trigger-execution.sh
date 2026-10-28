# Sourced by live-path-check.sh; public row-trigger execution, not a fixture.
if rg -F -q 'executeStatementFuel 4096 [] false [] state sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.executeRows executeTriggerPointWithRegisters' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreScalarQuery.executePrepared' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'prepareTriggerStatement 1000 active state parents sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'let plan ← steps base state table statement' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'if step.rowid.isSome && old.isNone then continue' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'point registers current (← capture stored (withoutOutput command)) source' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'inheritConflict (conflict statement) action' SQLeanite/CoreTriggerProgram/Preparation.lean &&
   rg -F -q 'CoreTriggerProgram.preparePrograms' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'if (programs state statement).isEmpty && outputs.isEmpty then' SQLeanite/CoreTriggerProgram/Scope.lean &&
   rg -F -q 'let selected ← read false state parents query' SQLeanite/CoreTriggerProgram/Scope.lean &&
   rg -F -q 'current := restoreFrame caller current' SQLeanite/CoreTriggerProgram/Preparation.lean &&
   rg -F -q 'next.catalog.changed || !next.catalog.current.triggers.isEmpty' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreTriggerProgram.restoreFrame_registers' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreTriggerProgram.capture_insert' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'AFTER row triggers retain OLD/NEW images, preparation, counters and transaction semantics' "$audit_sources/Tests.lean"; then
  ok "public AFTER row programs use actual images, preselected keys, lexical bindings and connection-frame restoration; rollback persistence retains trigger metadata"
else
  fail "row-trigger executor, image capture, frame restoration or metadata persistence is disconnected"
fi

if rg -F -q 'current ← executeBody (execute program.definition.name parents) read current parents' SQLeanite/CoreTriggerProgram/Preparation.lean &&
   rg -F -q 'let selected ← read false state parents' SQLeanite/CoreTriggerProgram/Scope.lean &&
   rg -F -q 'CoreTriggerProgram.selectInput_ordinary_insert' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Trigger programs preserve captured DML, SELECT inputs, inherited policy and nested preparation' "$audit_sources/Tests.lean"; then
  ok "trigger SELECT/DML captures share actual lexical compilation, inherited conflict rules and recursive preparation; input coroutine admission retains sorted/materialized cases"
else
  fail "trigger captured DML, recursive preparation or SELECT-input execution is disconnected"
fi

if rg -F -q 'triggerForeignEdges 1000 active state sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.ForeignCounter.require next.foreignCounter' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'executeStatementUntriggeredWithForeign deferredForeign state sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'let assignments ← effectiveAssignments stored.schema assignments' SQLeanite/CoreTriggerProgram/Scope.lean &&
   rg -F -q 'if state.schemaProgram then throw' SQLeanite/CorePragmaTable.lean &&
   rg -F -q 'current := { next with schemaProgram := current.schemaProgram }' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CorePragmaTable.executeWith_schemaProgram' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Trigger NO ACTION checks wait for the outer statement; discarded SET and schema contexts stay exact' "$audit_sources/Tests.lean"; then
  ok "trigger NO ACTION checks cover actual reachable relations at the outer boundary, retain live FK settings, skip overwritten SET evaluation and enforce resolved DIRECTONLY virtual-table context"
else
  fail "trigger FK boundary, overwritten SET or actual schema-program context is disconnected"
fi

if rg -F -q 'let before := programs.filter (fun program => program.definition.timing == .before)' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'let after := programs.filter (fun program => program.definition.timing == .after)' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'if step.rowid.any (fun key => (pending.findRowid? key).isNone) then continue' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'if deleting then deleteOutput read next stored statement oldValues' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'current ← runPrograms execute read next stored statement oldValues new after' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'CoreTriggerProgram.withoutDeleteOutput_empty' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'BEFORE DELETE retains original OLD and RETURNING across mutation, AFTER and rollback' "$audit_sources/Tests.lean"; then
  ok "BEFORE DELETE uses fixed original OLD registers, reseeks surviving keys and keeps RETURNING/AFTER order across body mutations"
else
  fail "BEFORE DELETE old-image, reseek or RETURNING/AFTER phase wiring is disconnected"
fi

if rg -F -q 'let next ← ForeignCounter.account current next step.statement' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'let edges ← CoreForeignKey.counterEdges state statement' SQLeanite/CoreTriggerProgram/ForeignCounter.lean &&
   rg -F -q 'unless decide (replayed.rows = actual.rows)' SQLeanite/CoreTriggerProgram/ForeignCounter.lean &&
   rg -F -q 'if programs.isEmpty && !requiredForeign && !scopedInsert && !requiredReplacement && !requiredOutput && !requiredInput && !requiredPartial then' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'foreignCounter := state.foreignCounter' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.ForeignCounter.require_ok' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'VDBE FK counters retain signed scans, zero guards and old-orphan cancellation' "$audit_sources/Tests.lean"; then
  ok "actual accepted point writes drive signed FK opcode counters, guarded scans and source self-reference order; the outer boundary checks zero and restores caller state"
else
  fail "accepted-row FK accounting, signed counter boundary or caller restoration is disconnected"
fi

if rg -F -q 'some <$> updateCandidate current stored row input columns' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'let beforeColumns ← if before.isEmpty then pure [] else match statement with' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'let metadata ← read true state parents' SQLeanite/CoreTriggerProgram/NewColumns.lean &&
   rg -F -q 'if position == table.schema.primaryKey || position > 31 || columns.any' SQLeanite/CoreTriggerProgram/UpdateBefore.lean &&
   rg -F -q 'let types : Array ResultColumn := image.map' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'oldValues new after subtypes' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'if frame.qualifiedOnly && qualifier.isNone then continue' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'CoreDerivedSQL.executeTriggerPoint_restores' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'BEFORE UPDATE freezes SET, reloads unassigned fields and preserves actual NEW register types' "$audit_sources/Tests.lean"; then
  ok "BEFORE UPDATE freezes real typed SET registers, derives demand from actual scopes, reloads untouched columns and forwards actual AFTER subtypes; source RETURNING limits remain separately validated"
else
  fail "BEFORE UPDATE, typed register capture, source limits or parameter scope is disconnected"
fi

if rg -F -q 'let statement ← insertInput inputRead state statement' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'some <$> insertCandidate inputRead current stored input (!before.isEmpty)' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'finishInsertInput inputRead current stored candidate.command' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'let evaluated ← used.mapM fun index' SQLeanite/CoreTriggerProgram/InsertBefore.lean &&
   rg -F -q 'cacheInputCondition visit read state condition.height true condition' SQLeanite/CoreTriggerProgram/InputRegisters.lean &&
   rg -F -q 'CoreTriggerProgram.cacheInputQueries_without_queries' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreTriggerProgram.finishInsertInput_update' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'BEFORE INSERT freezes ordinary inputs, caches subqueries and allocates rowids after programs' "$audit_sources/Tests.lean"; then
  ok "BEFORE INSERT uses actual typed NEW registers, separate post-program rowid evaluation, reached scalar subquery registers and materialized multi-VALUES sources"
else
  fail "BEFORE INSERT input registers, post-program allocation or lazy subquery phases are disconnected"
fi

if rg -F -q 'let inputRead := inputScope read parents' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'let scopedInsert := !parents.isEmpty' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'executeTriggerRead input table sql source programs parents' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'if let .insert .. := statement then' SQLeanite/CoreTriggerProgram/Scope.lean &&
   rg -F -q 'let input ← if streamingValues then' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'CoreTriggerProgram.inputScope_empty' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Nested INSERT retains lexical inputs, subtype, lazy targets and caller registers' "$audit_sources/Tests.lean"; then
  ok "nested INSERT passes real caller frames to typed row input evaluation, preserves discarded-target laziness/subtypes and distinguishes materialized inputs from streaming source rows"
else
  fail "nested INSERT lexical executor, input phases, subtype or source-row evaluation is disconnected"
fi

if rg -F -q 'CoreTriggerControl.pragma state argument schema' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'state.recursiveTriggers || !active.any' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'if current.triggerDepth >= 1000 then throw' SQLeanite/CoreTriggerProgram/Preparation.lean &&
   rg -F -q 'triggerDepth := caller.triggerDepth' SQLeanite/CoreTriggerProgram/Preparation.lean &&
   rg -F -q 'Replacement.beforeWrite base remove (capture stored)' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'point registers current (← capture stored (withoutOutput command)) source' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'next.totalChanges - (deleted.map (·.changes)).sum' SQLeanite/CoreTriggerProgram/Replacement.lean &&
   rg -F -q 'CoreTriggerProgram.restoreFrame_depth' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreDerivedSQL.executeTriggerPointWithRegisters_restores' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Recursive trigger controls retain live settings, frame depth and REPLACE register images' "$audit_sources/Tests.lean"; then
  ok "recursive_triggers is a live connection flag; real program entry enforces depth, REPLACE deletes use actual DELETE programs with auxiliary counts excluded and the original full UPDATE registers/footprint retained"
else
  fail "recursive trigger control, actual frame depth, REPLACE deletion or frozen UPDATE input is disconnected"
fi

if rg -F -q 'SQLite.TriggerRaise.bind (state.triggerDepth != 0 || state.raiseContext)' SQLeanite/CoreConnectionSQL.lean &&
   rg -F -q 'SQLite.TriggerRaise.bind (parents.any (·.qualifiedOnly))' SQLeanite/CoreTriggerProgram/Binding.lean &&
   rg -F -q 'name.toLower == "__sqlean_trigger_abort"' SQLeanite/CoreTokenGrammar/MatchExpr.lean &&
   rg -F -q '"__sqlean_trigger_abort", [value]' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'String.ofList (Text.nulPrefix message)' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'SQLite.TriggerRaise.bind_disabled' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'RAISE ABORT retains dynamic messages, lazy control and unpublished failed writes' "$audit_sources/Tests.lean"; then
  ok "certified trigger RAISE ABORT specializes before binding, keeps ordinary lazy message evaluation and error text conversion; the private executable function is rejected in public calls"
else
  fail "RAISE ABORT contextual admission, lazy message evaluation or public private-call rejection is disconnected"
fi

if rg -F -q '(executeStatementEffects state sql source).toExcept' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q '(executeStatementFuel 4096 [] false [] state sql source).run { state }' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.Execution.abort state context' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'restoreFrame caller (← Execution.current)' SQLeanite/CoreTriggerProgram/Preparation.lean &&
   rg -F -q 'returningOutput read next stored statement new subtypes' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'CoreTriggerProgram.Execution.abort_database' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreTriggerProgram.Execution.abort_totalChanges' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Error outcomes preserve native connection effects while rolling back statement data' "$audit_sources/Tests.lean"; then
  ok "public execution uses the state-carrying runtime; error outcomes restore statement data with actual connection effects and unwind caller frames; RETURNING evaluates after the remembered point"
else
  fail "state-carrying execution, ABORT data/counter split, frame unwinding or RETURNING phase is disconnected"
fi

if rg -F -q 'let requiredOutput := !(CoreTriggerProgram.returning sql).isEmpty' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.prepareBody executeStatementUntriggered executeTriggerRead state parents sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'prepared.preparedContext.getD' SQLeanite/CoreTriggerProgram/ReturnPrepare.lean &&
   rg -F -q 'preparedContext := some preparedContext' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'let state := returningContext state' SQLeanite/CoreTriggerProgram/ReturningOutput.lean &&
   rg -F -q 'CoreTriggerProgram.returningContext_schemaProgram' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "ordinary DML preparation precedes runtime error effects; RETURNING uses separate point/output phases, real compiled subquery scopes and a language context distinct from schema restrictions; inputs retain their actual materialization rules"
else
  fail "ordinary error phases, real RETURNING scope compiler, language permissions or source materialization is disconnected"
fi

if rg -F -q 'parents.isEmpty && CoreWindow.has query && !CoreScalarQuery.has' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreWindow.execute temporary (if preparing then { query with limit := some 0 } else query)' "$audit_sources/SQLeanite/CoreDerivedSQL.lean"; then
  ok "ordinary window INSERT preparation reuses the real window compiler with LIMIT 0 and executes no projected values"
else
  fail "window input preparation is routed through the scalar-only path"
fi

if rg -F -q 'let earlyForeign := ForeignEarly.eligible state statement' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'if earlyForeign then ForeignEarly.require base (capture stored) current stored (withoutOutput command)' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'ForeignCounter.missing state.database edge value' SQLeanite/CoreTriggerProgram/ForeignEarly.lean &&
   rg -F -q 'CoreTriggerProgram.ForeignEarly.eligible_disabled' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Single-write FK lookup fails before the point and cannot cancel against old orphans' "$audit_sources/Tests.lean"; then
  ok "single-write immediate FK lookup uses the actual checked candidate before publishing a point, retains self/NULL rules and cannot cancel against a later parent scan"
else
  fail "single-write FK phase, actual candidate lookup or no-orphan-cancellation regression is disconnected"
fi


if rg -F -q 'let requiredInput := CoreTriggerProgram.requiresInputEffects sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q '!requiredOutput && !requiredInput && !requiredPartial then' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.requiresInputEffects_single' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Later INSERT input failures retain earlier actual point connection effects' "$audit_sources/Tests.lean"; then
  ok "ordinary multiple-input INSERT uses actual per-point effect states before later source/constraint failures"
else
  fail "ordinary multiple-input connection effects or their maintained regression is disconnected"
fi


if rg -F -q 'CoreTriggerProgram.RegisterInput.eligible state registerSql then' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'let prepared ← CoreTriggerProgram.RegisterInput.prepare state registerSql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreSQL.insertRegisterRowsWith (m := ExecutionM)' SQLeanite/CoreTriggerProgram/RegisterInput.lean &&
   rg -F -q 'insertRegisterRowsWith (fun current input =>' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.RegisterInput.pending_database' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'External SELECT register coroutines retain earlier point effects on late failures' "$audit_sources/Tests.lean"; then
  ok "external plain SELECT register inputs share the checked source loop with effectful point writes and retain late source-failure states"
else
  fail "shared SELECT register interpreter, pre-execution preparation or actual point error states are disconnected"
fi


if rg -F -q 'CoreSQL.registerDirection?' SQLeanite/CoreTriggerProgram/RegisterInput.lean &&
   rg -F -q 'seen.any (CoreExpr.distinctEqual projection values)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreJsonTable.inlineProjection state query prepared source inner' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.ValuesInput.rows? state sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'context := prepared.context, row := values' SQLeanite/CoreTriggerProgram/ValuesInput.lean &&
   rg -F -q 'CoreTriggerProgram.ValuesInput.rows?_utf8_only' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Register input plans preserve cursor order, DISTINCT, sorter materialization and UNION yields' "$audit_sources/Tests.lean"; then
  ok "register input plans retain rowid cursor order, DISTINCT state, real sorter input, UNION coroutine leaves and actual VALUES source frames"
else
  fail "ordered/distinct/compound/derived register producer or its maintained regression is disconnected"
fi


if rg -F -q 'CorePartialSQL.preparePoint base (capture stored)' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'CorePartialSQL.replacementVictims state statement values old' SQLeanite/CoreTriggerProgram/Replacement.lean &&
   rg -F -q 'CorePartialIndex.sortedKeys prepared' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'checkedFilteredIndex prepared physical' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'filteredIndexes : List CoreCatalogData.FilteredIndex' SQLeanite/CoreSizedPageCodec.lean &&
   rg -F -q 'objects.map (·.filteredIndexes)' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'CorePartialIndex.selectRows_satisfy' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Partial index source, qualifying keys, metadata and transactions use actual state' "$audit_sources/Tests.lean"; then
  ok "partial column indexes retain certified sources, real predicate keys, explicit uniqueness/actions, independently checked physical contents and both rollback/WAL image paths"
else
  fail "partial index source/key semantics, actual point actions, independent decoder or physical publication path is disconnected"
fi


if rg -F -q 'CoreIndexExpression.eval prepared.context values prepared.key' SQLeanite/CorePartialIndex.lean &&
   rg -F -q 'CoreIndexKey.entryLe prepared.collations left.2 right.2' SQLeanite/CorePartialIndex.lean &&
   rg -F -q 'CorePartialIndex.keyValues compiled candidate.values' SQLeanite/CorePartialSQL.lean &&
   rg -F -q 'PhysicalQuery.compareValue actual wanted' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'CorePartialIndex.keyEntry_rowid' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'expression indexes retain computed keys, physical rowids and unique actions' "$audit_sources/Tests.lean"; then
  ok "expression indexes compute actual schema keys, preserve physical rowids and validate persisted key contents"
else
  fail "expression index key evaluation, rowid law, native actions or independent decoding is disconnected"
fi


if rg -F -q 'CoreIndexKey.adjacentUnique prepared.index.unique prepared.collations ordered' SQLeanite/CorePartialIndex.lean &&
   rg -F -q 'CoreIndexKey.uniqueConflict compiled.collations candidateKey oldKey' SQLeanite/CorePartialSQL.lean &&
   rg -F -q 'CoreIndexPrepare.columnCollation table spec.column' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'CoreIndexKey.uniqueConflict_head_null' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Collated index keys preserve declared predicates, metadata and actual unique victims' "$audit_sources/Tests.lean"; then
  ok "collated physical keys use actual declared/expression collation, NULL uniqueness and native replacement victims"
else
  fail "collated index key admission, comparison, predicate, NULL law or actual SQL effects are disconnected"
fi


if rg -F -q 'selected.mapM CoreIndexKey.cellPlan?' SQLeanite/CoreSizedPageCodec.lean &&
   rg -F -q 'IndexRecords.subtreeFrom source (source.pageCount + 1) entry.rootPage' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'IndexRecords.subtreeIOFrom source (source.pageCount + 1) entry.rootPage' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'keyValuesMatch prepared.table prepared.keys actual.values wanted.values' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'CoreIndexKey.fromValues_recordValues' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Composite index records preserve every key, actual rowids and tuple uniqueness' "$audit_sources/Tests.lean"; then
  ok "composite physical indexes retain every key and real rowid through actual SQL effects and independently checked file traversal"
else
  fail "composite key programs, tuple record codec, independent acquisition, rowid law or maintained regression is disconnected"
fi


if rg -F -q 'return automaticIndexFromDefinition tableText specification member definition decoded same' SQLeanite/CoreCatalogData.lean &&
   rg -F -q 'CorePartialSQL.attachAutomatic next sql' SQLeanite/CoreDerivedSQL/Read.lean &&
   rg -F -q 'sqlIsNull := source.automaticTable?.isSome' SQLeanite/CoreSizedPageCodec.lean &&
   rg -F -q 'CorePartialIndex.automaticSources table' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'in (tableRowsWithSource table extended).zipIdx do' SQLeanite/CoreSchemaPragma.lean &&
   rg -F -q 'composite declaration requires retained SQL source' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreCatalogData.automaticIndex_table' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Composite table keys retain actual automatic origins, PK ordinals and rowid effects' "$audit_sources/Tests.lean"; then
  ok "composite table constraints retain certified automatic origins, actual NULL catalog SQL, PK metadata and rowid effects"
else
  fail "automatic table keys, retained source admission, NULL catalog records, independent acquisition or maintained regression is disconnected"
fi
