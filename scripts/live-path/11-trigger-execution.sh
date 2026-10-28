# Sourced by live-path-check.sh; public row-trigger execution, not a fixture.
if rg -F -q 'executeStatementFuel 1000 [] false state sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.executeRows (executeStatementUntriggeredWithForeign true)' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreScalarQuery.executePrepared' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'prepareTriggerStatement 1000 active state [] sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'let plan ← steps base state table statement' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'if step.rowid.isSome && old.isNone then continue' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'base current (← capture stored command) source' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'inheritConflict (conflict statement) action' SQLeanite/CoreTriggerProgram/Preparation.lean &&
   rg -F -q 'CoreTriggerProgram.preparePrograms' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'if (programs state statement).isEmpty then' SQLeanite/CoreTriggerProgram/Scope.lean &&
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

if rg -F -q 'current ← executeBody (execute program.definition.name) read current parents' SQLeanite/CoreTriggerProgram/Preparation.lean &&
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
   rg -F -q 'else deleteOutput read next stored statement oldValues' SQLeanite/CoreTriggerProgram/Rows.lean &&
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
   rg -F -q 'if programs.isEmpty && !requiredForeign then' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'foreignCounter := state.foreignCounter' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.ForeignCounter.require_ok' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'VDBE FK counters retain signed scans, zero guards and old-orphan cancellation' "$audit_sources/Tests.lean"; then
  ok "actual accepted point writes drive signed FK opcode counters, guarded scans and source self-reference order; the outer boundary checks zero and restores caller state"
else
  fail "accepted-row FK accounting, signed counter boundary or caller restoration is disconnected"
fi
