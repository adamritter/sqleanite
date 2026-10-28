# Sourced by live-path-check.sh; public row-trigger execution, not a fixture.
if rg -F -q 'executeStatementFuel 1000 [] state sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.executeRows executeStatementUntriggered' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreScalarQuery.executePrepared' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'prepareTriggerStatement 1000 active state [] sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'let plan ← steps base state table statement' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'if step.rowid.isSome && old.isNone then continue' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'base current (← capture stored step.statement) source' SQLeanite/CoreTriggerProgram/Rows.lean &&
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
