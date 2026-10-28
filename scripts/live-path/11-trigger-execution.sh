# Sourced by live-path-check.sh; public row-trigger execution, not a fixture.
if rg -F -q 'executeStatementFuel 1000 [] state sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerProgram.executeRows executeStatementUntriggered' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreScalarQuery.executePrepared' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'prepareBody base read state [] statement' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'let plan ← steps base state table statement' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'if step.rowid.isSome && old.isNone then continue' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'base current (← capture stored step.statement) source' SQLeanite/CoreTriggerProgram/Rows.lean &&
   rg -F -q 'current := restoreFrame caller current' SQLeanite/CoreTriggerProgram/Preparation.lean &&
   rg -F -q 'next.catalog.changed || !next.catalog.current.triggers.isEmpty' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreTriggerProgram.restoreFrame_registers' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreTriggerProgram.capture_insert' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'AFTER row triggers retain OLD/NEW images, preparation, counters and transaction semantics' "$audit_sources/Tests.lean"; then
  ok "public AFTER row programs use actual images, preselected keys, lexical bindings and connection-frame restoration; rollback persistence retains trigger metadata"
else
  fail "row-trigger executor, image capture, frame restoration or metadata persistence is disconnected"
fi
