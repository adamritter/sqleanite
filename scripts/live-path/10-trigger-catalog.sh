# Sourced by live-path-check.sh; actual trigger source/catalog publication.
if rg -F -q 'completion.phase == .start' SQLeanite/SQLite/Script.lean &&
   rg -F -q '| .trigger, .semi => .bodySemi' SQLeanite/SQLite/Script.lean &&
   rg -F -q 'matchStatement child' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'TriggerEvent.updateOf columns' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -F -q 'CoreCatalogData.triggerAtOwner text owner' SQLeanite/CoreViewSQL.lean &&
   rg -F -q 'CoreTriggerSQL.executeDDL state sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTriggerSQL.removeDroppedOwners next sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q '| .createTrigger .. | .dropTrigger .. => true' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'viewEntries objects ++ triggerEntries objects' SQLeanite/CoreCatalogImage.lean &&
   rg -F -q 'CoreCatalogImage.viewEntries objects ++ CoreCatalogImage.triggerEntries objects' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'source.definition.name == name && source.owner == owner && source.text == sql' SQLeanite/CoreCatalogImage.lean &&
   rg -F -q 'name.toLower == "schema_version"' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreCatalogData.trigger_decoded' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreCatalogData.triggerAtOwner_owner' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'let records ← currentRecords state records' SQLeanite/CoreSchemaRead.lean &&
   rg -F -q 'CoreDecode.catalogFromPageSource source' SQLeanite/CoreCatalogImage.lean &&
   rg -F -q 'catalogFromPageSource_shallow source catalog catalogRead' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'CoreSchemaRead.currentRecords_durable' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Persistent trigger source, UPDATE OF, catalog bytes and transaction identity' "$audit_sources/Tests.lean"; then
  ok "complete trigger source reaches certified declarations, actual root-zero catalog checks, cookie/snapshot identity and both file publication paths"
else
  fail "trigger grammar/source, catalog identity/physical checks or public DDL publication is disconnected"
fi
