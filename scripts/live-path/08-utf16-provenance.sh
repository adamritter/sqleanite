# Sourced by live-path-check.sh; checks the retained UTF-16 paths.
if rg -F -q 'textEncoding := header.textEncoding.val' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   rg -F -q 'textEncoding := header.textEncoding.val' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'records header.textEncoding.val' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreWALFileAdapter.textEncoding session' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreTextEncoding.fields source.textEncoding record.fields' SQLeanite/Runtime/Record.lean &&
   test "$(rg -F -c 'CoreTextEncoding.fields source.textEncoding record.fields' "$audit_sources/SQLeanite/CoreDecode.lean")" = 4 &&
   rg -F -q 'checkedEncodedIndex source.textEncoding table index physical' "$audit_sources/SQLeanite/CoreDecode.lean" &&
   rg -F -q 'terms.mapM encodedSpecification' SQLeanite/CoreOrder.lean &&
   rg -F -q 'SQLite.TextEncoding.bind state.catalog.current.textEncoding' SQLeanite/CoreConnectionSQL.lean &&
   rg -F -q '| "__sqlean_encoded",[.text function,.integer encoding,value]' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'name.toLower == "__sqlean_encoded"' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'CoreDecode.encodedIndexEntries_perm' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Runtime.Record.decodeRowCell_eq_reference' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'UTF-16 record translation, runtime encoding and BINARY comparison' "$audit_sources/Tests.lean"; then
  ok "actual UTF-16 cookie reaches record/catalog/index reads, scalar byte operations and BINARY sort; the original runtime record equality remains audited"
else
  fail "UTF-16 cookie propagation, record/index checks, expression binding, BINARY sorting or component proofs are disconnected"
fi

if rg -F -q 'observeRow := if header.textEncoding.val == 2 || header.textEncoding.val == 3 then' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   rg -F -q 'observeRow := if header.textEncoding.val == 2 || header.textEncoding.val == 3 then' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'CoreFileAdapter.reopenWithMetadata paths (some origins)' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreWALFileAdapter.reopenInSession session (some origins)' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreWALFileAdapter.reopenWithMetadata paths (some origins)' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreDecode.finishRowRead schema source cell.rowid record.fields fields' SQLeanite/Runtime/Record.lean &&
   test "$(rg -F -c 'finishRowRead schema source cell.rowid record.fields fields' "$audit_sources/SQLeanite/CoreDecode.lean")" = 2 &&
   rg -F -q '(ctx.lookupScalar row)' SQLeanite/CoreExpr.lean &&
   rg -F -q 'storedTexts := state.catalog.storedTexts' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.executeSelectEncoded state query' SQLeanite/CoreConnectionSQL.lean &&
   rg -F -q 'CoreOrder.encodedSpecification' SQLeanite/CoreWindow.lean &&
   rg -F -q 'if let some name := aliasName? expression then' SQLeanite/CoreCompoundTail.lean &&
   rg -F -q 'CoreCompoundTail.aliasName_encoded_input' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreExpr.lookupScalar_value' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreDecode.finishRowRead_unobserved' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.executeCompoundTail_encoding_preserves_state' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'UTF-16 native byte provenance and compound/window ordering' "$audit_sources/Tests.lean"; then
  ok "validated native TEXT bytes reach scalar evaluation in both file modes; compound/window ordering uses the connection encoding and retained logical/decode contracts"
else
  fail "native TEXT provenance, encoded compound/window execution or its component contracts are disconnected"
fi

if rg -F -q 'concatTyped encoding (← eval left) (← eval right)' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'expressionComparisonTypedWith operandAffinity op left right typedA typedB' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'sources.findSome?' SQLeanite/CoreExpr.lean &&
   rg -F -q 'original.column == column - source.offset' SQLeanite/CoreExpr.lean &&
   test "$(rg -F -c 'joinScalarPrepare context select originalRight state.catalog.storedTexts' "$audit_sources/SQLeanite/CoreSQL.lean")" = 2 &&
   rg -F -q 'storedTexts := state.catalog.storedTexts }, input.rows' SQLeanite/CoreWindow.lean &&
   rg -F -q 'extremeScalar := if replace then input.scalar else state.extremeScalar' SQLeanite/CoreAggregate.lean &&
   rg -F -q 'typedRows := result.map (·.typed)' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'selected.typedRows' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'materializeTypedRows state definitions result.rows typed' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'fromStorage value.textEncoding bytes == cell.bytes.toArray' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'SQLite.Scalar.concatTyped_utf8' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreAggregate.Result.scalar_value' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'UTF-16 native TEXT survives derived sources, JOIN, min/max and concatenation' "$audit_sources/Tests.lean"; then
  ok "native TEXT uses actual source slots and typed materialization/results through JOIN, windows, min/max, comparison and concatenation"
else
  fail "native typed TEXT representation or its source/value contracts are disconnected"
fi
