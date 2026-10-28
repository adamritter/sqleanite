# Sourced by live-path-check.sh; retained in-progress predicate checks.
if rg -F -q 'evalInListTyped eval operandAffinity constant argument values negated applyLeftAffinity' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'evalBetweenTyped eval operandAffinity argument lower upper' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'branchesNativeTyped eval test operandAffinity base otherwise cases.toList' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'testTermsTypedWithConstants (ctx.lookupScalar row)' SQLeanite/CoreExpr.lean &&
   rg -F -q 'frame.context.lookupScalar frame.row qualifier name' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q '.literal (.text "stored")' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'SQLite.Scalar.membershipTyped collation affinity left typed' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'testEvaluatedTypedFuel (ctx.evalTyped row)' SQLeanite/CoreAggregate.lean &&
   rg -F -q '| .call "__sqlean_between" arguments false =>' SQLeanite/SQLite/TextEncoding.lean &&
   rg -F -q 'Scalar.builtinTyped_stored_representation' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Scalar.testBetweenTyped_argument_error' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Scalar.evalInListTyped_empty' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'UTF-16 predicates retain native bytes, correlated captures and BETWEEN error order' "$audit_sources/Tests.lean"; then
  ok "native CASE/IN/BETWEEN, FILTER/HAVING and actual captured bytes reach typed public execution while preserving branch/error order"
else
  fail "native predicate/capture representation, branch order or its contracts are disconnected"
fi
