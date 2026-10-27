# Repository guidance

SQLeanite is a Lean 4.35.0 verified database core. Keep changes scoped to this
repository; upstream SQLite is an optional external comparison dependency.

Use `lake build` and `lake exe sqleanite_tests` for normal validation. Before
committing proof or live-path changes also run
`scripts/lean-verification-audit.sh` and `scripts/live-path-check.sh`.

Never introduce `sorry`, a project `axiom`, `native_decide`, `unsafe`, or a
project-local `partial def`. The only allowed `opaque` declarations are the
twelve named host bindings enforced by the audit. Put executable examples in
`Tests.lean`; put reusable propositions and proofs beside the definitions they
describe; register headline theorems in `SQLeanite/ProofAxioms.lean`.

`Engine.lean` and `LegacyServerMain.lean` exist only for conformance testing.
The public executable must continue through `CoreRuntime` and the `Core` file
engines. Preserve this boundary and update the live-path audit when wiring new
proved code into execution.

