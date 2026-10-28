# Repository guidance

SQLeanite is a Lean 4.35.0 verified database core. Keep changes scoped to this
repository; upstream SQLite is an optional external comparison dependency.

Keep every source file below 600 lines (including Lean fixtures and test drivers).
Split by responsibility and declaration boundary; do not compress code to fit.
Run `python3 scripts/check_module_boundaries.py` after moving code or imports.

Use `lake build` and `lake exe sqleanite_tests` for normal validation. Before
committing proof or live-path changes also run
`scripts/lean-verification-audit.sh` and `scripts/live-path-check.sh`.

Never introduce `sorry`, a project `axiom`, `native_decide`, `unsafe`, or a
project-local `partial def`. The only allowed `opaque` declarations are the
twelve named host bindings enforced by the audit. Put executable examples in
the appropriate `SQLeaniteTests/` module and register them in its test registry;
`Tests.lean` owns only process dispatch. Put reusable propositions and proofs
beside the definitions they describe. Register headline theorems in the
responsibility files imported by `SQLeanite/ProofAxioms.lean`.

Start with `docs/ARCHITECTURE.md` and `docs/module-layout.json` to locate a
declaration. Compatibility modules preserve existing imports; implementation
modules import the narrow responsibilities they use. Keep `CoreDecode`
independent of `CoreSQL` and `Engine`; shared index admission lives in
`CoreIndexPrepare`. Use `scripts/lean_sources.py` when an audit needs a logical
source spanning a compatibility module's explicitly imported files.

`Engine.lean` and `LegacyServerMain.lean` exist only for conformance testing.
The public executable must continue through `CoreRuntime` and the `Core` file
engines. Preserve this boundary and update the live-path audit when wiring new
proved code into execution.

