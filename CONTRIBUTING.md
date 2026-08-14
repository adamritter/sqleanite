# Contributing

Contributions are welcome, especially small changes with a clearly stated
invariant and an executable regression test.

Before opening a change, run:

```sh
lake build
lake exe sqleanite_tests
scripts/lean-verification-audit.sh
scripts/live-path-check.sh
```

Keep the verified core free of `sorry`, project axioms, `native_decide`,
`unsafe`, and opaque partial definitions. New host operations must be narrow,
named in the audit allowlist, specified by a Lean contract, and disclosed in
`docs/TRUST.md`. Do not count a closed computation or an `rfl` restatement as a
headline verification result.

State new theorems against the live `Core` types and add important ones to
`SQLeanite/ProofAxioms.lean`. If a proof is meant to justify removing a runtime
check or fallback, remove it in the same change and extend
`scripts/live-path-check.sh` so the connection cannot silently regress.

Benchmark changes against equivalent outputs, not timing alone. Avoid running
the expensive full upstream suite for every edit; the 149 Lean tests, focused
differential corpus, and audits are the ordinary development gate.

