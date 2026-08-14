# Pre-registered Lean mutation benchmark

This directory is the immutable input set for the P1–P4 proof arm. The registry
was committed before any patch was executed. Every mutation changes executable
behavior and names a concrete semantic defect; proof-script-only edits are not
admitted.

`scripts/run-lean-mutations.sh` applies each patch to a clean tracked worktree,
runs `lake build`, reverses the patch, and records detection latency. A failed
build is not automatically credited: `results.md` separately audits whether it
is a type error, a semantic proof failure, or a brittle-tactic false positive.

The benchmark does not run SQLite's large upstream suite. Its proof arm only
checks the Lean build. The C SQLite comparison is by bug class, not by identical
source patches, and remains a separate experiment.

`c-registry.tsv` pre-registers ten bounded C-source mutations across query,
index/B-tree, and storage behavior. `scripts/run-c-mutation-pilot.sh` compiles each
mutated SQLite CLI and runs only its deterministic witness; it does not run the
expensive full suite. See `results.md` for exclusions, missed crash-only faults,
and comparison limits.
