# P1–P5 mutation benchmark: Lean proof arm

Registry commits: `5bec52b8ba` (P1–P4), `3267d85d7c` (P5)

Runner-fix commit: `f8fbd7b933`

Command: `LAKE_BIN=/home/ofirp/.elan/bin/lake scripts/run-lean-mutations.sh`

The registry was committed before execution. A preliminary runner invocation is
excluded: its logs contained only `lake: command not found`; the runner fix was
committed before the reported run, and no mutation was changed.

## Summary

| Metric | Result |
|---|---:|
| Pre-registered semantic mutations | 19 (21 today; see below) |
| Raw `lake build` failures | 19/19 (100%) |
| Bucket 1: definition rejected by proof-carrying type | 1 |
| Bucket 2: theorem false under mutation | 17 |
| Bucket 3: brittle proof / theorem remains repairable | 1 |
| Credited proof-time detections (buckets 1–2) | 18/19 (94.7%) at the time of this run; 21/21 raw detections today |
| Query executions before detection | 0 |
| Median mutation-to-detection time | 1,043 ms |
| Mean mutation-to-detection time | 2,716 ms |

The two P2 mutations alter the helper called by the live expression-index SELECT
path. Both were detected before executing a query, in 18.174 s and 18.261 s;
their higher latency is recompilation of the large live engine, not test time.
The P5 additions all failed in under 0.9 s because they touch the smaller pure
WAL/interleaving model.

## Manual classification

| Mutation | Bucket | Time (ms) | Defect→failure lines | Audit |
|---|---:|---:|---:|---|
| p1-fold-not-identity | 2 | 1,146 | 24 | `foldNot_eval` is false for TRUE/FALSE. |
| p1-pushdown-wrong-side | 2 | 1,046 | 11 | Left predicate cannot filter the right input. |
| p1-eliminate-left-projection | 2 | 1,045 | 8 | A joined row is not equal to its left projection. |
| p2-index-drop-first | 2 | 18,174 | 21 | Nonempty indexed output is not a permutation after `tail`. |
| p2-index-duplicate-row | 2 | 18,261 | 20 | Duplicated candidate violates exact row preservation. |
| p3-duplicate-replacement | 2 | 746 | 23 | Existing-key insertion is no longer duplicate-free; later sortedness is false. |
| p3-paginate-drops-key | 2 | 745 | 10 | `flattenPages (paginate xs) = xs` is false. The failing `change` is a symptom, not a brittle-only failure. |
| p3-split-duplicates-median | 2 | 744 | 4 | Multiplicity-aware split equality is false. |
| p3-merge-reverses-pages | 2 | 744 | 4 | Merge contents are reversed, so exact abstraction equality is false. |
| p3-reverse-child-directory | 1 | 644 | 0 | `Tree` requires the directory to enumerate pages in order; the constructor's proof field cannot be filled by `rfl`. |
| p4-journal-after-image | 2 | 1,043 | 29 | A modified old page plus a growth page recovers a hybrid: neither old nor fully new. |
| p4-wrong-original-size | 2 | 1,046 | 75 | Rollback truncates to the wrong count. |
| p4-recovery-no-truncate | 2 | 1,045 | 10 | A surviving growth write remains after rollback. |
| p4-main-before-journal-sync | 2 | 1,044 | 105 | Main writes may survive while the only journal copy is lost. |
| p4-commit-without-delete-sync | 3 | 1,045 | 132 | The existing proof script assumes no pending delete, but old-or-new remains provable: a surviving old journal legitimately yields old under the current theorem. |
| p5-admit-two-writers | 2 | 745 | 96 | The serializability theorem would have to equate an accepted two-writer `none` result with a serial `some` result; `lost_update_schedule_is_rejected` is also false. |
| p5-torn-reader-snapshot | 2 | 847 | 83 | A mixed old/new `Database` is neither legal serial observation, so the observation-relation equality is false. |
| p5-unlock-before-wal-sync | 2 | 745 | 6 | The reordered protocol is rejected at unlock with a pending frame and cannot equal the proved completed state. |
| p5-publish-before-sync | 2 | 744 | 24 | A staged frame changes `visible`, directly falsifying `WAL.pending_is_invisible`. |

Bucket 3 exposes a specification gap. `rollbackCommit_crash_atomic` permits old
or new at every checkpoint, including `committed`; it does not separately state
that a returned commit must recover new. Crediting this failure would inflate the
benchmark. The follow-up is a committed-phase durability theorem, after which
this same semantic mutation should become a genuine bucket-2 failure.

That follow-up was implemented after preserving this report:
`GrowableStorage.rollbackCommit_committed_recovers_new` and its concrete-codec
lifting require new-state recovery after commit returns. The initial 13/1/1
P1–P4 classification remains 13/1/1 for buckets 2/1/3 rather than being
retroactively improved; the four later preregistered P5 mutations are all
bucket 2.

## Scope and C comparison arm

The table above is the Lean proof arm. It demonstrates detection before runtime
for registered Lean implementation faults; it does not by itself establish a
wall-clock advantage over C SQLite.

The current C arm was preregistered in two committed batches and contains ten
source mutations across scalar/3VL semantics, affinity, index traversal and
deletion, and file truncation. `scripts/run-c-mutation-pilot.sh` compiled each
mutated CLI and ran its bounded witness, without invoking the expensive full
SQLite suite.

| Metric | Current result |
|---|---:|
| Preregistered C mutations | 10 |
| Mutants accepted by the C compiler | 10/10 |
| First-witness detections | 9/10 |
| Queries before each detection | 1 |
| Median compile-plus-witness time | 8,232 ms |

The complete per-mutation data and build logs are retained in
`c-results.tsv` and `c-logs/`. The C compiler caught none of these semantic
faults; every detection required execution. The Lean arm instead executes zero
queries before its credited proof failures. On this machine some Lean rebuilds
are slower than the C build plus witness, so the supported claim is detection
distance and quantified coverage, not uniformly lower wall-clock latency.

`c-p1-and-as-or` is retained as a **miss**, not quietly discarded. Its mutation
changes the live `OP_And` implementation, but its constant-only witness is
folded before that opcode executes. Strengthening the witness after seeing the
result would violate preregistration. This is the C analogue of the benchmark's
brittle-proof bucket: it exposes inadequate witness coverage and is not counted
as a detection.

Crash ordering is reported as a separate focused arm. Removing the journal sync
compiles and passes every non-crashing query. The test-only power-loss VFS in
`native/powerloss-vfs.c` buffers unsynced writes and persists seeded subsets at the
first main-file sync. Stock SQLite recovered old-or-new in 20/20 deterministic
rounds; the held-out `c-p4-skip-journal-sync` mutant recovered a partial commit
in 20/20. The matched Lean `p4-main-before-journal-sync` fault falsifies the
old-or-new recovery theorem before query execution. The VFS is unverified and
the sample covers one C durability mutation, so it is not folded into the
aggregate C-versus-Lean latency table.

A separate focused differential arm remains green:
`scripts/run-differential-smoke.sh` compares ten deterministic SQL programs
byte-for-byte against the system C CLI. This is bounded interoperability
evidence, not a substitute for either theorem coverage or the full SQLite suite.

## Live Core planner mutations

The two P2 mutations in the original registry target `Engine.lean`, the legacy
interpreter. Three were added against the planner that actually runs:

| Mutation | Detected? |
|---|---|
| `p2-core-planner-drops-first` — planner drops the first index candidate | yes, 948 ms |
| `p2-core-planner-wrong-column` — planner matches the wrong column | yes, 947 ms |
| `p2-core-planner-any-index` — planner accepts an index that does not cover the predicate | **no — withdrawn as invalid** |

### What the withdrawn mutation revealed

Removing the `column = index.column` guard does not break
`indexedCandidates_filter_eq_scan`, and it should not: the planner filters by the
*predicate's* column regardless of which index was chosen, so the result is
still correct. Pointing it at an unrelated index is a performance defect, not a
correctness one.

That is worth stating plainly, because it is evidence for a real limitation
rather than a proof gap: **`indexedCandidates` never consults the index.** The
`index` argument is decorative. The planner is proved sound and is genuinely on
the live path, but it filters the in-memory row list in O(n) and does not read
the persisted index B-tree, so it does not improve complexity over a scan.

Counting this mutation as "missed" would have implied the proofs are weak. They
are not; the implementation is. The encoder does write real multi-page index
B-trees that C SQLite searches with a covering index, so the gap is on the read
side only.
