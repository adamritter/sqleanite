# POPL'10 parity plus FSCQ durability plan

This plan targets one compositional result rather than a larger collection of
disconnected verified components.  The comparison points are Malecha et al.'s
verified relational database (POPL 2010) and FSCQ's crash specifications
(SOSP 2015).  SQLeanite keeps its distinguishing constraint: the implementation
reads and writes a bounded, documented subset of the real SQLite format.

The target is not all of SQLite or an unconditional theorem about Linux and
storage hardware.  Unsupported SQL must fail closed, and the final durability
claim is conditional on the explicit VFS contract in `docs/TRUST.md`.

## Baseline and non-regression policy

The starting point, measured on 2026-08-14, is:

- `lake build` succeeds;
- all 149 executable tests pass;
- the verification audit reports seven allowlisted host bindings and no
  `sorry`, project `axiom`, `native_decide`, `unsafe`, or project-local
  `partial def`;
- every live-path check passes;
- at 2,000 rows, the twelve public workloads are 1.2--5.0x C SQLite.

Every implementation milestone must keep the build, verification audit, and
live-path audit green.  Every proof or live-path milestone must run the 149
tests before commit.  The workload benchmark is run after changes that can
affect parsing, planning, query execution, encoding, commit, or recovery, and
at least once per milestone.

Performance gates:

1. no individual public workload may regress by more than 10% in three-run
   median without a recorded explanation;
2. no workload may cross above 5x C SQLite;
3. parsing and proof evidence must not add a second runtime execution or
   decode/compare pass;
4. prefer proof-carrying inputs and refinement lemmas over validating a result
   after it has been computed;
5. a regression accepted temporarily must have a named deletion condition and
   may not survive the milestone that introduced it.

Gates 1 and 2 are stated over the twelve public workloads. The YCSB-style suite
added in milestone 6a is reported, not gated, until it has a recorded baseline;
its 3x target is a reach goal, not an exit condition.

## Final claims

### Read theorem

For every text in the explicitly supported SQL grammar, parsing and executing
the text returns the result of the denotational bag/three-valued semantics and
does not change the logical database for read-only statements.

### Durable write theorem

For every supported write text that successfully executes from an encodable
old database to a new database, every modeled crash outcome of the concrete
rollback-journal commit and any finite number of recovery restarts decodes to
the old database or the new database.  If commit returns, recovery decodes to
the new database.

In schematic form:

```text
SupportedText text command
execute old command = ok new
encode old = oldBytes
commitTrace oldBytes (delta old new) = trace
------------------------------------------------------------
decode (recover (crash trace outcome)) = some old
  or
decode (recover (crash trace outcome)) = some new
```

The executable syscall layer must be shown to implement the same ordered
request trace under `SyscallVFS.Contract`; the contract itself remains in the
documented TCB.

## Milestone 0: freeze the evidence floor (complete)

- Keep a machine-readable benchmark baseline and a three-run median runner.
- Add a fast regression mode suitable for every semantic/storage commit.
- Make the verification and live-path audits check the final theorem names as
  they land.

Exit gate: one command reports build, proof hygiene, live-path status, tests,
and performance deltas against this baseline.

The gate is `scripts/check-paper-floor.sh`; full three-run medians use
`scripts/run-benchmark-regression.sh`.

## Progress snapshot (2026-08-14)

- Milestone 1 is partial.  The live total parser is connected to an explicit
  AST grammar and successful execution exposes its parse equation.
  `CoreSQLWriteText.TranslatedWrite` gives CREATE TABLE/INDEX, single-row
  INSERT/REPLACE, DELETE, UPDATE, and COMMIT a transparent,
  execution-independent translation relation; `executeStatement_eq_core`
  proves that it reaches the corresponding live Core command.
  `CoreSQLReadText.TranslatedRead` now does the same for simple single-table
  SELECT, COUNT, SUM, MIN/MAX, grouped aggregation, and two-table inner/left
  joins, and binary UNION ALL/UNION/INTERSECT/EXCEPT.  Each form reaches its
  independent bag/three-valued denotation from an actual SQL string.  The
  compound theorem retains both arm denotations, explicit empty-result width,
  and the duplicate-sensitive bag operator.  An independent token grammar
  with lexer/parser correctness, arbitrarily nested compound chains,
  multi-row INSERT, and statement-list traces remain open.
- Milestone 2's read constructors, bag/three-valued denotations, optimizer
  bridge, and cost-safe rewrite set are present and on both live file paths.
- Milestone 3's seven bulk command-to-byte theorems are complete.  The
  localized proof now has a component-wise representation invariant, exact
  storage-image read-after-write lemmas, a recursive validating-open
  refinement, and direct table-decoder refinement from mixed changed/unchanged
  pages.  A byte-relevant physical page descriptor records derived SQLite
  separators; its changed-page encoder accounts for every complete post-state
  tree page, and the live cached selector is proved equal to that specification.
  Root-to-leaf point writes now have both directions: selected pages are exact
  post-state bytes, and every omitted post-state page is byte-identical to a
  complete pre-state page.  This accounting theorem is composed across point
  insert/replace/delete, split/merge, bulk replace/retain, `replaceBetween?`,
  table alignment, and the live `updateState?` delta builder.  The converse is
  also composed: every emitted write comes from an exact complete post-tree
  page, and active post-tree page identities are unique.  These facts now
  yield `pageSourceContains_updateStateTree`, a direct represented-old-image
  to represented-new-table-tree theorem with no runtime validation. Catalog,
  overflow, freelist, and changed-index components must still be composed into
  the complete localized database representation witness.
- Milestone 4's growable page-level rollback protocol, concrete journal codec,
  returned-commit result, finite recovery-crash trace, and conditional syscall
  contract are present.  Crash atomicity now lifts over an arbitrary exact
  page-write list, so it does not require the bulk encoder.
- Milestone 5 has the parsed-command theorem
  `CoreEndToEnd.executeCommand_commit_crash_atomic` retains the exact logical
  effect of all seven persisted commands and composes it with arbitrary-delta
  recovery. `CoreSQLWriteText.executeText_commit_crash_atomic` now begins at an
  actual SQL `String` for one supported persisted statement and reaches
  concrete recovery bytes. Its transparent support witness contains the
  parser equation and proved translation relation.
  The `CoreSQLReadText.executeText_*_refines` family likewise begins at an
  actual SQL string, proves reads leave the state unchanged, and reaches the
  independent bag denotation for simple queries, scalar/grouped aggregates,
  joins, and binary compound reads. Arbitrarily nested compounds,
  statement-list/parser parity, and construction of the localized database
  representation premise still depend on milestones 1 and 3; those links are
  not hidden as trusted assumptions.

The latest three-run 2,000-row medians after the SQL-text read refinements are
294/9/19/76/100/11 ms for bulk load, primary lookup, secondary lookup, bulk
UPDATE, bulk DELETE, and inner join respectively.  Every workload remains
within the frozen non-regression budget; the proof-only additions add no
runtime execution or validation pass.

## Milestone 1: verified SQL text front end

Define `CoreSQL.SupportedText text statements` as a transparent relation for
the lexical and grammatical subset accepted by the verified Core.  Separate
three concerns that are currently combined in `CoreSQL.execute`:

1. lexing/parsing text into the existing syntax AST;
2. translating the AST, in a database context, into Core commands or query
   plans;
3. executing those commands.

Prove:

- tokenization soundness for every token used by the supported grammar;
- precedence and delimiter correctness for supported literal predicates;
- statement-list and transaction-boundary correctness;
- translation correctness for CREATE TABLE/INDEX, INSERT/REPLACE,
  UPDATE/DELETE, SELECT, BEGIN/COMMIT/ROLLBACK;
- rejection leaves the input Core state unchanged;
- successful `CoreSQL.execute` is equal to executing the translated command
  sequence.

The live executable must call the proved front end.  The broad legacy parser
may remain as a test fixture, but may not be a trusted shortcut on the Core
path.

Exit gate: a theorem beginning with supported SQL `String`, not a pre-parsed
`Statement`, reaches the existing `Core.execute_*_exact` theorems.

## Milestone 2: POPL'10 semantic and optimizer parity

Give every live Core read form one denotational interpretation over bags and
SQLite three-valued predicates:

- projection, filtering, DISTINCT, ordering and LIMIT;
- COUNT, SUM, MIN/MAX and grouped aggregation;
- inner and left-outer join;
- UNION ALL, UNION, INTERSECT and EXCEPT.

Prove that each live executor result refines this interpretation.  Existing
`QuerySemantics`, `RelationalAlgebra`, `KRelation`, `CoreJoin`, and
`CoreOptimizerBridge` results should be composed rather than copied.

Add a small, executable cost semantics.  Its purpose is not to predict wall
clock time; it counts logical row visits, comparisons, and materializations.
For every live optimizer rewrite, prove result preservation and either cost
non-increase or record the precise precondition under which the planner may
select it.  Index substitution must carry its existing exactness certificate
and a strictly smaller scan-bound certificate when selected.

Exit gates:

- every live read constructor has an execute-to-denotation theorem;
- every live optimizer transformation has semantic and cost theorems;
- the optimizer bridge remains on both rollback-journal and WAL paths;
- no validating full execution is added to justify an optimized result.

## Milestone 3: logical writes to SQLite bytes

Compose the seven existing execute-level write refinements with
`CorePageCodec.decode_encodeBulk` and the localized page-state refinement.
State frame conditions explicitly: unrelated tables, indexes, catalog entries,
and unchanged pages remain unchanged.

Prove two layers:

1. bulk encoding: decoding the bytes for the post-state yields exactly the
   post-state;
2. localized encoding: applying the certified page delta to a represented old
   image yields an image representing exactly the post-state.

Cover CREATE TABLE, CREATE INDEX, INSERT, REPLACE, UPDATE, DELETE, and COMMIT.
The localized theorem is the live performance theorem; bulk re-encoding is
only the construction/base case.

Exit gate: parsed write command to exact post-state SQLite bytes is one theorem
chain, and point/bulk mutations still meet the public performance budget.

## Milestone 4: FSCQ-style concrete rollback durability

Refine the live journal implementation into the existing growable-storage
protocol:

- concrete journal bytes decode to exactly the pre-images for the page delta;
- the live request order is journal write, journal sync, main writes, main
  sync, journal unlink, and parent-directory sync where required;
- crashes may retain any allowed subset/permutation of unsynced operations;
- recovery copies only authenticated pre-images and is idempotent;
- crashes during recovery, including after any copied page, preserve the same
  old-or-new result after restart;
- file growth and shrink restore both page contents and logical length.

Connect `CoreFileAdapter`, `PhysicalJournalCodec`,
`PhysicalJournalRecovery`, `GrowableStorage`, `POSIXVFS`, and `SyscallVFS`
with refinement structures.  Do not replace the live code with a proof-only
protocol.

Torn-write scope must be explicit.  Either prove the journal framing/checksum
protocol rejects every modeled torn sector and lift atomicity to
`TornStorage`, or state atomic journal-record writes as a VFS premise and make
the exact sector/alignment requirement visible in the theorem and TCB.

Exit gates:

- the old-or-new theorem is over concrete SQLite main-file and journal bytes;
- it quantifies over every commit checkpoint and repeated recovery crashes;
- successful returned commit implies the new decoded database;
- the syscall interpreter has a conditional refinement theorem to that trace;
- crash injection and the missing-sync mutation experiment agree with the
  theorem boundaries.

## Milestone 5: end-to-end composition

Compose milestones 1--4 into two headline theorems:

- `executeText_read_refines`: supported SQL text to denotational result;
- `executeText_commit_crash_atomic`: supported SQL write text to old-or-new
  recovered SQLite bytes.

Register both in `ProofAxioms.lean` and require them in
`scripts/live-path-check.sh`.  Their assumptions must mention only supported
syntax/data bounds, initial representation validity, modeled crash outcome,
and the explicit VFS contract.  Intermediate equalities that the repository
already proves must not be repeated as new assumptions.

Exit gate: deleting or bypassing the parser translation, live executor,
localized encoder, journal codec, recovery function, or syscall trace breaks a
build or live-path assertion for the headline theorem.

## Milestone 6: paper artifact

- Add generated theorem/TCB/LOC manifests and proof-latency measurements.
- Run differential tests in both interoperability directions.
- Run crash injection at every exposed operation boundary.
- Expand the matched Lean/C mutation corpus around parser, optimizer, B+ tree,
  journal ordering, recovery, and codec faults.
- Report three-run performance medians and scaling curves, including proof
  changes that removed runtime validation.
- Run the YCSB-style suite below and report it beside the twelve public
  workloads.
- Keep `README.md`, `docs/TRUST.md`, `docs/ARCHITECTURE.md`, and benchmark
  documents synchronized with exactly what the two headline theorems say.

Exit gate: `scripts/reproduce-all.sh` rebuilds the artifact from a clean tree
and produces the theorem, test, mutation, interoperability, crash, proof-time,
and performance tables used by the paper.

## Milestone 6a: YCSB-style evaluation

The twelve public workloads are more realistic than YCSB but are ours, so a
reviewer cannot place them. VeriBetrKV (OSDI 2020) reports YCSB against RocksDB
and BerkeleyDB, and that is the recognized yardstick a systems reviewer will
look for. Adding it costs no proof work and makes the performance claim
comparable to published numbers rather than self-defined.

Note on provenance: YCSB is VeriBetrKV's evaluation, not FSCQ's. FSCQ evaluated
with Unix application benchmarks (an xv6 source build, file create/delete
microbenchmarks, and a mail-server workload) against ext4 and xv6, reporting
roughly 2x ext4. Those are a filesystem-shaped comparison and do not transfer
to a database. FSCQ parity is therefore about the *durability theorem*
(milestone 4), and YCSB is about *performance comparability*. They are separate
goals and the plan should not conflate them.

### The exact configuration VeriBetrKV used

Taken from their OSDI'20 artifact
(`secure-foundations/veribetrkv-osdi2020`,
`src/veribetrkv-dynamic-frames/ycsb/*.spec`), not from the standard YCSB
distribution. Their specs differ from stock YCSB in ways that matter, so copy
theirs:

| Spec | Name | read | update | scan | insert | RMW | distribution |
|---|---|---:|---:|---:|---:|---:|---|
| `workloada-onefield` | A | 0.5 | 0.5 | 0 | 0 | -- | zipfian |
| `workloadb-onefield` | B | 0.95 | 0.05 | 0 | 0 | -- | zipfian |
| `workloadc-onefield` | C | 1.0 | 0 | 0 | 0 | -- | zipfian |
| `workloadd-onefield` | D | 0.95 | 0 | 0 | 0.05 | -- | **latest** |
| `workloadf-onefield` | F | 0.5 | 0 | 0 | 0 | 0.5 | zipfian |
| `workloadc-uniform` | Cuniform | 1.0 | 0 | 0 | 0 | -- | **uniform** |
| `workloade-onefield` | E | 0 | 0 | 0.95 | 0.05 | -- | zipfian, `maxscanlength=100`, `scanlengthdistribution=uniform` |

All of them: `recordcount=10000000`, `operationcount=10000`,
`readallfields=true`, `writeallfields=true`, `fieldcount=1`,
`fieldlength=512`. No `syncinterval` on A--F.

Four consequences that a stock-YCSB reading would get wrong:

1. **One 512-byte field, not ten 100-byte fields.** Hence the `-onefield`
   filenames; their driver asserts `values->size() == 1`. The record is ~512 B,
   not the stock ~1 KB.
2. **`operationcount` is only 10,000 against `recordcount` 10,000,000.** The
   load phase dominates; the run phase is a short, cache-hostile probe.
3. **The dataset is deliberately larger than RAM.** Their harness runs the
   container with `--memory=2g` while 10M x 512 B is roughly 5 GB. Every A--F
   number is therefore an out-of-cache, I/O-bound measurement. Running these
   in-cache would produce numbers that are not comparable to theirs.
4. **E and the `writes`/`wka-*` specs exist but are not in the paper's data
   target.** The Makefile's `build/VeribetrfsYcsb.data` runs exactly:
   A, A, B, C, D, F, Cuniform -- A twice, the first as warm-up. Report the same
   set; E is optional and must be labelled as an addition if included.

They also ship `workload{a,b,c,d,e,f}-small.spec` with
`recordcount=100, operationcount=10`. Use those for CI.

Separately from A--F, the insertion microbenchmark their abstract leads with
(24x BerkeleyDB, 8x slower than RocksDB) is the **load phase** itself, timed
independently -- their driver records `load_duration_ms` and `run_duration_ms`
separately, with HDR latency histograms and CCDF percentiles per operation
type. Matching them means reporting load and run separately, and reporting p50
and p99 latency rather than throughput alone.

### Schema and the two adaptations we must declare

YCSB keys are strings (`NextSequenceKey` on load, `NextTransactionKey` on
transactions), and values are one 512-byte field:

```sql
CREATE TABLE usertable (ycsb_key TEXT PRIMARY KEY, field0 TEXT);
```

Two honest deviations, to be stated in the paper rather than papered over:

- **A TEXT primary key is not `INTEGER PRIMARY KEY`.** In SQLite this is a
  rowid table with a unique index on `ycsb_key`, so the reads go through the
  secondary-index path, not the rowid path. That is the correct translation of
  a KV store's byte-string keys and it exercises the certified TEXT index, but
  it means our numbers are not directly comparable to our own workload 03. An
  integer-key variant may be reported alongside, labelled as a deviation.
- **We compare against C SQLite, they compared against RocksDB and
  BerkeleyDB.** The ratio is to a different baseline; the workload is the same.

### Scale risk

10M rows x 512 B is a ~5 GB database. The largest measured SQLeanite
configuration to date is 200k rows. Reaching the paper configuration may expose
tree, cache, or commit behaviour that no current test covers, and it is the one
part of this milestone that is not merely scripting. Plan for a staged ramp
(100 -> 100k -> 1M -> 10M), record where it stops if it stops, and report the
largest configuration that runs with the memory cap applied rather than quietly
shrinking the dataset.

### Why this fits the frozen surface

Every workload is expressible in the existing SQL subset: point reads by key,
single-row `UPDATE ... WHERE ycsb_key = ?`, `INSERT`, read-modify-write for F,
and `WHERE ycsb_key >= ? ORDER BY ycsb_key LIMIT n` for the E scans if E is
run. No aggregates, no subqueries, no multi-column indexes, no
column-to-column predicates. **The suite requires no new SQL surface** -- it is
purely an evaluation addition, which is why it belongs in milestone 6 and not
earlier.

### Runner

`scripts/run-ycsb-benchmark.sh`, matching the conventions of
`run-workload-benchmark.sh`: generate the operation trace once from a seeded
generator, replay the identical trace against SQLeanite and C SQLite, verify
outputs agree before reporting any timing, and emit three-run medians. The
`-small` record/operation counts are the CI default; the 10M configuration is
the artifact default. Apply the same memory cap they did when reporting
paper-scale numbers, and say so in the table caption.

The zipfian and latest generators must be deterministic and seeded so the trace
is reproducible and both engines provably see the same operations. Port the
distribution from their vendored `YCSB-C` (`vendor/YCSB-C`) rather than
reimplementing it, so the key-selection skew matches.

Exit gate: A, B, C, D, F and Cuniform report output-verified three-run medians
for both engines, with load and run phases timed separately and p50/p99
latencies recorded, and the trace generator is seeded and checked in.

## Reach goals

Not required for the paper; recorded so they are not silently dropped.

- **At most 3x C SQLite on the YCSB-style suite.** The mandatory gate remains
  5x on the twelve public workloads; this is a stronger target on the
  recognized benchmark. Context for why 3x is ambitious but worth naming:
  VeriBetrKV reports insertions about 8x slower than RocksDB and query
  performance "similar to unverified databases", and FSCQ reports about 2x
  ext4. A verified SQL engine within 3x of C SQLite on YCSB would be at the
  strong end of the published range for verified storage, and read-side
  workloads (B, C and Cuniform) are the plausible ones to reach it first.
  Workload A and the load phase are the ones expected to resist, for the same
  reason bulk DELETE does today. Because A--F are I/O-bound by construction at
  the paper scale, the ratio there is dominated by page-access count rather
  than by CPU work, which is a different optimisation target from the current
  write-path work -- do not assume progress on one transfers to the other.
- Everything already marked reach elsewhere: general parser correctness beyond
  the supported grammar, `WITHOUT ROWID`, and exotic file-format variants.

## Explicit non-goals

- all SQLite syntax, pragmas, extensions, or file-format variants;
- proving Linux, a filesystem implementation, storage firmware, or hardware;
- replacing the fail-closed foreign-file validation boundary with unchecked
  trust;
- weakening proof hygiene to obtain performance;
- broadening the legacy interpreter and presenting its tests as verification.
