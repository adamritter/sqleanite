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
  proves that it reaches the corresponding live Core command. An independent
  token grammar with lexer/parser correctness, multi-row INSERT, and statement
  list traces remain open.
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
  parser equation and proved translation relation. Full statement-list/parser
  parity and construction of the localized database representation premise
  still depend on milestones 1 and 3; those links are not hidden as trusted
  assumptions.

The latest three-run 2,000-row medians after the table accounting proof are
296/9/18/75/98/11 ms for bulk load, primary lookup, secondary lookup, bulk
UPDATE, bulk DELETE, and inner join respectively.  These are within 1.4% of
the frozen Lean baseline in the worst case; UPDATE and DELETE improved by
2.6% and 3.0%.

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
- Keep `README.md`, `docs/TRUST.md`, `docs/ARCHITECTURE.md`, and benchmark
  documents synchronized with exactly what the two headline theorems say.

Exit gate: `scripts/reproduce-all.sh` rebuilds the artifact from a clean tree
and produces the theorem, test, mutation, interoperability, crash, proof-time,
and performance tables used by the paper.

## Explicit non-goals

- all SQLite syntax, pragmas, extensions, or file-format variants;
- proving Linux, a filesystem implementation, storage firmware, or hardware;
- replacing the fail-closed foreign-file validation boundary with unchecked
  trust;
- weakening proof hygiene to obtain performance;
- broadening the legacy interpreter and presenting its tests as verification.
