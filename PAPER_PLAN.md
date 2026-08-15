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

- Milestone 1's verified front end is complete for the supported Core grammar.
  `Lexer.lexCertified` constructs an inductive character-to-token trace.
  `CoreTokenGrammar.parseCertified` then cross-checks the total parser's AST
  with a separate AST-directed concrete grammar which shares no parser routine
  or parser state. It checks literal values, names, precedence trees,
  delimiters, joins, aliases, statement boundaries, and transaction commands;
  `parseCertified_agrees_parse` proves both front ends agree on the admitted
  AST. The live executor consumes only this certificate, and the text-level
  read/write/trace theorem families require it rather than a bare parse
  equation.
  `CoreSQLWriteText.TranslatedWrite` gives CREATE TABLE/INDEX, single-row
  INSERT/REPLACE, DELETE, UPDATE, and COMMIT a transparent,
  execution-independent translation relation; `executeStatement_eq_core`
  proves that it reaches the corresponding live Core command.
  `CoreSQLReadText.TranslatedRead` now does the same for simple single-table
  SELECT, COUNT, SUM, MIN/MAX, grouped aggregation, and two-table inner/left
  joins, and binary UNION ALL/UNION/INTERSECT/EXCEPT.  Each form reaches its
  independent bag/three-valued denotation from an actual SQL string.  The
  compound theorem retains both arm denotations, explicit empty-result width,
  and the duplicate-sensitive bag operator. Arbitrarily nested compound
  semantic chains remain open. Multi-row INSERT/REPLACE now
  translates to the exact live recursive Core command trace; every row keeps
  its command-specific logical effect, and the whole statement composes with
  returned-commit and repeated-recovery crash theorems. Transactional
  statement lists now thread translation through every possible successful
  intermediate state, retain explicit BEGIN/ROLLBACK snapshot effects, and
  compose the full parsed text with the same recovery theorems.
- Milestone 2's read constructors, bag/three-valued denotations, optimizer
  bridge, and cost-safe rewrite set are present and on both live file paths.
  Explicit parity witnesses now show that typed bijective renaming implements
  column permutation without changing multiplicity, and that cartesian product
  is exactly inner join with a constant SQL-TRUE predicate.
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
  to represented-new-table-tree theorem with no runtime validation.
  Constant-size localized writes now preserve the exact header and catalog
  facts directly when page zero is omitted; freelist-only page writes are
  therefore logically irrelevant on that path, while growth is forced through
  the explicit page-zero constructor. Overflow encodings now enter
  `TablesDecode` directly through `consOverflowEncoded`. The changed-index
  certificate now validates the complete combined table/index overlay source,
  rather than an index-only synthetic view. Page-directed insert/delete
  preparations carry an erased `OnStorage` witness identifying that overlay
  with the post-write image of the exact input buffer; the bounded-write check
  is over the delta only, not the database. Rebuilt indexes now carry an
  `OnStorage` witness too: every encoded page is either present in the exact
  physical delta or proved byte-for-byte equal to its validated old page.
  Thus both routed and rebuilt changed-index preparations are connected to the
  actual post-write storage image; complete database-certificate assembly
  remains the M3 integration obligation. The validating loader now exposes
  its exact catalog/table/index equations as
  `CoreDecode.PageSourceDecodes`, and a proved conversion produces
  `PageSourceRepresents` when the decoded database is a canonicalization
  fixed point. Canonicalization is proved idempotent, and the canonical
  catalog rebuilder is proved to return such a fixed point; this makes the
  remaining localized-preservation obligation explicit rather than hiding it
  behind a whole-decoder premise. The stronger
  `CoreLocalizedRepresentation.TableOnSource` invariant now records each
  table's identified tree pages, separately allocated overflow interval, and
  recursive decoder bounds. `TablesOnSource` aligns those witnesses with the
  catalog and database order. The multi-table encoder is proved to establish
  this invariant recursively, and `exists_tablesOnStorage_encodeBulk` ties
  the resulting base certificate to the exact live growable-storage image.
  `DatabaseOnSource` now combines that table layout with the exact catalog
  partition, physical index groups, and index metadata into the single
  proof-carrying state invariant from which `PageSourceRepresents` follows.
  The localized durability certificate is now genuinely `Prop`-valued (and
  therefore erased) and consumes this invariant directly; its former catalog
  data field has been moved under a propositional existential.
  The physical index-group encoder now establishes its decoder and metadata
  certificates together in one recursive theorem, including promoted entries
  and implicit TEXT-primary indexes, so their orders cannot diverge during
  final database-certificate assembly. The bulk-image base case is now closed:
  `exists_databaseOnSource_encodeBulk_in` assembles the catalog partition,
  table/overflow ownership, and physical/metadata index witnesses into one
  `DatabaseOnSource`; `exists_databaseOnStorage_encodeBulk` specializes that
  theorem to the exact array-backed page source used by the live writer.
  `exists_databaseOnStorage_padded` proves the same strong invariant after a
  shrinking commit appends its verified freelist, while
  `DatabaseOnSource.restate` raises the live allocator watermark beyond all
  physical pages without discarding any representation evidence.
  `CoreDurability.LocalizedRepresentation` now exposes their catalog/table/
  index equations and header framing as one erased certificate, and
  `executeText_localized_commit_crash_atomic` derives the public whole-byte
  crash theorem from it rather than assuming an opaque post-image decoder
  equation. An exact distinct page-zero write carrying an encoded SQLite
  header now proves the certificate's header field directly for the resulting
  growable image (`sqliteHeaderMatches_of_pageZeroWrite`), and its decoded
  catalog proves the catalog field without a whole-file validation pass
  (`catalogRead_of_pageZeroWrite`). Per-table decoder witnesses now compose
  structurally into the database-wide `mapM` table equation through
  `CoreLocalizedRepresentation.TablesDecode`; the changed table can use the
  local tree theorem while unchanged tables retain their prior witnesses.
  Exact physical-index certificates, including promoted interior entries, now
  fold through the executable canonical index validator table-by-table via
  `IndexesDecode` and `IndexGroupsDecode`. `IndexMetadataDecode` and
  `IndexMetadataGroups` independently reconstruct the exact canonical index
  list from the unchanged catalog run; their composition with the physical
  certificates now closes `indexesRead` without index re-encoding or a
  fallback database comparison. The public
  `localizedRepresentation_of_certificates` constructor consumes those exact
  table/index/metadata witnesses directly, so neither whole-database nor
  whole-index decoder equations remain as constructor assumptions. Exact
  rebuilt index and overflow runs lift from their numbered writes to the
  decoder's contiguous-page relation via
  `readsPagesFrom_applyWrites_of_covered`; `IndexesDecode.consEncoded` then
  turns an encoded changed index directly into the physical certificate.
  `localizedRepresentation_of_unchangedPageZero` composes these witnesses for
  the common constant-page-count path without a whole-file validation pass.
  The finite-delta source used for page-directed index validation is proved
  equal to growable-storage `applyWrites` for bounded live writes, while the
  fast array-backed old source is proved equal to its storage image without
  materializing all pages. `indexesDecode_consLocalized` consumes either live
  rebuilt or decoded-index certificate and makes the required source identity
  explicit.
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

The latest three-run 2,000-row medians after multi-row write refinement are
293/10/19/76/98/12 ms for bulk load, primary lookup, secondary lookup, bulk
UPDATE, bulk DELETE, and inner join respectively.  Every workload remains
within the frozen non-regression budget and at or below 5x C SQLite by median;
the proof additions add no runtime execution or validation pass.

## Milestone 1: verified SQL text front end

**This milestone is POPL'10 parity, not a reach goal.** Their RDBMS parses user
input with Ynot's packrat PEG parser, "implemented as a verified compiler": a
PEG grammar plus semantic actions yields an imperative computation whose result
"agrees with the specification" (paper section 4.2). A comparison that leaves
our parser unproved concedes a component they had.

Note the exact scope of their theorem, because it is also the right scope here:
it relates the *parser to a grammar*, not the grammar to SQL. Correctness
against an explicit, inspectable grammar is the standard they met and the
standard this milestone targets. Proving that the grammar is the true SQL
grammar remains a reach goal and is not needed for parity.

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

### What POPL'10 actually did

Recorded here so "parity" is checkable rather than rhetorical. Quotations and
definitions are from the paper (`usefulreading/papers/priorart-verified-rdbms-popl10.pdf`),
sections 3.4, 4.2 and 4.4. Their Coq development does not appear to be
publicly archived -- it predates the ACM artifact-evaluation era and the Ynot
repository (`ynot-harvard/ynot`) does not contain the RDBMS -- so the paper is
the citable ground truth.

Their algebra has a **six-operator basis**: selection, projection,
**permutation** (permutes a relation's columns), union, **difference**, and
cartesian product. They state this basis is "relationally complete, and equal
in expressive power to other relational formalisms, like relational calculus",
and note the choice is "somewhat arbitrary; for example, we could have chosen
to use join and recovered cartesian product as a degenerate case".

Their relations are **finite sets**:
`Definition Relation (I : Schema) := FSetInterface (Tuple I)`, with union,
difference and selection implemented by `FSetInterface`'s `union`, `difference`
and `filter`. There are no bags and no three-valued NULL logic.

Their optimizer runs as a distinct phase and implements **three**
transformations from a standard textbook: selection fusion
(`select P2 (select P1 Q)` to `select (P1 and P2) Q`), projection fusion
(composing the two permutations), and selection-projection re-ordering. They
report "several dozen algebraic identities that we have proven", any of which
could drive a transformation, "although not all will be beneficial". Their cost
model makes conservative assumptions -- selection and projection iterate every
tuple -- and they proved that **several** transformations are not
cost-increasing, not all of them.

Their parser is **verified**: Ynot's packrat PEG parser, "implemented as a
verified compiler", where a PEG grammar plus semantic actions yields an
imperative computation whose result "agrees with the specification". Note the
scope: the theorem relates the parser to a PEG grammar, not the grammar to SQL.

Three consequences for this plan:

1. **Permutation and cartesian product are parity items** and are not in the
   list below. Add them, or state explicitly that DISTINCT-preserving
   projection plus join subsumes them and prove the subsumption.
2. **INTERSECT is not one of their primitives** (it is derivable from
   difference), and UNION ALL cannot exist in set semantics. Our bag plus
   three-valued denotation is strictly harder than theirs and closer to real
   SQL, so on this axis the goal is not parity but a stated improvement. Do not
   describe it as matching them.
3. **A verified parser is parity, not a reach goal.** Milestone 1 is therefore
   required for the POPL'10 comparison, and the relative form -- correct
   against an explicit grammar rather than against SQL at large -- is the same
   standard they met. Our per-rewrite cost obligation below is stronger than
   their "several transformations".

### The parity work

Give every live Core read form one denotational interpretation over bags and
SQLite three-valued predicates.

Items marked **[parity]** are needed to claim POPL'10 coverage. Items marked
**[superset]** go beyond their algebra; keep them, and present them as an
improvement rather than as parity.

- projection, filtering, DISTINCT, ordering and LIMIT -- **[parity]** for
  projection and filtering; **[superset]** for ordering and LIMIT, which their
  set-based algebra cannot express at all;
- **column permutation** -- **[parity]**, one of their six primitives. This is
  discharged by `RelationalAlgebra.permute_eval` and
  `RelationalAlgebra.permute_symm_eval`: typed bijective `rename` preserves
  every tuple multiplicity and composing with the inverse is the identity.
- **cartesian product** -- **[parity]**, their sixth primitive. This is
  discharged by `RelationalAlgebra.innerJoin_true_eval`. State the direction
  honestly: they derive join from product, we identify product as the
  constant-true special case of our derived inner join.
- COUNT, SUM, MIN/MAX and grouped aggregation -- **[superset]**. Their algebra
  has no aggregation.
- inner and left-outer join -- **[parity]** via the product lemma above for the
  inner case; **[superset]** for left-outer, which is not derivable in their
  basis.
- UNION and EXCEPT -- **[parity]**. These are their `union` and `difference`.
- UNION ALL and INTERSECT -- **[superset]**. UNION ALL has no meaning in set
  semantics, and INTERSECT is not one of their primitives. Both are worth
  having: UNION ALL is the duplicate-preserving operator real SQL actually
  uses, and a primitive INTERSECT avoids the double-difference encoding. Keep
  them and say why.

The set-versus-bag difference is the important one and should be stated once,
prominently, rather than repeated per operator: POPL'10 denotes queries into
finite sets of tuples, so duplicates and NULL comparison never arise. Our
denotation is a bag with SQLite three-valued predicates. Every operator above
is therefore proved against a strictly harder and more SQL-faithful target than
theirs, which is a result in its own right and must not be described as
matching them.

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
- no validating full execution is added to justify an optimized result;
- every **[parity]** item above is discharged, including the permutation and
  product subsumption lemmas, so the POPL'10 claim rests on named theorems
  rather than on the two developments looking similar.

Our cost obligation is deliberately stronger than theirs: they proved *several*
transformations non-cost-increasing, we require a semantic and a cost theorem
for *every* live rewrite. Say so in the comparison; it is a cheap, defensible
improvement and it is already the exit gate above.

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

Taken from their OSDI'20 artifact, not from the standard YCSB distribution.
Their specs differ from stock YCSB in ways that matter, so copy theirs.

Source: <https://github.com/secure-foundations/veribetrkv-osdi2020> (commit
`053dd16`, "add source code"). A local read-only clone is kept outside this
repository next to the other third-party reference code, at
`../usefulreading/code/veribetrkv-osdi2020/`. It is deliberately not vendored
here: it is 96 MB and 5,925 files of someone else's Dafny, Docker and YCSB-C
source under their own licenses. The files that matter are

- `docker-hdd/src/veribetrkv-dynamic-frames/ycsb/*.spec` -- the seventeen
  workload specifications;
- `.../ycsb/YcsbMain.cpp` -- the driver, including the separate load/run timing
  and the HDR latency histograms;
- `.../ycsb/wrappers/ycsbwrappers.cpp` -- key selection
  (`NextSequenceKey`/`NextTransactionKey`);
- `.../Makefile`, target `build/VeribetrfsYcsb.data` -- which specs the paper
  actually runs;
- `.../vendor/YCSB-C/` -- the zipfian and latest generators to port;
- `run-experiments-in-docker-dynamic-frames.sh` -- the `--memory=2g` cap.

If reproducibility later requires the specs to be in-tree, vendor only the
`.spec` files with their upstream attribution; do not vendor the tree.

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

### Scale ramp, and why it is currently blocked

The ramp is 1k -> 100k -> **1M** -> 10M records, and 1M is a required reporting
point, not optional: it is the smallest size where the database (about 512 MB at
512 bytes per record) exceeds a typical page cache, which is the regime
VeriBetrKV's 2 GB cap is designed to create.

**It cannot be run today, and the reason is measured, not suspected.** Two costs
on the read path are linear in database size:

- opening a file decodes all of it, at roughly 33 ms/MB (30/51/93/181 ms at
  668 KB/1.3/2.7/5.4 MB);
- `lookupCertifiedIndexCandidates` re-compares the whole table per read, giving
  0.76/1.48/3.88/8.64 ms per read at 250/500/1000/2000 records.

Extrapolated to 1M records that is about 17 s to open and about 4 s *per read*,
so a 100-operation run is roughly 400 s. At 10M it is out of reach entirely.

So the scale ramp is gated on the read-path work below, and should be attempted
again as each item lands rather than treated as an independent task. Report the
largest configuration that completes, with the memory cap applied, and say
plainly where it stopped.

### Read-path cost structure (measured 2026-08-14)

Workload C, 1000 records, 512-byte field, 100 reads. C SQLite: 8 ms. Us: 651 ms.

| Component | Cost | Order |
|---|---:|---|
| Full-file decode on open | ~92 ms | O(database) |
| Index-certificate load, once | ~213 ms | O(database) |
| Certified lookup's table re-comparison | ~3.9 ms per read | **O(database) per read** |

The third is the important one. `lookupCertifiedIndexCandidates` requires
`stored.table.rows = table.rows`, a structural comparison of every row, on every
read. An indexed point lookup is therefore asymptotically no better than a scan:
**deleting the index makes the same 100 reads run 116 ms instead of 651 ms.**

This is the plan's own "proof debt paid as runtime cost" pattern in its purest
form -- the cached certificate cannot prove it still matches the live table, so
it re-verifies by brute force. Fixing it is a proof task, not an optimisation:
the check must become local (validate the candidate index entry and the fetched
row) rather than global, so it stays provable without trusting IO state.

A second, smaller defect in the same path: `CoreFileEngine.lean:164` caches with
`if retained.isEmpty then <load>`, so a legitimately empty certificate list
never caches and the whole file is re-read *per query*. That needs a loaded flag.

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
- **General parser correctness beyond the supported grammar.** Careful with
  this one: parser correctness *against an explicit grammar* is milestone 1 and
  is POPL'10 parity, because their PEG parser is verified. Only the stronger
  claim -- that the grammar itself is SQL's real grammar, over the unbounded
  surface -- is reach. Do not cite this bullet as grounds for leaving the
  front end unproved.
- `WITHOUT ROWID` and exotic file-format variants.

## Explicit non-goals

- all SQLite syntax, pragmas, extensions, or file-format variants;
- proving Linux, a filesystem implementation, storage firmware, or hardware;
- replacing the fail-closed foreign-file validation boundary with unchecked
  trust;
- weakening proof hygiene to obtain performance;
- broadening the legacy interpreter and presenting its tests as verification.
