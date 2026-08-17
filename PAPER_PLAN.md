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
added in milestone 6a is reported separately. Its mandatory read-side gate is
8x C SQLite at 1,000 records; the measured C and Cuniform ratios are now 4.0x
and 3.2x respectively. A uniform 3x target remains only a reach goal.

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

## Progress snapshot (2026-08-15)

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
  joins, and arbitrary recursively nested UNION ALL/UNION/INTERSECT/EXCEPT
  chains. Each form reaches its independent bag/three-valued denotation from
  an actual SQL string. `TranslatedCompoundRead` recursively retains every
  leaf denotation and empty-result width; `CompoundReadArmsRefine` proves each
  duplicate-sensitive operator against the independent optimized bag plan.
  Multi-row INSERT/REPLACE now
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
  actual post-write storage image. Complete database-certificate assembly is
  now closed by `DatabaseOnSource`, `OrdinaryLocalizedCommit`, and
  `PostImageCertificate`; the remaining M3 integration obligation is for each
  live adapter preparation to return that constructive certificate directly.
  The validating loader now exposes
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
  physical pages without discarding any representation evidence. The live
  table aligner now exposes an erased recursive alignment witness, and
  `TablesOnSource.updateStateCandidate`/`updateState` use it to retain every
  unchanged table certificate and replace exactly the one changed table. This
  discharges the database-order frame condition without comparing either the
  logical database or its encoded bytes. `TableOnSource.applyWritesOfUntouched`
  now transports each retained table across the actual growable-storage
  delta from page-range and noninterference facts, covering its separately
  allocated overflow interval as well as identified tree pages.
  The remaining encoder seam is now proved rather than assumed:
  `encodeChunkNodeWithOverflow_noOverflow` shows that the general durable
  encoder and the live localized encoder emit identical identified tree pages
  whenever the certified overflow run is empty. Both ordinary table deltas and
  changed-index candidates use that result to construct the complete changed
  `TableOnSource` directly over the actual post-write storage image.
  Prepared changed-index deltas now retain the exact decoded catalog entry
  together with proofs of its table, root-page, and canonical SQL metadata;
  `localizedLastIndexDelta_cons` installs either routed or rebuilt index bytes
  into the physical catalog run without permitting the certificate to be
  attached to an unrelated entry.
  The successful ordinary delta alignment now proves, for the complete table
  list, that schemas and declared indexes are unchanged.  Consequently the
  old `sqlite_master` metadata groups transport to the exact logical post-state
  as erased evidence; no catalog reparse or database comparison is required.
  Stable root identity is now proved through recursive deletion repair,
  root shrink, insertion splits, and fresh-page recycling. This supplies the
  algorithmic basis for preserving table root-page catalog entries when page
  zero is omitted from a localized data commit.
  That basis is now composed through the live table aligner:
  `updateState?_catalogEntries` proves the full table catalog run unchanged,
  and `DatabaseOnSource.updateState` assembles the catalog, changed table,
  retained tables, and transported metadata into the post-state invariant.
  Physical index ownership is now retained as the exact encoder run, including
  promoted entries, page reads, allocation bounds, and the logical index
  image. `TablePagesBeforeIndexRoots` is established by the bulk encoder.
  For an indexed ordinary delta, allocation monotonicity plus the successful
  equal-cardinality path proves the complete table page-ID list unchanged;
  exact write-to-page provenance then derives index noninterference without an
  arbitrary callback or a runtime scan. The indexless case is closed by
  `DatabaseOnSource.updateStateIndexless`: metadata proves that the catalog's
  index partition is empty, eliminating the physical-index callback rather
  than satisfying it vacuously. A mixed database which grows an unindexed
  table beside another table's index deliberately uses the proved bulk path;
  it is not admitted by a false global "all table pages precede indexes" rule.
  `OrdinaryLocalizedCommit` packages the actual delta, catalog/header frame,
  retained and changed table witnesses, and preservation mode.
  `PostImageCertificate` admits only that certificate, decomposed component
  evidence, canonical bulk encoding, verified freelist padding, or wide-page
  inline bulk encoding—never a bare post-image decoder equation. Those five
  constructors are why it is a discharged obligation and not an assumption. `PreparedBulkCommit` is now the exact pure
  object consumed by the live rollback writer; it retains its canonical versus
  padded branch and delta-write equation, and
  `PreparedBulkCommit.postImageCertificate` maps it to the public constructor
  with no extra runtime pass. The SQL-text and statement-trace crash theorems
  consume this constructive certificate. The ordinary live branch now returns
  one dependent preparation carrying its exact candidate, preimages, writes,
  distinctness, allocation, and preservation mode; the changed-index branches
  retain the same candidate plus exact table-preimage/table-write equations.
  Header/freelist augmentation is now a pure `planLocalizedWrites?` step, and
  `CommittedLocalizedDelta.trace_eq` ties the exact final list to the live
  journal/main-file request trace. The remaining localized integration is to
  construct the complete post-image table/index component certificate from
  those prepared values, rather than supplying its erased physical witnesses
  separately.
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
  joins, and arbitrary recursively nested compound reads. Statement-list/parser
  parity is complete, and localized database post-image construction is now
  exposed through `PostImageCertificate`
  rather than a bare decoder equality. Bulk commits already return the public
  certificate directly. Localized commits now mechanically bind the logical
  delta, table bytes, header/freelist plan, and concrete request trace; the
  remaining integration work is the final construction of the post-image
  component witness from that bound preparation.
  The ordinary indexed point-update chain now discharges its former raw
  `beforeInline`/`afterInline` overflow equations from the semantic
  `NodeRowsInline` invariant. `resolvePlans_pages_eq_nil_of_payload_le` proves
  that locally fitting SQLite record payloads allocate no overflow pages,
  `encodeChunkNodeWithOverflow_inline` lifts that fact through every persistent
  tree branch, and
  `executeText_committedLocalizedIndexedSingleOfRowsInline_crash_atomic`
  composes it with the exact returned commit. This covers the literal YCSB
  `TEXT PRIMARY KEY` layout and its 512-byte field without replacing it by an
  integer surrogate; genuinely large records retain the separately verified
  bulk/overflow path.
  The converse bridge, `encodeChunkNodeWithOverflow_of_inline`, now derives
  the complete overflow-aware encoding directly from the live localized
  tree-encoder equation. The strongest public theorem,
  `executeText_committedLocalizedIndexedSingleOfInlineTree_crash_atomic`,
  therefore has neither a caller-selected general encoding nor a raw
  no-overflow premise; it consumes the bytes the localized writer actually
  encoded.
  Full post-tree encodability is now preserved structurally as well.
  `exists_encodeChunkNode_of_pathAgrees` and
  `exists_encodeChunkNode_of_changed` combine the successfully encoded local
  descriptors with the already represented pre-tree; the result is threaded
  through every table mutation, recursive alignment, and `updateState?`.
  Consequently
  `executeText_committedLocalizedIndexedSingleOfInlineRows_crash_atomic`
  has no full-tree or general-encoder premise at all. Its remaining physical
  inputs are the old represented image/header, semantic inline row bounds,
  and the explicit VFS read/refinement facts.
  The exact benchmark specialization is
  `executeText_committedLocalizedIndexedSingleYCSB_crash_atomic`: it fixes the
  literal `usertable(ycsb_key TEXT PRIMARY KEY, field0 TEXT)` logical layout,
  proves `user` plus a 64-bit hash and one 512-byte value are inline, and
  derives the recursive pre/post tree invariants from those row shapes.

The latest three-run 2,000-row medians after multi-row write refinement are
293/10/19/76/98/12 ms for bulk load, primary lookup, secondary lookup, bulk
UPDATE, bulk DELETE, and inner join respectively.  Every workload remains
within the frozen non-regression budget and at or below 5x C SQLite by median;
the proof additions add no runtime execution or validation pass.

## Status 2026-08-16, independently measured

Measured after `8184bca` with a binary built from it. Build green, 151 tests,
audit clean. **Three of the four open items are genuinely closed; the fourth is
partly closed and what remains is now precisely located.** The section below
titled "Former blocking work" is accurate for items 1, 2 and 4 and premature for
item 3.

**Item 1, scale ceiling: CLOSED.** A **1,000,000-row** load completes — 194 s and
583 MB, against C SQLite's 3 s and 580 MB. 500,000 rows takes 92 s. The paper
target is met. Note the load ratio at scale is about 65x C, because our per-row
cost is flat at roughly 190 us while C's falls with size.

**Item 2, space amplification: CLOSED.** **1.01x** at 1M rows, 1.0x at both row
widths in the tier guard. Interior pages 13 against C's 8, from 43,326 against 47.

**Item 4, reads to 8x: MET on read-only workloads.** Workload C **3.6x**, Cuniform
3.9x, D 4.5x, C's p50 at 0.04 ms. 100 reads at 1M rows: 90 ms against C's 6 ms,
15x. Write-heavy A, B and F remain 9.9--13.3x.

**Item 3, write-open cost: IMPROVED 2.2x, NOT CLOSED.** Per-statement insert cost
was never the problem — ten inserts on one connection are 18--20 ms each and one
insert costs the same as ten. The cost is the *open*: an empty script costs the
same as a script containing an insert, so it is `CoreFileEngine.reopen`.

Two defects fixed (`buffer the general open and stop listifying whole databases`):

- `loadPageState` and `loadWidePageState` each converted the entire file to a
  `List UInt8`, one cons cell per byte of database, on every write open.
  `loadPageState` went from roughly 450 ms/MB to 3 ms.
- the general decoder read one page per syscall through `filePageSourceFor`;
  buffering the file once and slicing it cut that step from 3.4 s to about 1.3 s
  at 11 MB.

| database | one autocommit insert, before | after |
|---|---:|---:|
| 2 MB | 992 ms | **633 ms** |
| 11 MB | 5,394 ms | **2,499 ms** |

*Care needed here:* the buffered source must take its page size from the
validated header. Substituting the fixed-size `byteArrayPageSource` silently broke
the 1024-byte differential case; `scripts/live-path-check.sh` now asserts both the
positive and the negative form of that.

**Why it is still not closed, and one candidate fix that is now disproved.**

`loadOpenState`, the fast validated open, returns `none` in 5 ms on every file the
engine writes, for both TEXT and INTEGER primary keys, because
`CorePageLoad.open?` builds a 2-3 `PersistentPageTree` and cannot read the
high-fanout pages introduced for item 2. So each write open does two full passes:

| pass | cost at 11 MB |
|---|---:|
| construct `Core.Database` from bytes (general decoder) | ~1,243 ms |
| `loadWidePageState` validates the whole database again | ~950 ms |

**Disproved: a wide-format constructor does not help.** The obvious fix is to
teach the open path to construct from high-fanout pages, skipping the general
compatibility decoder. This was implemented and measured: the wide constructor is
reached (`hit=true`) and costs **1,243 ms**, i.e. exactly what the general decoder
cost. Building a `Core.Database` from bytes is inherently about 1.2 s at 11 MB on
either path, because every row is decoded into `Core.Row` with list-backed values.
The change was reverted rather than carried for no gain. **Do not retry this.**

What is actually left, in increasing difficulty:

1. **Fuse the two passes.** Construction already walks every page and decodes
   every row; the validation pass then does it again. Producing the wide state
   during construction would save roughly 38% of the open. The obstacle is a
   chicken-and-egg in `CoreWidePageLoad`: the chunk capacity is
   `chunkCapacityFor schema rows`, so it needs the rows, but the rows come from
   the decode whose grouping depends on the capacity. `loadNode` would have to
   return per-leaf rows so the node can be regrouped without re-reading pages,
   and `loadNodeCertified`'s `wellKeyed` obligation has to survive that. Still
   O(database).
2. **Make the write open lazy, which is the actual close.** The read path is
   already O(1) in database size — one read costs 11 ms at 2 MB and 12 ms at 11 MB
   — because `CoreLazyFileEngine` serves reads page-directed and never
   reconstructs anything. A write currently cannot do this because
   `Core.execute` needs a materialized `Core.Database` to produce the new table
   value. Closing item 3 means a page-directed write path: locate the leaf, mutate
   it, emit the proved delta, without building the database. That is an
   architecture addition of the same kind as `CoreLazyFileEngine`, plus the
   localized-commit proofs it must preserve, and it is the only route that removes
   the O(database) term.

*Acceptance, unchanged:* a single-row insert into a 1 MB and an 11 MB database cost
about the same. They are 3.9x apart today, down from 5.4x.

### The write open at 1M rows: 144 seconds for one insert

The single most important performance fact in this plan, measured on the 583 MB
1,000,000-row database:

| operation | cost |
|---|---:|
| one `SELECT` by primary key | **12 ms** |
| one autocommit `INSERT` | **143,671 ms** |

A four-order-of-magnitude gap on the same file. Reads are page-directed through
`CoreLazyFileEngine` and touch a handful of pages; a write reconstructs and
re-validates the entire database first. Every write workload at the paper scale is
therefore unusable per invocation, and this is what item 3 has to fix.

### Why a lazy write path is an architecture change, not a patch

The write side's correctness argument is founded on a *materialized* database, so
there is nowhere to put a lazy write without re-founding it:

- `CoreWidePageState.State` carries `database : Core.Database` together with
  `tables_eq : tables.map TableState.table = database.tables`;
- `CoreWidePageState.TableState` carries `table : Core.Table` and
  `represents : Store.rows tree = table.rows`;
- `CoreWidePageDelta.executeInsert?` computes the physical delta by *running*
  `Core.execute beforeState (.insert ..)` on that materialized database and
  proving the byte-level delta refines it.

So the physical write is correct *because* it agrees with the logical executor on a
fully decoded database. Removing the decode removes the reference the proof is
stated against. `Core.Table` stores every row in `rowTree`, so constructing one is
inherently O(rows) whichever loader is used — which is also why the wide-format
constructor measured identical to the general decoder.

Closing item 3 therefore needs a byte-level refinement that never mentions a
materialized `Core.Database`: "these pages denote some table T" and "after this
page write they denote T with this row inserted". That is the same shape as
milestone 3's localized representation, extended to stand alone rather than sit on
top of a decoded reference, and the durability theorems above it
(`executeText_commit_crash_atomic` in particular) have to be re-derived on the new
foundation.

*How to do it safely:* additively. Define the lazy representation and prove the
single-row insert refinement in a new module beside the existing path, leave every
current theorem untouched, and switch the executable over only once the new
refinement is proved end to end. Doing it in place would break the headline
durability theorem partway through, which is the project's central claim.

### Remaining work, in order

1. **Wide fast open.** The write open is now about 210 ms/MB, down from 490, but
   still O(database) because `CorePageLoad.open?` cannot read high-fanout pages and
   every write falls back to the general decoder. This is the last blocking
   performance item and the only one that changes the asymptotics.
2. **`REPLACE`/`UPDATE` growth at 512-byte rows is 2.4x per doubling**, at the
   guard threshold, so `scripts/run-scale-tiers.sh` **currently exits 1**. Narrow
   rows are 1.7x. Confirm whether this is a real superlinear term or threshold
   noise before acting.
3. **A, B and F p99 is about 113 ms** against p50s of 0.6--1.7 ms — the same shape
   as the tail item 3 explained, so probably the write open appearing once per
   connection.
4. **Trusted bindings rose from 7 to 9.** Two new allowlisted `opaque` host
   bindings entered the TCB during this work. The size of that surface is a
   headline property of the project, so each needs a recorded reason in
   `docs/TRUST.md`.

### On 10M rows: not yet, and 1M is not quite the intended regime either

VeriBetrKV's 10M-record configuration exists to exceed a 2 GB memory cap. Our 1M
database is 583 MB, so it fits in ordinary RAM and does not reproduce the
out-of-cache behaviour their numbers describe. Two cheaper and more faithful
options than 10M: run the 1M configuration under the same 2 GB cap, or raise the
record count until the database passes 2 GB, which is roughly 4M rows. Both are
better uses of machine time than 10M, and both want item 1 above fixed first,
because a multi-gigabyte database with a 490 ms/MB write open is not usable.

## Former blocking work (items 1, 2 and 4 closed 2026-08-16; item 3 partly)

All four measured items below are now closed. Their original diagnoses are kept
because they explain the architectural changes and provide falsifiable
regression targets. Current evidence is recorded under each acceptance test.

The implementation order mattered: 1, 2 and 3 blocked the paper independently,
while 4 was a performance target rather than a correctness gate.

### 1. Remove the per-row stack overflow. COMPLETE.

At diagnosis time, a single-table bulk load crashed with `Stack overflow detected. Aborting.`
somewhere between 130,000 and 160,000 rows. 130,000 rows of 512 bytes loads and
produces a 343 MB file; 160,000 aborts and leaves a zero-byte database. This is
row-count driven, not byte driven: 200,000 rows of 8-byte values also abort, and
the statement count is irrelevant here (203 statements is enough to trigger it),
so this is a separate limit from the statement-list recursion already fixed in
`bc13909`.

Some recursion on the commit or encode path is once-per-row and not tail
recursive. The pattern to reuse is the one this project already used for the
earlier 60k crash: keep the clean recursive definition for the proofs and swap in
a tail-recursive implementation with `@[csimp]`, as `orderedUpsertTR` does.

*Acceptance:* a 1,000,000-row single-table load completes and produces a readable
database, and `scripts/run-scale-tiers.sh` runs a tier at 200,000 rows without
aborting. **1,000,000 rows is the paper target** — it is the smallest size where
the data exceeds a typical page cache, which is the regime VeriBetrKV's 2 GB cap
creates. 10M is explicitly not required.

**Result (2026-08-16):** the exact 1,000,000-row, 512-byte-field YCSB-shaped
load completed in 220.76 s with exit status zero. C SQLite reports
`integrity_check=ok`, one million rows, and 512-byte min/max payloads. Peak RSS
was 44.2 GiB, which is an important remaining engineering limitation but no
longer a correctness or scale ceiling.

### 2. Give the physical page tree real fanout. COMPLETE.

At diagnosis time, files were 4.5x larger than C SQLite's for identical data: 343 MB against 75 MB at
130,000 rows of 512 bytes, for 63 MB of payload. A page-type census of both files
localizes it exactly:

| | leaf-table | interior-table | total pages |
|---|---:|---:|---:|
| SQLeanite | 43,333 (49%) | **43,326 (49%)** | 87,811 |
| C SQLite | 18,572 (96%) | **47 (0.2%)** | 19,301 |

**Half of our pages are interior nodes.** The physical page tree is a 2-3 tree, so
an interior node carries two or three child pointers and then occupies a whole
4096-byte page — roughly six useful bytes out of 4096. SQLite packs hundreds of
separators per interior page and needs 47 interior pages where we need 43,326.

**The decision has been made: give the page tree real fanout.** Do not merely map
several 2-3 levels onto one SQLite interior page in the encoder; raise the
branching factor of the physical tree itself so an interior page holds as many
separators as it has room for. This is the larger change and the larger payoff,
and it is the intended direction.

The second, smaller factor is that leaves hold one chunk while
`chunkCapacityFor` reserves half of each page for a second chunk the bulk builder
never emits — there are exactly 43,333 chunks and 43,333 leaf pages. Removing the
`/ 2` naively is unsafe, because `PersistentPageTree.Node.leaf` carries an
arbitrary entry list, so a two-chunk leaf is representable and would fail to
encode; that is the defect the byte-aware capacity was introduced to fix. Raising
fanout should subsume this, but if it does not, pack two chunks per leaf in the
bulk builder or split by bytes at emit time.

*Acceptance:* `scripts/run-scale-tiers.sh` reports amplification under 1.5x at
both 40-byte and 512-byte row widths, and `scripts/page-census.py` shows interior
pages as a low single-digit percentage of total pages rather than half. Run it on
our file and C SQLite's for the same data; today it reports 49% against 0%.

*Note:* amplification is not only a disk cost. Every extra page is a page written
on commit and traversed on read, so it is a constant factor on every timing
reported in this plan.

**Result (2026-08-16):** on the exact million-row artifact SQLeanite emits
625,565,696 bytes versus C SQLite's 622,739,456 bytes, or **1.0045x**. Table
interiors are 563 of 152,726 pages (0.37%); index interiors are 95 (0.06%). Both
files pass C SQLite's integrity check. The table and TEXT-index builders now
select real byte-bounded fanout, and page allocation skips SQLite's reserved
pending-byte page.

### 3. Make commit cost proportional to the change, not the database. COMPLETE.

This began as "explain workload D's p99 tail" and the explanation turned it into
the most consequential write-path item. The measurements below are the
pre-fix baseline.

D reports p50 1.08 ms and p99 334 ms. Timing every statement individually shows
all the slow ones are its INSERTs -- 346, 329, 326 ms -- against SELECTs at about
1 ms. D is 95% read and 5% insert, so seven inserts dominate its whole run.

**A single autocommit INSERT costs time proportional to the entire database:**

| table | our ms per insert | C SQLite |
|---|---:|---:|
| 500 rows, 1 MB | 84 | 12 |
| 1,000 rows, 2 MB | 180 | 12 |
| 2,000 rows, 5 MB | 303 | 12 |
| 4,000 rows, 10 MB | 790 | 12 |

Roughly 79 ms/MB, while C SQLite is flat at 12 ms. **The cost is per commit, not
per insert.** On a 5 MB table:

- one autocommit insert: **321 ms**
- ten autocommit inserts, so ten commits: **3,029 ms** — linear in commits
- the same ten inserts inside one `BEGIN`/`COMMIT`: **741 ms**

So commit does work proportional to the whole file however little changed, which
is precisely what the localized page-delta path was built to avoid. Note the
secondary effect too: an incremental insert into an existing 2,000-row table costs
about 44 ms once the commit is excluded, against 0.45 ms per row while bulk
loading the same table, so the incremental insert path is also carrying
size-dependent cost.

Worth checking first: whether the rollback journal is writing pre-images for the
whole file rather than the changed pages, and whether the commit re-encodes rather
than applying the proved delta.

**Why this blocks the 1M target.** At 79 ms/MB, one insert into a 1M-row database
of about 2.6 GB would take roughly 200 seconds. Workload D and any autocommit
write workload are unrunnable at the paper scale until this is fixed, independently
of items 1 and 2.

*Acceptance:* a single-row insert into a 1 MB and a 10 MB database costs about the
same, and workload D's p99 is within about 20x of its p50.

**Result (2026-08-16):** a single durable insert costs 18.324 ms in a 1.27 MB
database and 19.997 ms in a 10.03 MB database. Workload D at 2,000 rows reports
p50 0.88 ms and p99 17.52 ms (**19.9x**) with identical output to C SQLite. The
live path journals and verifies only its four-to-six changed pages. Recurrent
commits use a proved persistent-journal inode protocol, eliminating both
directory syncs; an invalidated proof-carrying read certificate is retired in
bounded storage rather than synchronously destructed on the first write.

### 4. Bring the YCSB read ratio to 8x. COMPLETE.

At diagnosis time, reads were at 16.8x C SQLite for workload C, down from 74x. **The target is 8x, not
3x** — the earlier 3x reach goal is superseded and should not drive design
decisions. Item 2 will contribute here for free, since fewer pages means fewer
page traversals.

*Acceptance:* workload C and Cuniform report 8x or better at 1,000 records.

**Result (2026-08-16):** three-run 1,000-record medians are **4.0x** for C and
**3.2x** for Cuniform; both have 0.04 ms p50 and 0.10 ms p99 in the timed
single-connection run.

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

### Space amplification: 4.5x C SQLite, and why (measured 2026-08-15)

Files are 4.4--6.0x larger than C SQLite's for identical data: at 130,000 rows of
512 bytes, 343 MB against C's 75 MB for 63 MB of payload. A page-type census of
the two files decomposes it exactly:

| | leaf-table | interior-table | total pages |
|---|---:|---:|---:|
| SQLeanite | 43,333 (49%) | **43,326 (49%)** | 87,811 |
| C SQLite | 18,572 (96%) | **47 (0.2%)** | 19,301 |

**Interior nodes are half of all pages.** The physical page tree is a 2-3 tree, so
an interior node carries two or three child pointers and then occupies a whole
4096-byte page -- roughly six useful bytes out of 4096. SQLite packs hundreds of
separators per interior page and needs 47 where we need 43,326. This is inherent
to using a 2-3 tree as the *physical* tree and is the larger of the two factors.
The verified 2-3 tree is what makes the branching proofs small, so raising fanout
is a real design decision, not a tuning constant: either the physical encoder maps
several 2-3 levels onto one SQLite interior page, or the page tree itself gains
fanout.

**Leaves hold one chunk where the budget reserves two.** There are exactly 43,333
chunks and 43,333 leaf pages, so the `/ 2` in `chunkCapacityFor`, which reserves
half of each page for a second chunk the bulk builder never emits, wastes half of
every leaf. Removing it naively is unsafe: `PersistentPageTree.Node.leaf` carries
an arbitrary entry list, so a two-chunk leaf is representable and would fail to
encode -- exactly the defect the byte-aware capacity was introduced to fix. The
safe forms are to pack two chunks per leaf in the bulk builder, or to split by
bytes at emit time instead of fixing chunk size up front. Both change tree shape
and therefore interact with the milestone 3 page-identity proofs.

*Why it matters for the paper beyond disk:* every extra page is a page to write on
commit and a page to traverse on read, so amplification is also a constant factor
on the timings reported elsewhere in this section.

*Acceptance:* `scripts/run-scale-tiers.sh` reports amplification under 1.5x at
both row widths. **The chosen fix is to give the physical page tree real fanout**
— see open-work item 2, which supersedes the options discussion above.

### Scale ceiling: two stack overflows near 100,000 rows (measured 2026-08-15)

**The ramp does not fail on performance. It crashes.** Superseding the earlier
"blocked on open cost and O(n) reads" framing -- both of those were fixed, and
what remains is two independent recursion-depth limits.

**Statements per invocation, between 50k and 60k.** 60,000 rows as 60,002
statements overflows; the same 60,000 rows as 62 multi-row statements loads fine
in 31 MB; 50,000 statements are fine. Value width is irrelevant. Running the same
60,003 statements through `--verified-file-timed`, one statement at a time on one
connection, completes -- so the recursion is over the statement list.
`CoreFileEngine.runStatements` recurses per statement and is not tail recursive
in `IO`, and `CoreLazyFileEngine.executeReadStatements?` has the same shape.

**Rows per table, between 100k and 130k.** 100,000 rows of 512 B loads in 103
statements and 265 MB; 130,000 fails; 200,000 rows of 8 B fails in 203
statements. Row-count driven, not byte driven, so something on the commit or
encode path recurses once per row.

**Consequence.** VeriBetrKV's configuration is 10,000,000 records, so the engine
is about two orders of magnitude short of the published comparison, and it is a
hard crash rather than a slow path. **Milestone 6a cannot report a 1M number,
let alone 10M, until both recursions are bounded.** The largest verified
configuration is 100,000 rows.

The project has fixed this class before: `orderedUpsertTR` with a `@[csimp]` swap
for the earlier 60k crash kept the clean definition for proofs while making the
executable tail recursive. That is the pattern to reuse for both sites.

*Acceptance:* a 1,000,000-row load completes, and `scripts/run-scale-tiers.sh`
extends to a tier above 200,000 rows without a crash. **1,000,000 rows is the
paper target; 10M is not required.** The statement-count half of this ceiling was
fixed in `bc13909` and verified at 200,000 statements; the per-row half remains
open as open-work item 1.

**Harness mitigation, already landed.** `scripts/ycsb-trace.py --insert-batch N`
emits multi-row INSERTs and clears the statement ceiling. It defaults to 1 so
nothing already measured changes, and a batched load was verified
output-identical to C. It cannot help with the per-row ceiling.

### Scale ramp, and why it is currently blocked

The ramp is 1k -> 100k -> **1M**, and 1M is the paper target rather than a
waypoint; 10M is explicitly not required. 1M is a required reporting point, not
optional: it is the smallest size where the database (about 512 MB at
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

### Read-path cost structure (measured 2026-08-15, supersedes the 2026-08-14 entry)

The earlier version of this section was wrong in two ways and is corrected here,
because it was pointing the work at the wrong things.

**Reads do not pay the full-file open.** One indexed read costs 10--11 ms flat
across an 8x file-size range (1.3 MB to 10.9 MB). An empty script over the same
files costs 48/90/175/344 ms, i.e. about 32 ms/MB. That linear cost is real but
lives on `CoreFileEngine.reopen`, which a read batch never takes:
`CoreLazyFileEngine` serves reads page-directed. Lazy open therefore matters for
cold non-read entry points, not for read throughput.

**The certified-lookup table re-comparison is gated, not the current cost.**
`certifiedLookupWorthAttempting` skips the O(table) check above 256 rows, and the
deletion condition is recorded on that function. It remains a correctness-shaped
cleanup, not a performance item.

**What reads actually cost: decoding every cell of every index page visited.**
Per-read cost falls as the index key gets wider, which is the signature:

| index key width | ms per read |
|---|---:|
| 8 bytes | 4.15 |
| 32 bytes | 3.29 |
| 128 bytes | 3.00 |

Wider keys mean *fewer entries per page* and therefore a *deeper* tree, yet reads
get faster. So the dominant term is per-page work proportional to entries per
page, not tree depth. `decodeIndexInteriorIOFrom` and `decodeIndexLeafIOFrom`
decode a page's entire cell array into `IndexEntry` values -- each allocating a
`Core.Value`, and for TEXT a `List UInt8` -- before the traversal chooses one
branch. A binary search inside the page would touch O(log cells) entries instead
of all of them.

Two contributing factors, both in the decode layer:

1. **Whole-page decode where a search would do.** This is the algorithmic half
   and the larger one.
2. **Pages arrive as `List UInt8`.** Every parse walks a linked list, and
   `preadPageSource` converts a 4096-byte page into 4096 cons cells per read.

Measured per-read totals for context: `CoreLazyFileEngine` batch 3.23 ms per read;
`CoreFileEngine` on one connection 1.92 ms p50, 2.05 ms p99. C SQLite is below its
own timer resolution, about 0.08 ms from batch measurements. So reads are roughly
25--40x C, and closing that is a decode-layer change, not caching.

**Two things already ruled out, recorded so they are not retried.** Caching table
schemas across a read batch changed 1000 reads from 3305 ms to 3225 ms -- inside
noise -- and was reverted. Caching page-zero geometry per connection was a 4%
win. Reading and decoding page zero is cheap; the cost is in the index pages.

### Write-path cost structure, and the one remaining quadratic

Bulk load was quadratic in row count. Root cause was `Table.upsert` rebuilding
the entire declared-key map on every insert from `table.rows`, which is a full
`toList` of the row tree. Mean microseconds per insert by decile of position in a
4,000-row load were 52, 84, 120, 162, 202, 248, 303, 359, 409 -- linear in rows
already present.

**Fixed for schemas with an explicit INTEGER PRIMARY KEY**, which is a common
SQLite shape but is not the literal YCSB schema used here.
`declaredKeyMapAfterUpsert` now takes the tree rather than a materialized row
list, so the `∅` branch never forces `storedRows`. Per insert is now flat at
35--39 microseconds, and load growth per doubling is 1.9x/2.0x/2.2x. At 16,000
rows the load went from 23.5 s to 6.6 s.

**Resolved 2026-08-15.** `REPLACE` and `UPDATE` on a hidden-rowid table were
quadratic -- 115 s and 1717x C SQLite at 2,000 rows -- and are now linear. The
byte-aware capacity is carried through mutations rather than recomputed, and
`scripts/run-scale-tiers.sh` reports 1.8x/1.9x growth per doubling for both
shapes and exits clean. At 2,000 rows UPDATE went from 115.1 s to 1.6 s. The
diagnosis below is kept because it explains the shape of the defect.

**The original finding: `REPLACE` and `UPDATE` on a
hidden-rowid table.** `Table.insertValues` routes hidden-rowid *inserts* to
`Table.upsertGeneratedFresh`, which was already incremental, so plain INSERT is
linear on both schema shapes -- a TEXT PRIMARY KEY table loads at
736/1449/3004/7144 ms for 2k/4k/8k/16k rows, growth 2.0x/2.1x/2.4x, essentially
the same as the explicit-key case. The surviving quadratic is reached through
`Table.upsert` on a table where `schema.hasHiddenRowid` is true, which is what
`REPLACE` and `UPDATE` do.

Measured, TEXT PRIMARY KEY table, load then REPLACE every row:

| rows | total | growth |
|---|---:|---:|
| 1,000 | 5.6 s | -- |
| 2,000 | 24.1 s | 4.3x |
| 4,000 | 108.4 s | 4.5x |

Quadrupling per doubling is textbook O(n^2), and 108 seconds for four thousand
replaces is far more severe than the bulk-load defect this replaced.

Making it incremental is **not** a local change, and this is the interesting part:
`upsert` may *replace* an existing row, and the replaced row's declared key can
differ from the new row's. A bare `declaredKeyMap.insert` would then leave the
old key still mapped to a row that no longer exists, breaking
`DeclaredKeyMapRepresents`. `Table.upsertGeneratedFresh` already does the
incremental insert correctly, but only because its `fresh` precondition rules the
replacement case out entirely.

A correct incremental version needs to erase the replaced row's declared key
before inserting the new one, which means looking up the row currently at
`row.treeKey` first. The shape is:

```lean
declaredKeyMap :=
  match tree.root.lookup row.treeKey with
  | some previous =>
      (declaredKeyMap.erase (previous.declaredKey schema)).insert
        (row.declaredKey schema) row
  | none => declaredKeyMap.insert (row.declaredKey schema) row
```

and the obligation is that this equals
`buildDeclaredKeyMap schema (orderedUpsert row rows)` whenever the map already
represents `rows` and the tree is well-keyed. That is a genuine proof about
`orderedUpsert` interacting with map erase/insert, not a rewrite, so it belongs
with the milestone 3 representation work rather than being done opportunistically.

*Acceptance:* a scale-tier run over `REPLACE` and `UPDATE` against a
TEXT-PRIMARY-KEY table grows at about 2x per doubling, matching the INSERT case.
`scripts/run-scale-tiers.sh` currently covers INSERT only and should be extended
with a mutation tier once this is fixed, so the guard would catch a regression.

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

- **The mandatory 8x YCSB read target is complete.** The 3x figure below is
  retained only as an aspirational reach goal and for the published-range
  context it records.
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
