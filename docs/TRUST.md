# SQLeanite trust boundary

This file records what SQLeanite currently proves, what it merely tests, and
what must be trusted. It is intentionally narrower than a claim that SQLite is
verified.

## Current architecture and claim

There is **one** verified core. `--verified-file` (rollback journal) and
`--verified-wal-file` (write-ahead log) are the only database entry points; the
fixed-schema stack and its `--mvp-*` flags were retired. Arbitrary schemas over
INTEGER / REAL / TEXT / BLOB / NULL are stored as real multi-page SQLite B-trees -- tables and
indexes both -- and files round-trip against the C implementation in both
directions.

BLOB is represented by exact proof-carrying bytes, mapped to SQLite's even
serial-type codes, and covered by the same generic
`decodeValueField_recordField` and whole-record round-trip theorems as INTEGER
and TEXT. Focused interop writes BLOB from Lean and checks it with C SQLite,
then writes BLOB from C and checks exact bytes in Lean. REAL is retained in the
Core as raw proof-bounded binary64 bits and round-trips through SQLite's serial
type 7 without a floating-point equality axiom. `Binary64.compareBits` orders
non-NaN bit patterns by sign/exponent/significand, and mixed INTEGER/REAL
comparison scales the integer significand with exact `Nat` powers of two;
positive and negative zero are proved equal. NaN SQL literals are rejected.
Parsing a decimal literal to `Float.toBits` and rendering with `Float.ofBits`
remain executable-edge operations in the TCB; the storage and comparison
theorems themselves never perform host floating arithmetic.

What is proved and what is not:

- **Proved:** three-valued optimizer rewrites; equality and range index
  candidates equal a full scan, and the live cost-aware planner may substitute
  them; paged-tree `toList` commutation;
  growable crash atomicity with page-level undo and truncation, including that
  a returned commit recovers the new state; WAL recovery for arbitrary schemas;
  single- and non-overlapping-writer serializability; canonical schema and
  index SQL round trips; and a strict whole-file theorem showing that decoding
  every image produced by the retained canonical Core codec returns the
  original database. The whole-file theorem is conditional only on the
  explicitly stated standard-library UTF-8 encode/decode law. The live
  recursive topology now has a compositional whole-image inverse:
  `decodeFromPageSource_encodeBulk` covers emitted page intervals and
  `decode_encodeBulk` covers the byte-file entry point. `encodeChecked` is now
  only a compatibility name for that proved encoder and performs no runtime
  decode/compare admission check. The exact raw primary-tree lookup covers
  arbitrary emitted tree height, both interior shapes, overflow and valid
  misses. `encodeBulk_generatedHeader` connects the live encoder to the
  persisted generated-image stamp used to admit a cold missing-key result.
  Generated INTEGER indexes additionally have an end-to-end promoted-key
  refinement: equality and range traversal over their emitted pages equals
  filtering the complete logical index, without reopening or linearly
  validating it.
- **Not proved:** cold raw-page pruning completeness for unstamped wider
  C-produced index nodes or mixed-storage-class indexes. After a validating
  reopen, wider INTEGER indexes have exact directed certificates and mixed
  indexes have exact but linear all-value certificates. Also not proved is
  that a particular kernel,
  filesystem, and device satisfy the explicit syscall/VFS refinement
  assumptions.

The legacy in-memory SQL interpreter (`Engine.lean`) still exists behind the
separate test-only `sqleanite_legacy_server` executable and is **not** part of
the verified core or the production `sqleanite` import graph.

## The one assumed law, and why it is a *checkable* assumption

`CoreDecode.UTF8Roundtrips : ∀ value : String, TextRoundtrips value` is the only
library-level law this project assumes rather than proves. It says Lean's own
UTF-8 encode/decode pair round-trips every string, and it exists because the
standard library exposes no theorem about its own implementation.

Its blast radius, counted rather than estimated: **47 hypothesis positions across
eight modules** — 44 theorem or definition parameters plus three
`PostImageCertificate` constructors. By module: `CoreDurability` 18,
`CoreWriteBytes` 8, `CorePageCodec` 6, `CoreWriteSemantics` 5,
`CoreWidePageInverse` 4, `CoreFreelistCodec` 3, `CoreDecode` 2,
`CoreLocalizedRepresentation` 1. Any theorem that lifts a byte-level catalog or
TEXT fact to *arbitrary* strings takes it; the storage and comparison theorems do
not, and never perform host UTF-8 operations.

The part worth stating, because it costs nothing and changes what kind of
assumption this is:

> `TextRoundtrips value` has a `Decidable` instance. The universal law could
> therefore be replaced by a **per-string check at the boundary** — over the
> finite set of identifiers and TEXT payloads a given database actually contains
> — turning an assumed law into a runtime-verified premise, with no change to any
> proof but the threading of a witness through those 47 positions.

That threading is deliberately not done here: it is mechanical, wide, and buys
nothing for a bounded claim that already discloses the law. But the distinction
matters and should be stated: this is a *disclosed and checkable* assumption, not
an irreducible one. It is not in the same class as trusting the kernel or the
device.

## `PostImageCertificate` is discharged, not assumed

A correction worth recording explicitly, because the shape invites the opposite
reading. `CoreDurability.PostImageCertificate` is **not** an assumed decoder
equation smuggled into the crash theorem. It is an inductive with five
constructive alternatives, and its docstring says the design rule out loud:
"There is deliberately no constructor accepting an opaque decoder equation."

| constructor | what it requires |
|---|---|
| `ordinary` | an `OrdinaryLocalizedCommit` built by the live writer |
| `components` | a `LocalizedRepresentation`: the exact catalog read, table decodes and index reconstruction |
| `bulk` | an actual encoder run, `encodeBulk database = some image`, plus image equivalence |
| `padded` | the same for a verified freelist-padded layout |
| `wideBulk` | the same for the wide inline encoder |

The live localized path uses `.components` and `.ordinary`, which `CoreDurability`
builds from the live writer's own prepared delta — no encoder is re-run and no
decoder equation is assumed. Only the three bulk-shaped constructors mention
`encodeBulk`, and each demands that the encoder *actually produced* the image
rather than positing a decode. Do not list this among the assumptions.

## What the durability claim is conditional on

Stated once, plainly, because a crash theorem is only as strong as the storage
model it quantifies over:

> Every crash-atomicity result in this project — `rollbackCommit_crash_atomic`,
> `rollbackCommit_committed_recovers_new`,
> `rollbackCommit_recovery_crash_trace_atomic`, the localized-commit family, and
> the SQL-text level `executeText_commit_crash_atomic` — is **conditional on
> `SyscallVFS.Contract`**, the refinement obligation for a concrete host adapter.
> No project axiom asserts that any particular kernel, filesystem or device
> satisfies that contract. Syscall behaviour, filesystem semantics, device write
> caches and directory durability therefore remain in the trusted computing base
> described above, and the crash fault-injection and power-loss experiments are
> evidence about a real system rather than instances of the theorem.

The comparison to FSCQ is about the *shape of that theorem* — quantifying over
every checkpoint and every modeled crash outcome, with recovery proved to be the
old or the new state and never an intermediate one. It is not a comparison of
evaluations: FSCQ is evaluated as a filesystem (xv6 build, mail server, versus
ext4), which does not transfer to a database's operation mix. Performance
comparability with a production engine is what YCSB and the workload benchmark
are for. The two should not be presented as one result.

## The page-local write path is proved but not deployed

`CoreLazyWrite.insertPlan_refines` proves that the plan the executable computes
for a single-row `INSERT` -- one located leaf, re-encoded, every other page
byte-identical -- denotes exactly `Core.orderedUpsert` of that row into the
table's decoded rows. It is sorry-free and audited.

It is **not on the shipped path**, and the claim must not be stated as if it
were. Three things separate the theorem from the default binary:

- the refinement is conditional on `WellFormedTree` (sound separators, disjoint
  sibling page sets, inline leaves, in-range page numbers), and nothing checks
  those premises at open time;
- so `Main.lean` reaches it only under `SQLEANITE_PAGE_LOCAL_WRITES=1`, an
  explicit opt-in that exists precisely so the default cannot rest on an
  unchecked structural assumption;
- the opt-in path commits through `commitLocalized` rather than
  `commitLocalizedCertified`, so even when enabled its journal trace is not the
  one tied to the proved rollback plan.

`scripts/structural-check-census.py` measures what the missing checkers would
cost: 1,720 ms once per open at 1,000,000 rows, against 143,671 ms for a single
insert on the whole-database path. That is a cost measurement for a proof
obligation, not a discharge of it. Until a Lean checker with a soundness theorem
exists, the honest description is: proved, audited, reachable only by opt-in, and
not part of any performance number reported for the default configuration.

## Proof trusted computing base

Kernel-checked theorems trust:

- the Lean 4.19.0 kernel;
- Lean's primitive definitions used by the model, including `Float` at the
  abstract Lean level;
- any future imported theorem library (there are no package dependencies at
  present).

There are currently:

- no `sorry` declarations in `SQLeanite/`;
- no project `axiom` declarations in `SQLeanite/`;
- no `unsafe` declarations in `SQLeanite/`;
- no `native_decide` proofs in `SQLeanite/`.

The executable deliberately declares opaque `extern` functions for the narrow
host boundary: positional page reads/writes, `fdatasync`, parent-directory
`fsync`, `renameat`, `unlinkat`, and process-liveness probing. They are not used
to prove pure database theorems and are listed in the executable TCB below.
The verification audit admits exactly the eight named declarations in
`SyscallVFS.lean` and `ProcessLock.processAlive`; every other project `opaque`
declaration remains a hard failure.

Closed executable examples belong in `Tests.lean`; they are not counted as
semantic theorems. Definitional `rfl` lemmas may document an API but are not
counted as non-trivial verification results.

## Executable trusted computing base

Running the produced binary additionally trusts:

- Lean's elaborator, compiler, C code generator, runtime, garbage collector,
  standard library, and the platform C toolchain;
- the runtime implementation of primitive integer, string, array, and floating
  point operations;
- `Std.Mutex`, its opaque platform lock operations, runtime task scheduling,
  and `IO.asTask` for the serialized-connection shell and stress test;
- journal-temp creation through `IO.FS`, the explicit C syscall boundary
  (including constant-stack batched positional page write/read-back loops), and
  the operating system/filesystem/device behavior named by `SyscallVFS.Contract`;
- the generated-image header stamp as a provenance boundary for sub-linear
  cold primary and certified-index misses. It combines the `LSQL` application
  id with matching SQLite change-counter fields; ordinary SQLite commits
  invalidate it and are tested. Secondary lookup additionally requires the
  exact canonical `/*LSQL:INTEGER*/` catalog marker and locally validates every
  resolved rowid/value link.
  It is not a cryptographic MAC. An actor able to forge arbitrary database
  bytes and restore the stamp is outside the modeled VFS/serialized-writer
  threat model and could make an invalid off-path tree look like a valid miss;
- `Main.lean`'s unverified stdin/stdout rendering and file-facing shell;
- `LegacyServerMain.lean`'s test-only stdin/stdout protocol and the
  operating-system pipe when upstream conformance tests are run;
- `tests/sql/tester.tcl`, which is an unverified SQLite-test compatibility and
  callback adapter.

No C SQLite engine code is linked into the Lean executable.

## Opaque partial definitions

Lean compiles `partial def` through an opaque implementation that cannot be
unfolded by the kernel. There are now no project-local partial definitions in
the `SQLeanite` library or either executable root.

The potentially unbounded stdin and test-only server loops use Lean's standard
`IO.iterate`, which is itself an opaque partial runtime primitive and therefore
remains part of the executable I/O boundary. The project-local loop bodies and
all definitions in the pure SQL library are transparent.

`evalExpr` is no longer on this list. Its live implementation is a transparent,
structurally recursive worker bounded by the executable maximum nesting height
of its input expression. The height implementation and the bounds for direct,
array, optional, and case-branch children are kernel checked. Semantic success
theorems currently cover literals, collation wrappers, `IS NULL`, and
three-valued `NOT`. A general theorem that the computed height excludes the
worker's defensive fuel-exhaustion result on every expression remains to be
proved.

Eleven live expression analyses now share total, short-circuiting traversals
over the complete nested `Expr` structure. A separate traversal stops at SQL
subquery boundaries where the prior aggregate/default semantics did so. The
kernel-checked membership theorem shows that a matching array argument makes
the containing call match, instead of treating nested array recursion as an
opaque implementation detail.

`evalAggregate` is also total. Both its expression recursion and its
materialization of compound subqueries consume an explicit depth budget. The
public evaluator supplies the greater of the expression height and a
1000-level dynamic-subquery allowance, plus the root step; Lean proves that
this covers the complete syntactic input tree.

`executeSelect` now has a total compound-query driver with SQLite's 500-term
compound limit as its explicit recursion budget. Lean proves that a query with
no compound arms is exactly `executeSimpleSelect`, so the wrapper is connected
to the live simple-select semantics rather than merely being terminating test
scaffolding.

`runSQLProgress`, the live server entry point, was nonrecursive and is now a
regular transparent definition. Its parse-error theorem proves that a lexical
or syntactic failure returns the original database unchanged. Successful
execution now remains transparent through `executeCore` and the pure engine.

The live lexer loop is total. It consumes one unit of fuel per emitted or
skipped token and starts with one more unit than the number of input
characters; every non-empty token consumes at least one character. The public
budget inequality and empty-input tokenization are kernel checked.

Parser token lookup, constant-integer folding, balanced-clause skipping,
table-constraint skipping, and the top-level statement loop are now regular
definitions. Token lookup uses a bounded array scan and has a theorem showing
that positions at or past the end yield EOF at the unchanged position. Pratt
expression parsing now uses an explicit 1000-level recursion budget, and the
compound-SELECT parser uses SQLite's 500-term limit as its budget. Recursive
FROM parsing uses the same 1000-level stack budget while retaining unbounded
join-list breadth. The CTE inliner and recursive-CTE source check are total
traversals bounded by the exact compound-query height. There are now no opaque
partial definitions in the live lexer or parser.

`Select.compoundHeight` is a structurally recursive measure over the nested
array of compound arms. Its positivity and the bound for every member arm are
kernel checked, and it supplies the exact runtime budgets used by the parser's
query transformations.

The live LIKE/GLOB matcher and JSON5 object-key quoting pass are total. Pattern
matching consumes a budget derived from pattern plus text length; class scans
and JSON quoting consume budgets derived from their input lengths. The quoted
JSON string scanner is directly structurally recursive.

UTC year/day and month/day normalization are well-founded recursive functions.
Their strictly positive calendar-step lemmas justify termination, and
kernel-checked postconditions prove that each returned day lies inside the
returned year or month.

Direct-only-function and parameter checks now traverse compound queries using
their exact compound height; the statement-level direct-only check was
nonrecursive and is transparent. CHECK-qualifier rewriting, index-expression
nondeterminism diagnostics, and first aggregate/min-max searches traverse the
complete expression tree using its exact height rather than opaque recursion.

Result-schema inference now has an explicit budget combining exact compound
height with the database's configurable 1000-level default view-depth limit;
recursive view and parsed-subquery inference consume that budget. Result-name
projection is transparent, and compound-arm output matching uses exact query
height.

Source-free aggregate and outer-subquery checks are separate total traversals
over exact query and expression heights. Statement execution itself is
structurally recursive and transparent, supported by a total statement-height
measure whose positivity and nested-array member bounds are kernel checked.
Insert/delete-trigger recursion and cascading foreign-key deletes enforce
SQLite's 1000-level recursion convention explicitly; trigger-body dispatch is
nonrecursive and transparent.

The mutually recursive expression, subquery, SELECT, aggregate, and view
evaluators now share one decreasing budget. Internal calls consume the existing
budget rather than resetting it. Entry budgets combine exact expression or
compound-query height with the database's configurable view-depth allowance
and a 2001-step dynamic-query allowance. Lean proves that this allowance
strictly exceeds the configured view limit, and the live database-aware
evaluator has a kernel-checked literal-success theorem.

Expression-to-SQL rendering is now a total height-bounded traversal, including
the exact text-literal escaping rule used by schema diagnostics. Decimal
normalization is also total, with 400 shifts covering the finite IEEE-754
binary64 decimal exponent range (including subnormals). The abstract behavior
of Lean's primitive `Float` remains in the proof TCB as documented above.

## Denotational query semantics and optimizer

`SQLeanite/QuerySemantics.lean` defines an executable denotational semantics
for the MVP relational algebra over actual `Database` table rows. Rows retain
join structure, predicates return SQLite's three-valued `Truth`, WHERE retains
only TRUE, and ORDER BY is represented separately because row order is
observable. `BagEq` is core `List.Perm`; no theorem-library dependency was
added.

`SQLeanite/Optimizer.lean` proves exact evaluation equality for four real AST
transformations: left-side predicate pushdown through an inner join, recursive
three-valued constant folding, identity-projection elimination, and adjacent
filter fusion. Exact
equality implies bag equivalence and also discharges the stronger ordered-query
obligation. The same module proves De Morgan and NOT-equals rewrites, and gives
parameterized counterexamples showing why classical excluded middle and
predicate pushdown through a left outer join are unsound under SQL NULL.
`SQLeanite/ProofAxioms.lean` prints the axiomatic basis of every optimizer
headline theorem.

This semantics is deliberately a small verified relational algebra, not a
semantic interpretation of every constructor in the legacy parser's much
larger `SQLeanite.Select`. `CoreOptimizerBridge` embeds every live
single-table `Core.Predicate` into that denotation without converting values,
runs all four rewrites bottom-up, and projects it back. The bridge is used by
both rollback-journal and WAL SELECT execution before index selection, and its
round-trip and result-preservation theorems are printed by `ProofAxioms`.
The Core executor also invokes its proved recursive predicate normalization.
That pass performs double-negation elimination,
equality/inequality negation conversion, De Morgan rewrites, and recursive
child optimization under SQLite three-valued semantics;
`Core.Query.eval_optimize` proves the observable rows are unchanged. The
denotational join form remains broader than the current live bridge;
unsupported legacy features remain outside the verified-core claim.

## Ordered index core

The live expression-index SELECT branch is now proof-covered at its actual
boundary. `Engine.evalIndex` is the helper invoked by `executeSimpleSelect`: it
evaluates expression keys for each already-filtered environment and sorts by
those keys. `index_matches_scan` proves, from a successful live helper result,
that its output is a `List.Perm` of the full-scan candidate list. The proof
covers both key attachment and the exact insertion-sort implementation used at
runtime, so row loss or duplication in that path is a proof failure.

This is intentionally not described as indexed lookup: the current engine has
only index schema metadata and uses this branch to reproduce expression-index
scan order after a full filter. The theorem establishes P2 bag correctness for
the index behavior that actually executes today; building a physical lookup
index is part of Tasks 3 and 5.

`SQLeanite/BTree.lean` defines a transparent executable rowid search tree,
its global ordering invariant, lookup, insertion, and finite-map abstraction.
Insertion is proved to preserve ordering, and `toMap_insert` proves insertion
commutes with lookup at every key (replacement at the inserted key, no change
elsewhere). This establishes the abstraction framing needed by a B-tree.

It is not yet a SQLite B-tree: nodes currently hold one key, have no page
layout or occupancy/balance invariant, and are not used by live tables. Page
splitting, merging, serialization, and replacement of the `Array StoredRow`
table representation remain open.

`SQLeanite/PagedBTree.lean` is the mutation-tight replacement abstraction. It
stores sorted duplicate-free entries in capacity-two leaf pages behind a
proof-carrying root directory. Directory references are `Fin pages.length` and
the directory must enumerate every page exactly once, so an out-of-range,
duplicated, omitted, or reordered child pointer cannot be constructed without
breaking a proof. Its `toList` follows that directory and is multiplicity-aware.

Insertion/replacement and deletion repaginate the exact ordered entry list,
causing executable leaf splits and merges. Kernel theorems prove `toList_insert`
and `toList_delete` as exact abstraction-function commutation equations,
strict sortedness under the well-formedness hypothesis, capacity preservation,
and contents-neutral explicit overflow-page split and adjacent-page merge.
Executable tests cover a third-key split, replacement without duplication, and
deletion that merges two pages. These obligations detect duplicated medians or
dropped keys that the older extensional `toMap` theorem cannot see.

This is currently a two-level B+tree core with a proof-carrying root directory,
not yet SQLite's recursively balanced interior-page implementation, and it is
not on the live table path. Connecting it to physical page layouts and live MVP
tables remains part of the Task 5 vertical slice.

`SQLeanite/RecursiveBPlusTree.lean` begins the replacement recursive core. It
is an unbounded-height capacity-two 2-3 tree whose insertion descends through
one routed child, splits a full leaf, absorbs a split in a two-child interior
node, propagates a split through a full three-child node, and grows the root.
`insertStep_toList` is an induction over that recursive algorithm and proves
that the localized mutation implements the abstract ordered upsert; it does
not flatten and repaginate the input tree. `insertStep_balanced` proves that a
completed mutation preserves bounded leaf occupancy and equal child heights,
while a propagated split returns two balanced nodes at exactly the original
height; `insert_balanced` closes the root-growth case. Executable coverage
forces several levels of split propagation, decides the resulting balance
invariant, and checks lookup, range, replacement, and local deletion.
`deleteBalancedStep` propagates underflow explicitly, borrows from a three-child
sibling, merges with a two-child sibling, and shrinks the root.
`deleteBalancedStep_toList` follows every case and proves that the localized
mutation is exactly abstract key filtering; untouched siblings are justified
from their separator bounds.

`Node.Valid` combines occupied/bounded leaves, strict leaf ordering, equal
child heights, and disjoint separator intervals. `insertStep_valid` proves the
full invariant across every local descent/split case, `insert_rootValid` admits
only the empty root exception, and `insertAll_rootValid` makes the invariant
inductive from `Tree.empty`. Thus routing is no longer an unchained premise.
`rangeScan` uses those separator intervals to prune subtrees outside a half-open
key interval, and `rangeScan_eq_range` proves the localized traversal is the
same ordered result as filtering the abstraction list.

The executable `checkRootValid` reflects the entire structural invariant.
Public `delete` performs localized balanced deletion and accepts it when that
checker succeeds; an unexpectedly rejected candidate is rebuilt through proved
recursive insertion. `delete_rootValid` therefore makes validity correct by
construction for every input, while `toList_delete` proves exact filtering
semantics for every valid input. Regression coverage deletes 48 keys through
both operations, witnessing redistribution, merging, root shrink, and final
validity.

This recursive milestone is not by itself the physical SQLite tree. Deletion
validity is guarded by a reflected checker with a proved rebuild fallback,
rather than a direct theorem that every localized candidate passes. Leaves are
not linked. The former `CoreBPlusTree`, duplicate `TableTree` cache,
`CorePageState`, and non-live `CorePageDelta` adapter have been deleted.
`Core.Table` now stores a `PersistentPageTree.Store` plus a proof that its keys
represent exactly the logical row abstraction; there is no separately stored
row list. INSERT/REPLACE commute with that abstraction by theorem. The
page-identified packed `CoreChunkPageState` remains the live SQLite-page state,
and applies and proves the corresponding localized physical mutation. The
remaining consolidation gap is joining that packed physical state directly to
the table store, rather than retaining it at the connection/storage boundary.

`SQLeanite/RecursivePageBTree.lean` now supplies the separate physical
refinement layer. It groups page-sized cell runs into an arbitrary-depth,
balanced capacity-three plan, assigns pages in preorder, and encodes genuine
SQLite interior-table pages. `build_toCells` proves that grouping preserves the
exact cell sequence, `build_balanced` proves equal leaf depth,
`references_bounded` proves every recursively generated child pointer remains
inside its allocated extent, and `encodePagesFrom_length` ties emitted bytes to
that extent. A complete one-table integration seam emits a catalog plus the
recursive tree; both the general Lean decoder and C SQLite pass a height-three,
60-row image. The allocator now composes multiple tables with the existing
physical index allocator, and both rollback-journal and WAL adapters use it on
their live write paths. Index keys promoted into recursive interior pages are
removed from their leaves; `popMax_toCells`, `ofPlan_toCells`, and
`buildIndex_toCells` prove that this changes placement without dropping or
duplicating an entry. Index balance, recursive reference bounds, emitted page
count, and refinement to `CoreFile.indexCells` are also proved. C SQLite's
`integrity_check` and a forced index scan pass a height-two physical index.
The live store-owned encoder now has a compositional whole-image inverse at
both the page-source and byte-file entry points. The older canonical codec is
retained as an independent construction-time inverse fixture.

## Storage model and VFS boundary

`SQLeanite/Storage.lean` now defines fixed-size pages, in-range page ids,
logical disks, pending page writes, explicit sync operations, traces, and crash
outcomes. Its current model assumes atomic whole-page writes (no torn pages) and
allows writes not covered by a completed sync to be lost or reordered. It
proves that every crash after a completed sync observes exactly the newly
durable disk.

`SQLeanite/TornStorage.lean` makes the stronger hardware model explicit. A
`SectorGeometry` partitions a page into fixed-size sectors and
`SectorCrashOutcome` lets each sector independently retain its old or intended
bytes. Atomic old/new pages embed into this relation, while
`tornWitness_is_outcome` constructively exhibits `[1,1,0,0]` between all-zero
and all-one four-byte pages and proves it is not page-atomic. This establishes
that torn writes are now expressible and non-vacuous. The rollback atomicity
theorem has not yet been lifted to sector outcomes; doing that requires the
checksummed physical journal and explicit sector-ordering assumptions below.

The storage layer now includes an abstract rollback-journal cache, journal
creation/deletion and sync steps, staged main-file writes, seven observable
commit checkpoints, and recovery. `rollbackCommit_crash_atomic` quantifies over
every checkpoint and every main/journal crash outcome and proves recovery is
exactly the old disk or `applyWrites old writes`, never an intermediate disk.
The model assumes atomic whole-page main writes and atomic replacement of the
abstract journal snapshot; torn journal records are not modeled yet.

The original `Storage` rollback journal is a deliberate but major idealization: its
durable value is a **whole-disk snapshot**, not a header plus page-level undo
records. Recovery uses `recoveredJournal.getD recoveredMain`, so a surviving
journal replaces the recovered main image wholesale. The model therefore does
not prove SQLite's actual page-copy rollback algorithm. It remains as a legacy
fixed-geometry model used by existing physical-page theorems and is not the
headline crash result.

`SQLeanite/GrowableStorage.lean` is the replacement crash model. Its image has
a variable page count; writes may allocate pages; its journal header records the
original page count; and its undo list contains only pre-images of transaction
writes that address old pages. Recovery copies those recorded pre-images and
truncates the image to its original size. `rollbackCommit_crash_atomic`
quantifies over all seven protocol checkpoints and every modeled subset and
permutation of unsynced main writes, proving that recovery is equivalent to the
old or fully committed growable image. `crash_can_roll_back_growth`
constructively witnesses the new case: an allocation may reach the main file
and is removed by a surviving synced journal. A separate
`rollbackCommit_committed_recovers_new` theorem strengthens the final checkpoint:
after commit returns, every crash outcome recovers the new image rather than
merely one of old or new. Recovery replay is proved idempotent, and
`rollbackCommit_repeated_recovery_crash_atomic` proves the same old-or-new
result after an arbitrary finite number of recovery-process restarts which see
the surviving journal. More strongly, `RecoveryCrashTrace` exposes crashes at
intermediate writes inside the page-copy loop: at each recovery attempt, any
subset and permutation of unsynced authenticated preimage copies may survive.
`rollbackCommit_recovery_crash_trace_atomic` proves an arbitrary finite trace
of those interruptions still recovers to the same old-or-new result. The model
still assumes atomic whole-page writes and an atomic abstract journal value;
its theorem does not yet lift journal-record byte tearing or sector outcomes
into the protocol.

`Storage.VFSContract` is the formal boundary for the legacy fixed-geometry
platform adapter. An adapter
must refine reads, writes, syncs, and crash outcomes to the pure cache model.
`GrowableStorage.VFSContract` is the replacement boundary for the growable main
file and separate journal file. It covers main-page reads and writes, both sync
barriers, journal replacement/deletion, and joint main/journal crash outcomes;
verified recovery performs page restoration and truncation over those recovered
files. There is no project axiom asserting that a real filesystem satisfies
either contract. If such an assertion is added for Linux, macOS, or Windows, it
belongs in this TCB.

`SQLeanite/POSIXVFS.lean` exposes two refinements of the same rollback state
machine. `run_commitPlan` covers temporary-file write, journal `fdatasync`,
rename, directory `fsync`, main writes/`fdatasync`, unlink, and final directory
`fsync`. `run_persistentCommitPlan` covers a durable, pre-created journal inode:
write and sync an active undo record, publish and sync main pages, then write and
sync an inactive marker. Both prove exactly the committed growable rollback
state. The latter removes recurrent directory operations without weakening the
abstract ordering. Its inode is installed once through the former rename and
directory-sync sequence. `SyscallVFS.Contract` requires a concrete adapter to
refine every operation and joint crash outcome. No host filesystem is asserted
to implement that contract, so syscall, filesystem, device-cache, and
directory-durability behavior remains in the TCB.

The legacy physical adapter retains the rename/delete protocol and publishes a
complete image. The arbitrary-schema Core adapter executes the persistent-inode
protocol, uses `GrowableStorage.deltaWrites`, and writes only pages that are new
or byte-different. Its returned trace is exactly
`POSIXVFS.persistentCommitPlan`.
An orphan temporary journal is ignored and durably removed on reopen because
the protocol never starts main-file writes before publication of the final
journal name.

The fast suite deterministically materializes four concrete namespace/fault
states: orphan temporary journal, published journal before main writes,
published journal after the new main image, and journal deleted after main
sync. Recovery yields the expected old/old/old/new states respectively. A
covered-byte corruption is also injected and must fail closed before modifying
the main file. These tests exercise the executable boundary but do not replace
the still-trusted host-filesystem refinement obligation.

`SQLeanite/PhysicalJournalRecovery.lean` is now the shared pure recovery
executable for both live rollback adapters. It parses raw aligned pages without
trusting a possibly damaged database header, calls the same
`GrowableStorage.recoverWithJournal` function as the crash proof, and emits its
pages in order. `rollbackCommit_recovery_bytes_atomic` lifts the all-phase,
all-outcome theorem to exact equality with the old or new serialized byte
stream. Only filesystem reads/writes and the successful byte-to-page parse
remain between the live recovery path and this theorem.

`SQLeanite/GroupCommit.lean` models batches of full immutable database images.
`commitGroup_eq_commitSequential` proves that staging a chronological batch and
crossing one durability barrier produces exactly the same logical WAL as one
barrier per transaction. `sync_absorbPending_visible` proves that older pending
full images can be discarded without changing the post-sync visible state, and
the protocol count theorem reduces `n` syncs to one. This is currently a proved
optimization model, not yet the physical WAL adapter's commit implementation.

`CoreWALFileAdapter.commitBatch` now instantiates that result for chronological
lists of already-computed `Core.Database` states. Because each physical WAL is
a complete self-contained image, it publishes the proved newest state with one
WAL-file sync; the fast test checks both logical reopening and the single sync
call. Computing the batch and the host sync/rename semantics remain outside
this pure group-commit proof.

`SQLeanite/PageCache.lean` adds a proof-carrying bounded read cache and an
unbounded dirty write buffer. Resident keys are unique and cache length is
bounded by construction; `read_refines` makes every hit agree with an
authoritative store, and insertion preserves that relation. Dirty writes are
never hidden in the evicting read cache: the separate buffer absorbs repeated
writes to one page and `flush` returns every latest dirty page before becoming
empty. This pure cache is not yet on the live pager path.

`SQLeanite/PageReuse.lean` makes the two reuse barriers explicit. A free page
is selectable only when its free record has crossed the durability barrier and
its freeing epoch is older than the oldest active reader snapshot.
`takeReusable_sound`, `takeReusable_pending_none`, and
`active_reader_blocks_reuse` prove those obligations for every selected page.
This allocator policy is not yet connected to the live SQLite freelist pages.

`SQLeanite/CoreMultiFreelist.lean` removes the former single-trunk physical
limit. It partitions every unused-page suffix into SQLite trunk segments,
links each trunk to the next, and proves the emitted freelist has exactly the
requested page count; the complete padded image consequently retains its exact
original file size. The live arbitrary-schema rollback adapter now uses this
layout when a transaction shrinks its canonical image.

`SQLeanite/KRelation.lean` supplies a reusable multiplicity-valued denotation
for SQL bags. It covers `UNION ALL`, multiplicity intersection/difference,
`DISTINCT`, 3VL selection, Cartesian join, finite projection, grouping/count,
and natural-number group sums. Kernel theorems prove selection and aggregation
distribute over bag union, join substitution on either side, join commutation
through tuple swap, and DISTINCT idempotence. It is currently an algebraic
semantic layer alongside the live list semantics, not yet the evaluator for
the full Core query AST.

The live Core single-table query path now supports `SELECT DISTINCT`,
`COUNT(*)`, `COUNT(column)`, signed-integer `SUM(column)`, `MIN(column)`,
`MAX(column)`, and grouped columns plus these aggregate forms, with an optional verified 3VL
`WHERE` predicate.
`deduplicate_nodup` proves the executable eliminator returns no duplicate
projected row, and `Query.eval_nodup_of_distinct` lifts that fact to every
distinct query while `Query.eval_width` and the existing planner equivalences
continue to hold. `countInteger_exact` proves the checked signed-64 embedding,
and `execute_count_exact` states that every successful live count is exactly
the count of retained rows accepted by the explicit target (`COUNT(column)`
rejects NULL). `countRows_star` reduces the star target to the retained-list
length. Integer SUM ignores NULL, rejects TEXT in the intentionally strict
verified subset, returns NULL on an empty input, and range-checks every
signed-64 addition. `sumIntegerFrom_exact` and `sumIntegers_exact` prove a
successful executable fold equals the mathematical integer sum; no wrapping
or host overflow is trusted. MIN/MAX ignore NULL, return NULL on empty input,
and use the same exact SQLite storage-class and numeric ordering as ORDER BY;
`chooseExtreme_eq_left_or_right` and `extremeValues_mem_or_null` prove that the
fold can only return an input value or NULL, while `execute_extreme_exact`
connects that fold to live execution. The grouped evaluator proves
its key list duplicate-free, characterizes key membership by existence of a
selected row with exactly that value tuple, preserves result width, and is
connected to live execution by `execute_group_exact`. `AVG`, `HAVING`,
DISTINCT aggregates, and aggregate expressions beyond direct columns remain
outside this slice.

The live Core also executes `UNION ALL`, duplicate-eliminating `UNION`,
`INTERSECT`, and `EXCEPT` over supported SELECT arms. The transparent compound
driver is bounded by `Select.compoundHeight`, rejects unequal result widths
even when an arm is empty, and rejects the not-yet-modeled global compound
ORDER BY/LIMIT forms. `mem_combineRows` gives the exact row-membership semantics;
`combineRows_nodup` proves the three distinct operators eliminate duplicates;
and `combineRows_width` proves composition preserves the checked output width.

Two-table Core queries now include INNER and LEFT JOIN. LEFT JOIN constructs a
right row of exactly the stored schema width filled with NULL when ON retains
no right row, then applies WHERE after null extension as SQL requires. The
executable lemmas prove every per-left output is nonempty, selects exactly the
ON matches when any exist, selects exactly one null-extended row otherwise,
and always preserves the originating left row. The proved primary-key merge
planner remains deliberately restricted to INNER JOIN; LEFT JOIN uses the
exact nested-loop specification until an outer merge refinement is proved.

The legacy pager/journal model is not connected to the full SQL engine.
`SQLeanite/Durability.lean` retains the original fixed-geometry
`FixedDatabaseCodec` obligation and its conditional logical lifting theorem,
but that obligation is **unsatisfiable for the intended `Database` type**. At fixed page
size and count the disk type is finite while databases contain unbounded rows
and strings; `no_database_codec_at_zero` kernel-checks the simplest concrete
contradiction. Independently, exact roundtrip for the full legacy `Database`
would require proving `Float.ofBits (Float.toBits f) = f`, which Lean's opaque
primitive `Float` does not expose. Consequently the legacy conditional database crash
theorem is not evidence of logical durability and must not be counted as a
headline result. The replacement `Durability.DiskCodec` targets the dependent
`DiskFormat.DatabaseImage`, permits an explicit state equivalence, and therefore
does not impose a fixed finite codomain; no Float axiom is introduced.

`SQLeanite/PhysicalCodec.lean` supplies the first concrete witness for that new
interface. It deliberately fixes one table,
`items(id INTEGER PRIMARY KEY,first,second)`, and admits only NULL, signed
64-bit INTEGER, and at most 999 bytes of TEXT per value. Rows carry a strict
rowid-order proof and a proof that every cell fits one 4096-byte leaf page, so
overflow pages are rejected by construction. The encoder writes a real
two-page SQLite file: page one contains the database header and `sqlite_schema`
row, and page two contains the table leaf. The decoder reads the actual cell
content region and SQLite records, then checks the full page is canonical.
Kernel theorems prove cell-list, page, dependent-image, and complete-file
decode-after-encode round trips. The fast test writes those bytes and requires
the system `sqlite3` CLI to pass `PRAGMA integrity_check` and return the expected
rows.

`SQLeanite/PhysicalStore.lean` makes the restricted logical table executable rather
than requiring tests to assemble proof fields manually.  `orderedUpsert`
inserts any signed rowid in order and replaces an equal key; its strict-sorting
theorem is an induction over the executable comparison path.  `insertChecked`
uses that path but rejects an existing primary key, while `appendChecked`
remains a faster monotonic-rowid option.  `updatePayload` preserves rowid keys,
and `deleteRowid` filters the selected key.  Every operation re-enters
`PhysicalCodec.Database` through `rebuild`, which constructs the strict-order proof
and dynamically rejects a result that no longer fits the one-page MVP.  Kernel
theorems identify the exact resulting row list for insert/upsert, append,
update, and delete, and successful lookup is proved to return an existing row.
The rollback-adapter test commits a database produced by an out-of-order live
`insertChecked`.  Storage is still a sorted list rendered into one leaf page,
not the recursively paged B-tree needed after the MVP capacity limit.

`SQLeanite/LegacyFixedEngine.lean` is the first end-to-end pure command core over this
persisted type.  Its typed commands cover insert, replace, payload update,
delete, full scan, rowid lookup, and begin/commit/rollback.  Transaction
snapshots are immutable `PhysicalCodec.Database` values; rollback restores the exact
snapshot.  Insert and replace theorems connect successful command execution to
the verified `orderedUpsert`, and `run_append` proves command-list execution
composes across concatenation without an opaque loop.

`SQLeanite/LegacyFixedFileEngine.lean` is a thin unverified mutex/IO shell around that
pure core.  Autocommit writes use `PhysicalFileAdapter.commit` immediately; writes in
an explicit transaction remain private until COMMIT; rollback does not touch
the file.  The executable test rolls an insertion back, commits two
out-of-order inserts, reopens the SQLite file, and then persists an autocommit
update.  Thus the verified command/store functions are on this restricted
runtime path.  The shell-to-pure refinement, filesystem behavior, and mutex are
still trusted, and the legacy general SQL parser/engine does not yet delegate
matching SQL text to `LegacyFixedEngine`.  Direct typed-command callers and the
explicit restricted Core route below are the only live entry points.

`SQLeanite/CoreSQL.lean` and `sqleanite --verified-file DB [SQL-FILE]` now provide
an explicit SQL-text route to this restricted core.  The existing total Lean
lexer/parser handles syntax, after which a rejecting translator accepts the
exact `items(id INTEGER PRIMARY KEY,first,second)` physical schema,
NULL/signed-64-bit-INTEGER/short-TEXT literals, INSERT/REPLACE/UPDATE/DELETE,
the query subset below, and BEGIN/COMMIT/ROLLBACK.  CREATE declarations with
constraints or types absent from the encoded page-one schema are rejected.
The test parses and persists out-of-order inserts, checks SQL rollback, deletes
a row, and reopens the physical file.  Unsupported
forms return an error rather than falling through to the broader engine.  The
translation layer and UTF-8 CLI rendering are executable Lean but do not yet
have an end-to-end denotational correctness theorem. The separately built
`sqleanite_legacy_server` route remains the legacy
engine; it is not linked into the Core-only production executable.

`SQLeanite/Core.lean` begins removal of that fixed-schema keyhole.  Its
proof-carrying database supports multiple named tables, arbitrary column lists,
an INTEGER PRIMARY KEY at any column position, per-column NOT NULL, and
single-column index declarations.  Stored rows carry schema width,
primary-key/value agreement, and NOT NULL checks; tables carry rowid ordering
and index validity; databases carry unique table names.  Exact-result theorems
cover ordered insertion, checked row insertion, index addition, and table
creation.  Tests exercise two distinct schemas, a non-leading primary key,
NOT NULL rejection, and index metadata.

`CoreEngine.lean` and `CoreSQL.lean` put this model behind the real
total SQL parser.  The rejecting interpreter now executes arbitrary supported
CREATE TABLE declarations, CREATE INDEX on one column, reordered/multi-row
literal INSERT, SELECT projection/WHERE/ORDER BY/LIMIT/DISTINCT/COUNT(*)/GROUP BY, and transaction
boundaries against the proof-carrying database.  Column resolution is derived
from each stored schema rather than a three-constructor hardcoded column type.
Query output width, exact query/count execution, rollback restoration, and statement
list composition are kernel checked.  A two-table SQL test covers a
non-leading primary key, index creation, reordered insertion, filtering,
ordering, limiting, and NOT NULL rejection.

`CoreRecord.lean` connects arbitrary-width rows to SQLite physical record
and table-leaf cell bytes.  The INTEGER PRIMARY KEY payload position is encoded
as SQLite's canonical NULL placeholder while the signed key is carried in the
cell header.  The decoder reconstructs that column from the rowid, validates
the complete schema through `Row.create`, and has a suffix-preserving cell
roundtrip theorem.  Record/header and payload varint bounds are checked before
encoding instead of being assumed for unbounded column lists.

`CoreFile.lean` now serializes that arbitrary-schema database as a real
SQLite image. Page one contains generated `sqlite_schema` table and index
records; tables and indexes occupy one or more B-tree pages; arbitrary-width
table records use the verified codec above; and index cells are ordered by
indexed value and rowid. Every page and complete image carry kernel-checked
byte-length equalities. A two-table, one-index image passes the system SQLite
`integrity_check` and is queried through the C implementation in the test
suite.

Tables are no longer limited to one leaf page.  `CellPagination` splits encoded
cells into leaf-sized runs by actual byte size, and a table spanning several
leaves is given a real SQLite interior root page (type 5), so `rootPage` is
computed by a layout pass before the catalog is built.  Two facts are kernel
checked: `flatten_paginateCells`, that pagination loses, duplicates and
reorders nothing; and `paginateCells_fits`, that every emitted leaf fits a
page provided each cell fits a page alone. `CoreFile.encode` retains that
canonical no-overflow restriction for its existing whole-image inverse theorem.
The shipped adapters use `CorePageCodec.encodeChecked`, now a compatibility
name for the proved `encodeBulk`: table and index payloads
larger than their distinct SQLite local maxima retain the formula-selected
local prefix and allocate linked 4092-byte overflow pages after the owning
recursive tree. Planning pointers and final pointers have a proved equal byte
length, and the encoder dynamically checks that pointer substitution leaves
the recursive topology unchanged. Each raw overflow page has a kernel-checked
4096-byte length. The logical value bound is 999,999 bytes; this is a deliberate
finite implementation bound, not a SQLite format limit.

`CoreDecode.decodeSubtreeRows` descends interior pages on
the way back in, under an explicit fuel bound, so a cyclic or over-deep file
decodes to `none` rather than diverging. Table and index decoders follow
overflow chains with the database page count as fuel, require the exact final
zero sentinel, reconstruct the announced payload length, and reject cycles,
truncation, premature termination, and overlong chains. A live bidirectional
interop test writes a 9,000-byte indexed value from Lean, checks it through C
SQLite, then has C rewrite the value and both physical chains before Lean
reopens the result. The overflow-aware recursive encoder now has a
compositional whole-image inverse. `decodeFromPageSource_encodeBulk` combines
catalog, persistent table, overflow-chain, promoted-index and metadata
reconstruction refinements over the actual emitted page intervals.
The stronger `PageSourceRepresents` proposition retains those catalog, table,
and index components as separate proof fields.  Both
`pageSourceRepresents_encodeBulk_in` and the freelist-padded specialization
establish it, while its `decode` theorem recovers the public whole-image
inverse.  This decomposition is the representation invariant used by
localized-write preservation proofs; it carries no runtime validation data.
`CorePageSource.ofStorageImage` is the explicit bridge from the durability
model's zero-based growable pages to SQLite's one-based decoder reads.  Its
write lemmas prove that every distinct committed page reads back as written
and every unwritten old page is unchanged.  With the separately stated four
SQLite header fields, `CoreDurability.pageSourceRepresents_storageImage`
composes this component invariant into the public whole-byte representation
relation.  These propositions and proofs erase during compilation.
`CoreDurability.rollbackWrites_represents_crash_atomic` then lifts the
growable rollback protocol over an arbitrary exact page-write list: if the old
image represents the old Core database and applying those writes represents
the new one, every modeled commit crash and recovery decodes to exactly the
old or new canonical database.  Companion theorems cover a returned commit
and an arbitrary finite crash trace during page-by-page recovery.  The theorem
does not require the target to have been produced by the bulk encoder, so the
live-localized obligation is component-wise representation preservation rather
than another durability proof. `PostImageCertificate` now makes that
obligation constructive: its constructors are ordinary localized preservation,
decomposed component evidence, canonical bulk encoding, and verified freelist
padding. It has no constructor for a bare post-image decoder equation.
`CoreEndToEnd.WriteCommand` packages all seven persisted Core commands, and
`execute_write_exact` dispatches to their existing exact postconditions
without weakening the target-table or other-table frame clauses.
`executeCommand_commit_crash_atomic` composes that logical effect with the
generic page-delta theorem; companion results cover returned commit and finite
recovery-crash traces. `CoreSQLWriteText.TranslatedWrite` independently
describes how CREATE TABLE/INDEX, one-row INSERT/REPLACE, DELETE, UPDATE, and
COMMIT translate from the parsed AST to `CoreEndToEnd.WriteCommand`.
`executeStatement_eq_core` proves the live translator executes exactly that
command, and `executeText_commit_crash_atomic` starts from a SQL `String` and a
transparent parser/translation witness before reaching concrete recovered
bytes. `CoreSQLReadText.TranslatedRead` gives the non-aggregate single-table
SELECT an analogous result-independent translation relation;
`executeText_read_refines` proves actual supported text leaves the state
unchanged and yields exactly `CoreReadSemantics.queryDenotation`. Independent
lexing and parsing are now on that same live path. `Lexer.Tokenizes` records a
character-to-token derivation produced by `lexCertified`.
`CoreTokenGrammar.check` is a separate AST-directed grammar implementation: it
shares no recursive-descent routine or state with `Parser`, and replays the
significant tokens against the exact proposed AST, including names, literal
values, operator-tree precedence, delimiters, aliases, joins, statement
boundaries, and transaction commands. `parseCertified_agrees_parse` proves the
certified result is the broad parser's result, while `Parses.grammar` exposes
the independent replay witness. `CoreSQL.execute` consumes only this certified
result, and all read, single/multi-row write, and multi-statement trace support
relations now require `CoreTokenGrammar.Parses` rather than a bare parser
equation. The complete ordinary localized witness is assembled by
`OrdinaryLocalizedCommit.localizedRepresentation`. For the common indexed,
no-freelist, inline-row path,
`executeText_committedLocalizedIndexedInlineTables_crash_atomic` starts at
certified SQL text and the exact preparation/commit values returned by the live
adapter, derives the complete multi-table post-image internally, and reaches
old-or-new recovery plus the concrete POSIX request list. No caller-selected
post-state encoder result or whole-image decoder equation remains in that
theorem. `CoreLocalizedRepresentation` proves its physical read-after-write
layer. Every numbered page selected by
`CoreChunkPageDelta.writes` is present byte-for-byte in the resulting storage
page source; pages omitted from a distinct write set are preserved from the
old image.  A recursive table-decoder theorem consumes a mixed
changed/unchanged containment certificate (including overflow pages) and
returns exactly the proof-carrying logical table.  `PhysicalChunkPage` records
the derived SQLite separator that the generic tree page intentionally omits;
`encodeChunkNode_eq_mapM` proves these are exactly the existing encoder inputs,
and `encodeChangedChunkPages_accounts` partitions every post-state page into an
exact write or an exact pre-state page.  The live one-pass cached selector is
proved extensionally equal to that specification and avoids a quadratic scan.
For point mutations, `encodeChunkPath_subset_encodeChunkNode` proves that every
selected path page is an exact post-state page. `Node.PathAgrees` states that a
no-allocation insertion shares every page identity, separator, and sibling off
one root-to-leaf route. `encodeChunkPath_accounts_of_pathAgrees` turns that
structural relation into the complementary byte theorem: every complete
post-state page is either emitted on the path or occurs byte-for-byte in the
complete pre-state encoding. `replace?_treePagesAccounted`,
`insert?_treePagesAccounted`, and `delete?_treePagesAccounted` establish this
for point mutations; exact physical-difference proofs cover split, merge, and
bulk mutations. `replaceBetween?_treePagesAccounted` and
`updateState?_treePagesAccounted` compose all constructors through the live
state-delta builder. The converse family (`*_treePagesSelected`) proves that
every selected byte occurs in the complete post-state encoding. Successful
`numberedWrite?` conversion is proved in both directions, and active post-tree
page identities are unique. `pageSourceContains_updateStateTree` composes
these facts with old-image containment and read-after-write: applying the live
table write list contains the exact complete post-tree encoding without a
decode-and-compare check. Catalog metadata, exact promoted-index ownership,
freelist padding, and inline ordinary indexed/indexless mutations now compose
through `DatabaseOnSource`. `pageIds_disjoint_of_nodup` and
`retainedTableOnFinalWritesIndexed` derive the unchanged-table frame from the
allocator invariant, so the earlier one-table shortcut is no longer required.
Overflow-changing and freelist-changing writes remain on their proved
bulk/padded certificate paths; a single localized theorem covering those cases
is still open.
`decode_encodeBulk` then proves the public byte decoder returns the canonical
database. `decode_encodeChecked` exposes logical equivalence for adapter
callers. No theorem relies on executing a decoder and comparing its answer
inside the encoder; the standard-library UTF-8 round-trip law remains the
explicit premise. Post-write reopen checks remain because they validate bytes
that reached the filesystem, a separate refinement obligation.

Indexes use the same byte-driven leaf pagination and recursive SQLite
interior-index pages (page type 2). Promoted separator entries are removed from
their leaves, matching SQLite's index B-tree representation. The tolerant
decoder now traverses leaf and interior index pages, preserves promoted keys in
their in-order positions, decodes value/rowid records, and rejects an index
whose physical contents differ from the logical index derived from its table.
`CoreDecode.indexValueCandidatesFrom` performs value-interval-directed equality
descent and skips children whose separator bounds exclude the target;
`lookupIndexValueFrom_all_matches` proves every returned entry is SQL-equal to
that target. `indexRangeCandidatesFrom` performs the corresponding half-bounded
descent for `<`, `<=`, `>`, and `>=`, with
`lookupIndexRangeFrom_all_matches` proving result soundness. Their effectful
counterparts are on the live rollback-file query path.
The adapter maps physical rowids back into table order and records the number
of index pages acquired. A 120-row recursive-index test reads strictly fewer
than the index's total pages and executes the same SELECT through
`CoreFileEngine`.

Completeness of equality and half-bounded range pruning is now proved from the
promoted-key abstract tree and checked at the byte boundary. Generated INTEGER
and TEXT indexes and validating-open wider INTEGER indexes carry exact routing
certificates; mixed-storage indexes carry an exact all-value certificate and
filter that retained abstraction without rerunning the SQL plan. The sole
remaining `executeUncertifiedQueryWithCandidates` call is guarded by explicit
`FileProvenance.foreign`: arbitrary external bytes that fail certification are
compared with the verified logical executor, while generated images execute
the verified plan directly on an optimization miss. The live-path gate pins
that there is exactly one such call and that it remains under the foreign arm.

Ascending `ORDER BY indexed_column LIMIT n` uses a separate bounded cursor.
It crosses leaves only until the limit is satisfied and emits promoted
interior records exactly once. `AbstractIndexTree.cursorPrefix_eq_take` proves
its pure meaning is `take n` of the complete index abstraction, and
`indexPrefixFrom_decodeAbstract_exact` connects the shared pure/IO recursion to
decoded pages at arbitrary generated height. A multipage regression chooses a
limit larger than one leaf and compares the cold result with full Core
evaluation.

### Measured capacity and cost

Not a formal bound -- measured on this machine with ~30-byte rows.

| Rows | Autocommit | One transaction | Pages | C `integrity_check` |
|---:|---:|---:|---:|---|
| 500 | 22.8 s | 0.21 s | 6 | ok |
| 2,000 | 252 s | 0.33 s | 18 | ok |
| 10,000 | -- | 3.3 s | 51 | ok |
| 30,000 | -- | 30.6 s | 158 | ok |
| 60,000 | -- | 115 s | 313 | ok |
| 100,000 | -- | clean refusal | -- | -- |

Two separate quadratic costs, both real:

* **Per-statement whole-file rewrite.**  In autocommit each statement re-encodes
  and rewrites the entire database, which is why 2,000 rows takes 252 s
  statement-by-statement and 0.33 s inside one transaction.  Batching in a
  transaction avoids it entirely.
* **Rebuild-on-insert.**  `PagedBTree.Tree.insert` is
  `Tree.ofList (orderedInsert ...)`: it flattens the tree, inserts into a
  sorted list and re-paginates.  There is no descent, no localized split and no
  propagation, so each insert is O(n) and a bulk load is O(n^2).  This is
  invisible below a few thousand rows and dominates by 30,000.  The paged tree
  is therefore a *specification-level* structure, and the split theorems are
  correspondingly easier than the name suggests; real incremental B-tree
  insertion remains future work behind the same `toList` abstraction.

**Two-level ceiling.**  100,000 rows is refused with
`general MVP database exceeds the physical subset`: the single interior root
page cannot hold a child pointer for every leaf.  The tree is two levels deep,
so capacity is bounded by (interior fanout) x (rows per leaf) and is finite by
construction.  Verified-good capacity is **60,000 rows over 313 pages**,
round-tripping against the C implementation with `integrity_check ok`.
Going further requires a genuinely recursive tree, which is separate work.

`Core.orderedUpsert` previously recursed once per row of the prefix, so
inserting ascending rowids exhausted the stack near 60,000 rows and dumped
core.  `orderedUpsertTR` carries the prefix in a reversed accumulator and is
proved equal via `@[csimp]`, so the compiler runs the tail-recursive form while
every proof still sees the original definition.  Oversized input now fails
cleanly rather than crashing.

`CoreDecode.lean` provides the reverse path for the same physical subset.
Unlike the earlier canonical decoder, it follows the leaf-page cell-pointer
array and therefore accepts SQLite's free-space choices, and it accepts all
six SQLite signed-integer widths plus the compact zero/one serial types by
proof-preserving widening to the logical signed-64-bit type.  It parses table
and index declarations from `sqlite_schema`, reconstructs proof-carrying
tables, checks row width/primary-key/NOT NULL/order invariants, and restores
index declarations.  The interop test has C SQLite insert rows into both
tables and update the index, after which Lean successfully reopens and checks
the modified image. Interior table pages are traversed. Physical index
overflow records, non-UTF-8 encodings, and schema features outside the declared
MVP remain unread by the logical decoder. Index declarations come from the
catalog, but their referenced physical trees are traversed and checked before
the metadata is admitted.

The same module now also has a strict canonical decoder used for the proved
inverse. It decodes the database header and catalog, reconstructs arbitrary
schemas and multipage table rows, restores every table's index metadata, and
then requires byte-for-byte re-encoding of the complete image. That final
check covers physical index pages and rejects extra, corrupt, or noncanonical
pages rather than silently ignoring them. `decodeCanonicalFile_encode` proves
that every successful `CoreFile.encode` is recovered exactly. Its hypothesis
`UTF8Roundtrips` is the law `String.fromUTF8? value.toUTF8 = some value`; this
is kept explicit because Lean 4.19's standard library provides the executable
codec but no kernel theorem for that inverse. It is not a project axiom, and
the executable round trip is tested with ordinary and escaped identifiers.

`CoreFileAdapter.lean`, `CoreFileEngine.lean`, and
`sqleanite --verified-file DB` put those pieces on the live transactional
path.  The adapter journals exact page preimages read from the current file,
so a valid noncanonical C-written layout is the old state rather than being
silently canonicalized before journaling.  It then writes and reopens the new
proof-carrying image. `changedWrites_is_changed` proves every emitted page is
new or byte-different; `apply_deltaWrites_equiv` proves applying exactly those
writes yields the target growable image. The live adapter executes the same
page list with a Lean `readWrite` handle, combining adjacent dirty pages into
forward runs instead of replacing the file. `run_commitPlan` connects the emitted request sequence
to the abstract protocol, while `commit_crash_atomic` instantiates the
all-checkpoint/all-outcome theorem and proves recovery is equivalent to either
that exact old image or the new arbitrary-schema image.  Explicit transactions
remain private until COMMIT; autocommit statements persist immediately; and
the engine replaces its logical state with the result of physical reopening.
The live test creates two tables and an index transactionally, rolls a write
back, accepts two C-written rows, then performs another Lean commit and passes
C SQLite `integrity_check` and queries. A separate 100-row regression changes
one fixed-width payload, requires fewer page writes than the database page
count, reopens the result in Lean, and passes C SQLite `integrity_check`.

This closes the former hardcoded-schema keyhole for CREATE TABLE, CREATE INDEX,
INSERT, UPDATE, DELETE, SELECT, one INNER JOIN, and transaction boundaries.
UPDATE reconstructs selected rows through the schema validator and rejects
primary-key mutation and NOT NULL violations; DELETE rebuilds the proof-carrying
table from the retained rows.  `CoreJoin.lean` evaluates a two-table
cross product with SQL three-valued ON/WHERE filtering, projection, ordering,
and LIMIT, with kernel proofs for output width and ordering permutation.  The
live C/Lean roundtrip test exercises transactional UPDATE/DELETE and a join.
Generalized recursive physical splits, full index-content validation, and
validated page-directed point/range lookup are present for tables and indexes.
Integer-index equality and range lookup use retained proof-carrying
certificates and require no per-query result validation. Index-preserving
localized writes retarget those certificates only after checking exact logical
index-entry equality; the corresponding value/range exactness theorems are in
`ProofAxioms`. Full index changes discard them. Generated integer-only indexes
also carry an exact canonical `/*LSQL:INTEGER*/` catalog marker. The encoder
emits it iff all current indexed values are INTEGER, both catalog SQL forms
have proved parser round trips, and tests reject the marker on a text index.
This marker is meaningful only together with the generated-image provenance
stamp documented above; it is not independently cryptographic. Wider
C-produced INTEGER fanout is now certified after the general validating open;
`decodeWideAbstractIndexTreeFrom_toList` proves that its promoted-key tree has
exactly the ordinary complete physical decode's contents, and subsequent
equality/range queries use an exact ordered certificate. Mixed
storage classes receive an exact all-value certificate and avoid per-query SQL
plan comparison, but deliberately filter the retained abstraction until mixed
INTEGER/REAL separator order is proved. For generated
INTEGER indexes, the encoder now proves its globally sorted entry sequence,
the abstract decoder retains every promoted interior key exactly once, and
`lookupIndexValueFrom_encodeIndex_exact` /
`lookupIndexRangeFrom_encodeIndex_exact` construct routing certificates from
physical provenance without a linear cold scan. The shipped cold path requires
the stamp and marker, uses positional `pread` for the selected index and
primary-tree paths, and falls back after an ordinary C write invalidates the
stamp.
OS calls, synchronization, process-lock
implementation, and their refinement to the VFS contract remain trusted as
documented elsewhere in this file.

`SQLeanite/CoreFreelist.lean` closes the generalized route's former physical
shrink rejection.  A shrinking arbitrary-schema image retains the old page
count, replaces only page one's 100-byte database header, makes the first
unused page a freelist trunk, and names every later unused page as a freelist
leaf.  Kernel proofs establish every page's fixed length, the exact active and
free page counts, trunk capacity, and the padded image's old page count.  The
live rollback-journal adapter commits that padded image and reopens its
logical database. `CoreFreelistCodec.decode_paddedImage` now proves that the
actual whole-file bytes—including the rewritten header, any number of freelist
trunks, and unreachable free-page tail—decode to exactly the canonical Core
database. `pageSourceRepresents_padded` additionally preserves the component
catalog/table/index witnesses needed for local mutation. The
representation-parametric crash, returned-commit, and
recovery-crash-trace theorems are specialized to this padded image, closing
the former logical gap for shrinking bulk commits. A fast end-to-end test
collapses a multipage table and
secondary index, checks the file did not truncate, and requires C SQLite
`integrity_check`, a positive `freelist_count`, and the expected row count.
`CoreMultiFreelist` recursively emits as many capacity-bounded trunks as the
old file length requires.

Core reopen no longer begins with `readBinFile`.  `CoreDecode.IOPageSource`
lifts the same total, fuel-bounded recursive table and index traversal over an
effectful page acquisition boundary, and `CoreFileAdapter` supplies a regular-
file implementation that reads one validated SQLite page at a time. General
opens accept zero-reserved-byte 1024, 4096, 8192, and 65536-byte images (and
the other standard power-of-two sizes admitted by `ValidSQLitePageSize`),
including SQLite's special header value for 65536. The runtime size is carried
as `UsablePageSize`, whose bounds are proved at header validation; table,
index, interior, and overflow decoding all consume that same value. The proved
writer and generated-image fast paths deliberately remain fixed at 4096 bytes.
`CorePageLoad.loadNode_decodes` proves, by induction over the fuel-bounded
tree, that the persistent write-open loader and the public logical decoder
recover the same ordered rows.  `open?_decode` lifts that result through all
tables, index application, and database rebuilding: a validating open now
carries a theorem about the bytes it read rather than an unrelated shadow
tree.
Forward reads
discard skipped bytes; backward reads rewind; no resident whole-file byte array
is constructed.  The decoder requests only catalog-reachable table and index
pages, which a counted-source test checks by padding a valid image to 100 pages
and observing that the freelist suffix is never requested.  Lean's opaque
`IO.FS.Handle.read`, `write`, `flush`, rewind behavior, metadata, cursor
semantics, and short-read semantics remain
in the VFS TCB.  Commit and crash recovery still read the old image eagerly to
construct/restore the page-level undo journal; the lazy path currently applies
to ordinary reopen and query startup.

`SQLeanite/PhysicalQuery.lean` is the live read evaluator for that route.  It
implements projection over the three fixed columns, three-valued equality,
inequality and ordered comparisons, NULL, NOT/AND/OR predicates, ordering,
and LIMIT.  The same predicate evaluator selects rows for UPDATE and DELETE,
including operations without a WHERE clause.  Exact post-state row-list
theorems, output-width, limit, filter-membership, and order-permutation
properties are kernel checked.  ORDER BY uses a stable verified permutation
sort over lexicographic stored-column terms.  General expressions and joins
outside one qualified self INNER JOIN are still rejected. The join evaluator
uses 3VL ON/WHERE filtering, projection, ordering, and LIMIT. Pure primary-key
equijoins without an additional WHERE clause take a linear merge over the
already rowid-sorted tables; other shapes retain the cross-product evaluator.
`mergeRowids_eq_spec` proves exact ordered-list equality with the nested-loop
rowid specification, `rowidJoinSpec_eq_matchingRows` connects that specification
to SQL column values, and `evalPlanned_eq_eval` lifts it through ORDER BY, LIMIT,
and projection. Output width and ordering permutation are also kernel checked.

Primary-key equality queries use an early-terminating ordered lookup rather
than filtering every row.  `lookupRowid_eq_filter` proves that live path returns
exactly the full-scan result, and `evalDatabase_eq_eval` lifts the equality
through ordering, LIMIT, and projection.

The general Core planner distinguishes full scans, equality-index paths, and
half-bounded range-index paths. `indexedCandidates_filter_eq_scan` proves both
index shapes return exactly the full-scan filter under SQLite 3VL, and
`eval_plannedRows` lifts the substitution through projection, ORDER BY, and
LIMIT. `chooseAccessPath_estimatedRows_le` proves the chosen path's simple
selectivity estimate never exceeds the scan estimate. The current in-memory
candidate implementation still filters the resident rows; connecting this
choice to a lazy physical index interval is a remaining refinement theorem.

Multi-row INSERT and REPLACE are one pure command and one persistence action;
a duplicate or page-capacity error therefore exposes no prefix database.  Its
successful post-state is proved equal to the ordered-upsert fold.  FAIL,
ROLLBACK, and IGNORE conflict policies are rejected because their distinct
statement/transaction semantics are not yet implemented.

`PhysicalStore.upsertChecked` now executes the verified `PagedBTree.Tree.insert` on
the live persisted SQL path.  A proved signed-rowid bias preserves strict key
order, and `Database.tree_insert_rows` connects the tree abstraction back to
the exact logical `orderedUpsert` result.  This is still an in-memory two-level
tree whose leaves are repacked at capacity two.  Primary-key DELETE likewise
executes `Tree.delete` and is proved equal to rowid filtering.

`PhysicalTableBTree.lean` and `PhysicalMultiPageCodec.lean` now persist that capacity-two
partition as a real two-level SQLite table B-tree.  A one-leaf tree keeps page
two as the root leaf; after a split page two becomes an interior-table root and
bounded child page numbers select leaves from page three onward.  Separator
keys are the maximum rowids of the left children.  The abstraction theorem
proves the leaf partition flattens to the exact logical row list, every emitted
page is 4096 bytes, and complete-file decoding concatenates verified leaf
decodes and then requires canonical re-encoding of the root and all page
references.  The system `sqlite3` CLI passes `integrity_check` on a five-page
three-leaf image.  The logical `PhysicalCodec.Database.pageFits` field still limits
the *aggregate* encoded cells to one page, however; overflow payloads and
databases larger than that legacy logical capacity remain rejected even though
physical splits now execute.

The multi-page codec lifts the pure growable commit theorem.
`GrowableStorage.replaceWrites` enumerates every target page; kernel proofs
show applying it yields the exact target image and that every modeled
crash/recovery yields the old or new image.  `PhysicalFreelist.lean` handles a
logical tree that becomes smaller without asking the abstract main file to
truncate: the file retains its old page count, page one names a freelist trunk,
the trunk lists the remaining free leaves, and the database header carries the
exact total free-page count.  Page-list and byte-length theorems cover the
complete padded image.  The current verified layout supports one freelist
trunk (up to 1,023 free pages), which is comfortably above the MVP's aggregate
one-page logical row bound; larger freelists reject rather than overflow.

`SQLeanite/PhysicalFileAdapter.lean` now exercises that vertical slice through a
real growable file.  Its pure `commitPlan` contains journal-write,
journal-sync, one request for every target page, main-sync, journal-delete, and
deletion-sync requests;
`run_commitPlan` proves interpreting those requests is exactly
`GrowableStorage.rollbackCommitState ... committed`.
`PhysicalJournalCodec.lean` encodes the original page count plus page-numbered
preimages and has a suffix-preserving roundtrip theorem.
`decodeChecked_makeJournal_exact` additionally proves that the checksummed
bytes emitted by the live adapter decode to no invented records and to a
recoverable preimage for every overwritten page that existed before the
transaction.  The IO adapter syncs
that journal, writes the complete new multi-page image, syncs the main file,
deletes and syncs the journal deletion, and reopens through the verified
decoder.  Tests cover a two-to-five-page live commit accepted by C SQLite and
recovery from an injected grown main file; recovery restores old preimages and
truncates the three new pages.  They also shrink a five-page tree to two active
pages, require C SQLite `integrity_check` and `PRAGMA freelist_count=3`, and
reopen the logical rows through Lean.  `run_commitImagePlan` proves the padded
request trace equals the abstract committed protocol, and
`commitImage_crash_atomic` quantifies over every modeled phase and crash outcome
to yield either the exact pre-commit image or the freelist-backed new image.
The seven-case persistent MVP differential arm, including its former red
UPDATE/DELETE shrink case, is green.

The localized live adapter now crosses an explicit C syscall boundary for
`pread`, `pwrite`, `fdatasync`, parent-directory `fsync`, `renameat`, and
`unlinkat`; recurrent Core commits return the exact
`POSIXVFS.persistentCommitPlan` trace that those calls are intended to
implement. `SyscallVFS.Contract` has one conditional refinement field per
syscall class, and `completedPersistentCommit_refines` proves any execution
satisfying those fields reaches the abstract committed state. This still does
**not** prove that Linux, a particular filesystem, or a storage device satisfies
the contract. Journal-temp creation and host error reporting also remain in
the executable TCB. The MVP journal is a SQLeanite-specific format, not SQLite's
rollback-journal byte format. Its persistent envelope has proved active and
inactive round trips, a checked length, and spare inode capacity; the inactive
marker starts with zero so C SQLite treats the retained file as non-hot. The
active record carries a checksum over every covered journal byte; round-trip
and "accepted implies stored checksum equals recomputation" are kernel-proved,
without assuming collision freedom. It still has no sector padding, and
checksum collisions remain possible. Consequently
the stated host assumptions remain required for an end-to-end durability claim
about executed SQL. Crash injection, device-level power-loss injection, and the
missing-journal-sync mutation validate those assumptions empirically without
turning them into kernel theorems.

## Cross-process serialized boundary

`SQLeanite/ProcessLock.lean` specifies an exclusive-owner state machine.
Acquisition succeeds only from the unlocked state, release requires the same
owner, a sequential pair of critical sections constructively succeeds, and an
overlapping acquisition is constructively rejected.  The `--verified-file` CLI now
holds one lock across open/create, SQL execution, commit/recovery, and result
rendering.  A fast integration test starts eight independent SQLeanite
processes against one file and requires C SQLite to observe all eight rows and
an intact database afterward.

The live wrapper now returns a `CompletedCriticalSection` on success.  That
value contains the caller's real process id, its exact abstract acquire/release
events, and a kernel proof that the pure lock machine accepts the trace; the
ordinary `withLock` API is just its result projection.  `RuntimeRefinement`'s
`LiveHistory` pairs those certificates with measured writer tenures and reader
snapshot intervals.  `LiveHistory.serializable` composes lock ordering with the
multiwriter WAL theorem to produce a well-formed serial execution with the
same final `Core.Database` and reader observations.  This closes the prior
proof-composition gap: the live call shape, tenure-to-writer mapping, and
history theorem now share one explicit refinement record.

The runtime refinement is intentionally weaker than SQLite locking: it relies
on atomic filesystem directory creation and removal.  Those operations, retry
timing, process scheduling, and ownership identity are unverified.  Each lock
directory now records its owner process id; contenders call the opaque
`ProcessLock.processAlive` binding, implemented by the tiny `kill(pid, 0)` C
boundary, to reclaim an owner that the host reports dead, and a focused
regression creates and recovers a stale owner. The binding's liveness result,
PID identity/reuse, permission/error interpretation, and directory operations
remain explicit executable-TCB assumptions. Clients that do not use this
SQLeanite CLI do not honor the lock. This is
cross-process *serialized safety*, not concurrent-reader WAL behavior or
compatibility with SQLite's SHARED/RESERVED/PENDING/EXCLUSIVE byte-range locks.

## Physical WAL byte codec

`SQLeanite/PhysicalWAL.lean` now defines the concrete SQLite WAL header and
frame byte format for 4096-byte pages.  The header uses magic `0x377f0683`, WAL
format version 3007000, checkpoint sequence, salts, and SQLite's paired 32-bit
rolling checksum.  `Header.checksum_bytes` proves that the semantic three-pair
header recurrence equals checksumming the actual encoded 24-byte prefix.
Frames encode a positive page number, commit database size, matching salts,
the checksum chain, and exactly one page.  Suffix-preserving header, frame, and
frame-list roundtrips compose into `decode (encode wal) = some wal`; the decoder
also rejects bad constants, salt mismatches, checksum mismatches, truncated
frames, and non-frame-aligned files.  The fast suite executes a two-frame
roundtrip with distinct pages and verifies the byte recurrence.

`SQLeanite/PhysicalWALRecovery.lean` connects those bytes to the verified MVP page
image.  It emits every target page in descending order and makes the final page
one frame the commit marker.  The frame-to-write theorem proves these are
exactly the growable replacement writes.  Recovery remembers only states ended
by a nonzero commit marker, so valid trailing uncommitted frames are invisible;
`recover_forTree` proves recovery yields a storage image decoding to the exact
target logical rows.  Unlike the rollback adapter, this full-image WAL path can
represent both growth and shrink.

`SQLeanite/LegacyWALFileAdapter.lean` is the first executable physical-WAL edge.
It writes a complete WAL to a temporary file, syncs it, publishes it by rename,
reopens committed pages after restart, and checkpoints the recovered image to
the main file before deleting the WAL.  Tests establish that commit leaves the
old main file untouched, restart ignores a checksum-valid uncommitted tail, and
C SQLite accepts the checkpointed result.

`LegacyWALFileEngine` and `sqleanite --mvp-wal-file` put this adapter on a parsed
SQL execution route.  The command classifier has a kernel theorem showing that
every member of a batch classified read-only has `Command.writes = false`.
Such batches reopen an immutable committed snapshot without the process writer
lock.  A mutating batch holds one cross-process writer lock from reopen through
all statement execution and WAL publication, so cooperating writers cannot
both compute from the same old snapshot.  `--mvp-wal-checkpoint` materializes
the current snapshot.  The fast integration test runs eight writer processes
and concurrent lock-free reader processes, then requires C SQLite to accept the
checkpoint with all rows present.

Atomic rename, directory-entry durability, whole-file reads, command-classifier
dispatch in `Main.lean`, and every `IO.FS`/`sync` operation remain unverified
refinement obligations.  The adapter uses fixed salts and replaces a complete
self-contained WAL rather than appending transactions; it does not implement
the `-shm` wal-index/read marks or SQLite byte-range locks.  The runtime path is
therefore interoperability and stress evidence, not a theorem that OS
executions refine the pure WAL serializability and recovery models, and it does
not establish end-to-end OS durability.

## Serialized connection and concurrency boundary

`SQLeanite/SerializedConnection.lean` supplies the Tier 1 runtime shell.  Its
only mutable state is one `Std.Mutex Database`; `execute` holds that mutex
across the complete live `runSQLProgress` transition, and `snapshot` reads under
the same mutex.  The engine transition itself remains pure.  The fast suite
repeatedly starts eight dedicated runtime tasks against one connection, gives
each task multiple independently locked inserts, and checks a primary-key table
contains every row.  This samples real interleavings and detects lost updates,
but it is a stress test rather than a proof about Lean's task runtime.

The same module writes down the pure `SerializationContract`.  A concurrent
history satisfies it only when some permutation of the submitted requests,
run through the actual `runSQLProgress` reference semantics, produces exactly
the final database and completion sequence.  Kernel-checked induction proves
that schedule concatenation agrees with sequential composition and that every
request produces exactly one completion carrying the same request id.  Every
pure sequential run constructively satisfies the contract, so the obligation
is not empty.

There is deliberately no theorem claiming that `Std.Mutex` or the IO shell
refines `SerializationContract`: Lean core provides neither a formal concurrent
IO semantics nor a separation logic, and the mutex primitives are opaque
runtime operations.  The mutex implementation, scheduler, and this refinement
step therefore remain in the executable TCB.  Tier 1 prevents data races by a
coarse trusted lock; the separate Tier 2 model below is what permits readers to
retain snapshots while a writer computes.

## Logical WAL and one-writer serializability

`SQLeanite/WALConcurrency.lean` is a pure logical WAL/MVCC model.  A WAL has a
checkpointed immutable `Database`, newest-first durable frames, and one pending
frame.  `visible` ignores the pending frame; `sync` publishes it; and
`checkpoint` folds the visible version into the main image.  Kernel theorems
show pending data is invisible, a logical commit publishes exactly its proposed
database, checkpointing preserves the visible database, and a reader retains
its pre-commit immutable snapshot.

Raw timed schedules admit any number of writers.  `Accepts` explicitly rejects
all but zero or one writer transaction, validates every interval, and requires
globally unique transaction ids.  Readers may overlap that writer.  The
`accepted_schedules_are_serializable` theorem constructs a serial execution by
placing readers before or after the writer according to their snapshot-begin
time.  Its outcome equality covers the final database and the complete
transaction-id-indexed reader-observation relation.  Non-vacuity is checked in
both directions: `some_nontrivial_interleaving_is_accepted` constructs a reader
spanning the writer's commit interval, while
`lost_update_schedule_is_rejected` constructs a two-writer raw schedule and
proves it is not accepted.

The pure `WriterProtocolState` separately models lock, append, sync, and unlock
events.  Append and sync require the writer lock, and unlock is rejected while
a pending frame exists.  Successful steps and arbitrary successful traces
preserve the invariant that an unlocked state has no pending frame;
`writerProtocol_completes` proves the intended lock/append/sync/unlock ordering
ends with the new database visible and the lock released.  This ordering is a
contract model, not a proof about the runtime lock implementation.

The introductory theorem above permits only one writer transaction in the
complete modeled history.  `SQLeanite/WALMultiWriter.lean` removes that limit:
`Accepts` permits an arbitrary chronological list of writers whose intervals do
not overlap, while readers may overlap any number of them.  `visibleAt` selects
the durable version at each reader's begin tick.  The construction partitions
readers into writer epochs; kernel-checked permutation and observation lemmas
show no reader is dropped or duplicated and each retains the same version.
`Multi.accepted_schedules_are_serializable` proves equality of the complete
reader-observation relation and final WAL database.  A two-writer/two-reader
interleaving is constructively accepted, while an overlapping two-writer
schedule is constructively rejected.  This is the intended “one active writer,
many sequential writers” restriction; it does not claim general serializable
snapshot isolation.

Transactions still operate on whole immutable `Database` values.  The separate
physical WAL codec above supplies frame bytes and checksums, but it has not yet
been connected to this logical model; locking bytes, crash recovery, and
filesystem durability semantics are still absent.  In particular, the logical
`sync` is a pure state transition and is not evidence that an operating-system
sync completed.

`SQLeanite/WALConnection.lean` is the corresponding unverified runtime shell.
A short `Std.Mutex` protects publication and a separate `Std.BaseMutex`
serializes writers.  A reader copies the published immutable database under the
short lock and evaluates after releasing it; a writer similarly copies the old
version, computes privately, then publishes one logical WAL frame under the
short lock.  The stress test repeats a 200-row writer with eight concurrent
reader tasks and accepts only the complete old or complete new row count, never
an intermediate count.  The test samples runtime schedules; there is no theorem
that the opaque locks, scheduler, shell, or logical sync refine the pure model
or a physical WAL/VFS contract.  Those items remain in the executable TCB.

The preregistered P5 mutation arm injects four faults into this pure boundary:
admitting two writers, returning a mixed old/new reader snapshot, releasing the
logical writer lock before WAL sync, and exposing a pending frame before sync.
All four make a semantic theorem false and fail `lake build`; they are reported
as bucket-2 proof detections in `mutations/results.md`.  This does not show that
the proof detects mutations made only in the unverified `WALConnection` shell.

`scripts/run-differential-smoke.sh` is an unverified comparison harness.  It runs
ten deterministic SQL files against both the Lean batch executable and the
system C `sqlite3` CLI and compares process status and stdout byte-for-byte.
The corpus exercises the core DDL/DML/query subset and currently passes.  This
is finite interoperability evidence, not a semantic theorem, a C source-level
mutation campaign, or coverage of SQLite's full Tcl suite.

`scripts/run-mvp-differential-smoke.sh` separately runs seven deterministic files
through the persisted `--verified-file` route and C SQLite, each with its own real
database file.  It covers projection, NULL logic, predicate-selected writes,
rollback/commit, REPLACE, and a self inner join.  Its byte-for-byte output comparison is likewise
bounded interoperability evidence rather than proof.

The mutation comparison now includes ten preregistered C-source faults across
query semantics, affinity, index/B-tree behavior, and file truncation. All ten
mutated CLIs compiled; nine were detected by the first bounded witness. The
AND-as-OR witness was constant-folded and is retained as a miss. The Lean arm
executes zero queries before its credited proof failures, but this does not
support a blanket wall-clock advantage. Exact timings and exclusions are
disclosed in `mutations/results.md`. A separate test-only power-loss VFS now
detects the held-out missing-journal-sync mutation while stock SQLite satisfies
the old-or-new oracle. That C shim, process termination, host filesystem, and
finite 20-seed oracle are unverified benchmark machinery; they do not
strengthen the Lean TCB or constitute a VFS refinement proof.

The unmodified upstream `select1.test` and `insert.test` files run through
`tests/sql/tester.tcl` and the separate `sqleanite_legacy_server` binary: the
recorded focused checkpoint is 191/191 and 76/76, respectively.
`scripts/run-focused-upstream.sh` builds that non-default test target and executes
the tests in a temporary directory so checkout database files are untouched.
These 267 assertions are a bounded sample over the broad unverified
interpreter, not evidence that the verified Core implements the same surface;
the expensive full upstream suite was not run at this checkpoint.

`SQLeanite/FileFormat.lean` begins the concrete codec with big-endian 16- and
32-bit fields over actual `UInt8` bytes. It proves decoded values are in range,
decode-after-encode returns the exact bounded value while preserving the
unconsumed suffix, and truncated integer fields are rejected. Its complete
100-byte `DatabaseHeader` codec validates the exact `SQLite format 3\0`
signature, the fixed payload-fraction bytes, and all 20 zero-valued reserved
bytes. Kernel-checked theorems establish the exact encoded length and a
whole-header decode-after-encode round trip that preserves trailing bytes.
Fields whose SQLite interpretation is signed or conditional are deliberately
retained as raw 32-bit values at this layer.

`DatabaseHeader.WellFormedFor` now validates the special 65536-byte page-size
encoding, supported power-of-two page sizes, reserved-byte/usable-size
relationship, database page count, read/write versions, schema format, and
text encoding. A dedicated page-one representation places this verified
100-byte header before the B-tree prefix at byte 100, proves exact page size
and header/prefix lookup behavior, and emits pager page id zero. Ordinary
B-tree layouts therefore cannot silently be used as SQLite page one.
The combined database-header/B-tree-prefix decoder validates both layers at
the byte-100 boundary and has a suffix-preserving decode-after-encode theorem.

The same module implements SQLite's canonical unsigned 64-bit varint format,
including the special ninth byte that contributes eight rather than seven
payload bits. The encoder's length is proved equal to the canonical 1–9 byte
size function, and decode-after-encode is proved to recover every value in
`Fin 2^64` while preserving the unconsumed suffix. Runtime tests cover every
length transition and the exact maximum-value byte vector. The live SQL
engine's record-size estimator now uses this verified size function rather
than a duplicate implementation.

Record serial-type metadata is also typed: fixed integer/float/null tags are
enumerated, reserved codes 10 and 11 have no semantic constructor, and dynamic
blob/text tags carry proofs of their lower bound and even/odd parity. The
decoder/encoder roundtrip and payload-width preservation are kernel checked.
Canonical integer-width selection lives in this module, has an eight-byte
upper-bound theorem, and is used by the live record-size estimator.

A generic fixed-width big-endian unsigned codec now supplies the common byte
primitive for 1/2/3/4/6/8-byte payloads and page fields. It has proofs of exact
encoded width, suffix-preserving decode-after-encode for every value within
the width's range, exact byte consumption on every successful decode, and
rejection of truncated input. Signed integer payloads use a six-constructor
width type, so only SQLite's 1/2/3/4/6/8-byte widths are representable. Their
two's-complement conversion is proved to stay within the matching unsigned
modulus, conversion back is proved extensionally equal to the original
bounded integer, and the composed byte codec has exact-length,
decode-after-encode, suffix-preservation, and truncation theorems. Float,
text, and blob payload bytes are represented in `SQLeanite/Record.lean` as
physical fields whose serial metadata and payload size agree by construction;
floats remain raw IEEE-754 bits at this layer. Every field constructor has a
kernel-checked suffix-preserving payload roundtrip theorem, and sized payload
decoding rejects truncation. Physical record encoding now emits the header-size
varint, serial-type varints, and concatenated payloads. A fixed-point theorem
proves that the encoded header length is exactly the size it announces, and
the live `dbstat` record-size estimator uses this verified calculation. The
total whole-record decoder validates the announced header boundary,
canonical serial varints, and the size fixed point before constructing a
proof-carrying record. Its whole-record decode-after-encode theorem covers
every physical field list and preserves trailing bytes. Text encoding from
logical strings, page payloads, and logical SQL database serialization remain open.

`SQLeanite/PageFormat.lean` begins the concrete B-tree page refinement over
`Storage.Page`. It implements and roundtrip-proves SQLite's four B-tree page
type tags and exact 8/12-byte headers. Page numbers used by cell and overflow
codecs are positive bounded 32-bit values, making SQLite's reserved page zero
unrepresentable. `BoundedPageNumber` additionally proves a reference is no
larger than the database page count and converts to the pager's zero-based
`Fin pageCount`; both one-based/zero-based conversion roundtrips are kernel
checked. The same database bound is propagated through interior-header child
links, all four cell variants, and every page in an overflow chain.
The current verified physical-page subset explicitly requires the header's
reserved-byte count to be zero, so its usable page size is also its on-disk
page size. This is SQLite's normal default and prevents a header from claiming
larger physical pages than the typed pager actually serializes; nonzero
reserved tails remain unsupported rather than silently mis-modeled.
Proof-carrying bounded page layouts and bounded overflow chains expose these
facts to the pager, including a bounded pager id for each chain root. Raw
header fields remain decodable for diagnostics, while a
valid interior header rejects a zero rightmost-child reference. Valid decoded headers carry the
fragment-count, freeblock, content-area, and cell-pointer-array bounds needed
for safe page access, including the special zero encoding for offset 65536.
The decoder can consume an abstract fixed-size `Storage.Page`. Cell-pointer
arrays are now count-indexed by their header and each pointer is validated to
lie between the content-area start and page end; their codec has exact-length
and suffix-preserving roundtrip theorems, and the encoded prefix is proved not
to overlap cell content. Interior table cells now encode a bounded child-page
number and a signed 64-bit rowid key in SQLite's exact byte layout. Inline
table-leaf cells tie their payload-size varint to a payload of exactly that
many bytes by construction. Both cell codecs have exact-length and
suffix-preserving decode-after-encode theorems; truncation is covered by the
underlying verified field decoders and executable boundary tests. The exact
SQLite table-leaf local-payload formula is defined for proof-carrying usable
page sizes: its minimum, maximum, and modulo-based candidate calculation are
executable, and its result is proved not to exceed either the logical payload
or usable page size (and strictly smaller than an overflowing payload). A
proof-carrying table-leaf payload now permits exactly two physical forms: the
entire payload when it fits, or the calculated local prefix followed by a
positive 32-bit first-overflow-page number. The decoder can construct only
well-formed payloads, encoding has a kernel-checked exact-length theorem, and
the inline decoder has a suffix-preserving roundtrip theorem. Executable tests
cover the overflow branch's exact bytes, suffix preservation, and rejection of
page zero; its general kernel roundtrip theorem and the overflow-page chain
codec remain open. Individual raw overflow pages are implemented: their first
word is typed as either the zero end-of-chain sentinel or a positive next-page
reference, and their remaining bytes have exactly the usable overflow
capacity. Both pointer and whole-page codecs have kernel-checked exact-length,
suffix-preserving roundtrip theorems. Proof-carrying multi-page chains reject
duplicate page numbers, derive each physical next pointer from chain order,
and record the used-byte count on the final page. Kernel-checked theorems show
the chain is nonempty, reconstructed page count is exact, every adjacent link
and final sentinel is correct, and reconstructed logical payload length equals
the declared chain size. A resolved table leaf now requires no chain for inline
payloads and exactly one correctly rooted chain for overflowing payloads; its
kernel-checked reconstruction theorem proves local plus overflow bytes have
exactly the payload length announced by the cell. The distinct SQLite maximum
local-payload formula for index pages is also executable and proved to stay
within the logical payload and usable page, including a strict split when an
index payload overflows. Leaf and interior index-cell codecs now implement the
exact payload-size and left-child layouts with proof-carrying inline/overflow
payloads. Their encoded lengths and inline suffix-preserving roundtrips are
kernel checked; executable tests cover both cell variants and an overflowing
index payload. The live Core decoder now resolves table and index cells against
bounded overflow chains. General overflow-branch roundtrip proofs, an
end-to-end decoder/encoder theorem, balancing under localized page mutation,
and page-mutation refinement remain open. A generic
proof-carrying page layout now connects every cell-pointer entry to a concrete
nonempty cell interval, proves each interval begins after the encoded prefix
and ends within the page, and requires all intervals to be pairwise disjoint.
Its interval theorem rules out any byte offset belonging to two disjoint cells.
The layout now materializes an exact-size `Storage.Page`, prioritizing the
verified prefix and unique containing cell and zero-filling free space.
Kernel-checked lookup theorems show every prefix offset returns its prefix byte
and every occupied cell offset returns the corresponding cell byte. A typed
layout layer admits only table cells on table pages and index cells on index
pages, projects them to the disjoint generic intervals, preserves exact cell
count, and uses the same verified page materializer. Bounded typed pages and
bounded overflow chains now compile directly to in-range `Storage.PageWrite`
values; chain write lists are proved nonempty with length equal to page count,
and the standard disk write/read theorem applies to typed pages. A
`VerifiedPageSet` admits only those typed pages/chains and requires distinct
pager ids; the rollback-journal old-or-new crash theorem is specialized to its
concrete write list. Ordinary typed pages are proved not to be page one, while
a `VerifiedDatabasePageSet` requires the dedicated header-bearing first page,
non-first verified pages, and globally distinct pager ids. It too has a
specialized rollback-journal old-or-new theorem. This connects complete
verified physical write sets to the crash model, but not yet to logical SQL
state. A pointer-driven page decoder now reads every declared cell through the
page's required table/index and leaf/interior codec, returning a count-indexed
typed cell list whose cell count is proved equal to the header. Reconstructing
and validating decoded interval/freeblock coverage, a round-tripping logical
database codec, and live-engine integration remain open.

`SQLeanite/DiskFormat.lean` gives the physical pager a complete contiguous
file representation: pages are serialized in pager order with no gaps or
metadata outside the pages. Its decoder consumes exactly the statically known
page count and page size while preserving any trailing input. Kernel-checked
theorems prove decode-after-encode for every disk, injectivity of encoding, and
an exact total length of `pageSize * pageCount`. The verified database-page-set
rollback theorem is lifted through this encoder, so every modeled recovered
file byte string is exactly the old physical file or the fully written new
physical file. A validated geometry decoder derives both pager dimensions
from the first 100 bytes and has its own suffix-preserving roundtrip theorem,
so callers do not need to supply trusted page dimensions. The dynamic image
decoder then consumes exactly that many fixed-size pages. Images whose physical
bytes are proved to begin with their validated header have a whole-image
suffix-preserving roundtrip theorem. Every `VerifiedDatabasePageSet`
materializes such an image: later page writes are proved not to overwrite page
one, and the page-one byte array is proved to begin with the encoded 100-byte
header. Thus verified page sets have an unconditional dynamic whole-file
roundtrip theorem. Successful pager and image decodes also prove the exact
number of bytes consumed. This is still a
theorem about the abstract whole-page crash
model; it neither connects the live logical SQL engine to those pages nor
asserts that a real filesystem implements the modeled write/sync behavior.

## Reproducing the inventory

Run `scripts/lean-verification-audit.sh` from the repository root. The audit fails
if `sorry`, `native_decide`, project axioms, `unsafe`, bare `extern`, or any
`opaque` declaration outside the exact nine-binding host allowlist enters the
Lean library, and prints the current `partial def` inventory.
