# Architecture

Source modules, fixtures and maintenance scripts stay below 600 lines. The
boundary is enforced by `python3 scripts/check_module_boundaries.py`; CI and
the live-path audit run it. `docs/module-layout.json` maps the former large
modules to responsibility modules and lists their declarations. Existing module
names are compatibility imports; their implementation lives in matching
subdirectories. There is no generated code or include mechanism at build time.

Imports follow declaration dependencies rather than a chain of arbitrary file
segments. In particular, physical decoding does not import SQL execution.
`CoreIndexPrepare.lean` owns index-column resolution, index-name occupancy and
CREATE INDEX admission. `CoreSQL` keeps its existing public adapters and
`CoreDecode` calls the shared module directly. The structural check rejects even
an indirect dependency from the decoder to `CoreSQL` or the legacy `Engine`.

`SQLeaniteTests/` owns executable test responsibilities, shared fixtures and the
ordered registry. `Tests.lean` dispatches the established command-line modes.
The test modules compile at `-O0`, retaining the earlier test-driver build
optimization. Literal `TestData/` modules are split without changing the case
order or content; existing list names concatenate their batches.

`scripts/live-path-check.sh` composes the sourced audits in
`scripts/live-path/`. They share the original failure status and scratch files.
`scripts/lean_sources.py` follows a compatibility module's explicit imports to
provide a logical source view for the existing textual wiring checks. It never
includes unimported sibling files. Axiom audits run all retained print directives
from this view, since merely importing a compiled audit does not replay prints.
`scripts/executable-boundary.sh`, `scripts/popl-parity.sh` and
`scripts/lean-manifest.sh` use the same reader.

For an isolated proof change, build its responsibility module first. Run the
full build, executable tests, verification audit and live-path audit before
committing a completed change. The public process entry and native trust
boundary remain the ones described below.

The shipped path is intentionally a narrow vertical slice:

```text
SQL text
  -> Lexer / Parser / CoreSQL
  -> CoreEngine (proof-carrying Database and Table)
  -> PersistentPageTree / RecursiveBPlusTree
  -> CoreFile or CoreWAL page deltas
  -> rollback journal or WAL codec
  -> SyscallVFS contract
  -> seven C/OS bindings
```

Logical rows are stored in `PersistentPageTree.Store`, not mirrored in a bare
list. Its abstraction function connects local B+ tree mutations to ordered-map
semantics. The file adapters connect those trees to SQLite pages and preserve
stable page identities so point commits need not rebuild the database.

Query proofs use SQLite-style bag semantics and three-valued predicates.
Optimizer and routed-index theorems are connected to the same `Core.Database`
used by the executor. `ProofAxioms.lean` is an executable audit manifest: it
forces important theorem names to remain in the build graph and exposes their
kernel axiom dependencies.

Rollback-journal crash reasoning is pure Lean. It enumerates crash outcomes in
which pending writes may survive in subsets and permutations, and proves the
protocol recovers the old or new committed state under its VFS assumptions.
The concrete file boundary then implements the planned ordering through the
narrow syscall shim. That final implementation and the host filesystem remain
trusted and are listed in `TRUST.md`.

The broad `Engine.lean` interpreter covers much more SQL and supplies 98 of the
conformance-style tests, but it is a fixture, not a production fallback. The
`sqleanite` executable imports `CoreRuntime`, and the live-path audit prevents a
quiet return to the legacy path.


BEFORE INSERT has separate input and rowid phases in `CoreTriggerProgram`.
`InsertBefore` computes ordinary registers in physical column order and builds
the actual typed NEW image before constraints. `InputRegisters` retains reached
scalar-subquery registers while leaving surrounding counters executable; CASE
base copies and IN sources retain their separate evaluation rules. The point
write evaluates the remaining rowid expression after programs and allocates an
automatic rowid from the actual current table. Matching multi-VALUES inputs are
materialized before programs. These transient registers never change records.

Nested INSERT body statements pass lexical caller frames through `ScopedExecutor`
to the same row input path. Input reads use those frames; newly invoked programs
receive fresh event-specific OLD/NEW frames. A body INSERT without matching
programs still uses this input path to preserve selected values and subtypes.
Single VALUES skips discarded expressions, while streaming multiple source rows
evaluate all source fields and matching programs cause source materialization.

`CoreTriggerControl` owns the live `recursive_triggers` connection setting and
its ordinary PRAGMA virtual-table read. Actual program entry increments
`triggerDepth`, checks the pinned 1000-frame limit and restores the caller's
depth, including a false WHEN. Recursive preparation still compiles each active
program once; runtime admission follows the live flag. Structural executor fuel
is a separate implementation bound, not the semantic trigger depth check.

`CoreTriggerProgram.Replacement` obtains the actual accepted candidate and
victims from a pure point preflight, discarding that state. Real DELETE programs
run on the pending database before the actual REPLACE write. Auxiliary deletion
counts are excluded while body writes remain. INSERT keeps the already allocated
key. UPDATE retains its complete typed register image and original SET footprint
through an explicit `PointExecutor` input and the existing RowPreparation path;
no temporary database mutation substitutes for those registers. User RETURNING
runs in its actual post-deletion phase, with private projection context restored.

`SQLite.TriggerRaise` specializes certified RAISE(ABORT, expression) nodes only
in an actual trigger-program context. Ordinary scalar preparation and lazy
execution still bind/evaluate the message. The private executable name is
rejected by the public token matcher. Trigger-body binding specializes before
name validation; preparation uses its explicit OLD/NEW frames as the program
context. Native message conversion includes NULL and the first NUL boundary.
Errors still use Except String: failed-statement file atomicity is tested, while
same-connection post-error counter retention and other RAISE controls remain
separate open work and are not implied by those file comparisons.

`CoreTriggerProgram.Effects` uses the standard pure EStateM carrier to retain
runtime state on error. Successful body statements update that context, and
program unwinding restores caller frame registers on both success and failure.
`CoreDerivedSQL.executeStatementEffects` returns either success data/results or
the error with restored statement data and actual connection effects. The old
Except adapter remains for failure-closing callers. The new native continuation
regressions call the actual state-carrying API through a test-only transport;
they are reported separately from public file-mode comparisons.

Point capture now contains only the accepted row image and its metadata. User
RETURNING is evaluated afterwards from those typed registers and the actual
current database, before AFTER programs. A RETURNING error therefore retains
the point's actual rowid while ABORT restores its logical data. Real program
frames mark schema-program reads; an ordinary RETURNING correlation frame does
not by itself become a trigger context. Wider non-trigger error effects and
other error control classes still require separate coverage/implementation.

Ordinary DML now validates before marking execution started, so preparation
failures retain the preceding changes count while runtime failures set zero.
RETURNING selects the common point/output path even without user triggers. Its
multiple VALUES/coroutine inputs are materialized before writes, matching the
pinned native internal RETURNING program behavior.

`ReturnPrepare` reuses the actual prepared scalar-query context, including
captured source scopes and affinities, while enforcing RETURNING-specific
wildcard/aggregate/width checks. No dummy query callback or fabricated value is
used. `CoreScalarQuery.Result.preparedContext` is compiler metadata only; actual
outputs compile/evaluate in the current post-point read state. RETURNING also
permits RAISE while retaining ordinary direct-query permissions. The temporary
raiseContext flag is separate from schemaProgram and is not persisted by reads.

`ForeignEarly` represents the native single-write immediate-FK INSERT branch.
Eligibility is captured from original input shape before SELECT/VALUES lowering.
Root single VALUES with no RETURNING/program/replacement path checks child
parent lookups on the actual checked candidate before executing the point.
NULL and matching self-referencing NEW keys remain valid. A later parent scan
cannot cancel that early failure against an old orphan. The pure candidate
preflight is discarded; other statement shapes retain signed counter handling.


`InputEffects.requiresInputEffects` retains actual per-point connection states
for ordinary multiple VALUES and recognized VALUES-coroutine SELECT inputs, including statements
without FK checks, user programs or RETURNING. A later input/constraint error
can restore logical data while preserving last_insert_rowid from a completed
point. This uses the common input streaming/materialization and point executor;
preparation still completes before execution starts.
