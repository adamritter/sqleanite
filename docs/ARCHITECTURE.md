# Architecture

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

