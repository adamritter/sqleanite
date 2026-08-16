# SQLeanite

SQLeanite ("sequel-lean-ite") is a research implementation of a
SQLite-compatible database core in Lean 4. Its storage algorithms, executable
semantics, and proofs live in the same codebase; the command-line program uses
the proof-carrying `Core` path rather than a shadow specification.

The project currently builds with Lean 4.19.0 and has no Lake dependencies.
At this snapshot it contains 81,939 lines in 92 library modules, 1,973
theorems/lemmas, 872 explicitly audited headline theorems, and 151 executable
tests. The verification audit reports no `sorry`, `axiom`, `native_decide`,
`unsafe`, or project-local `partial def`.

SQLeanite is not a drop-in replacement for SQLite and is not production-ready.
It deliberately implements a bounded SQL/storage subset so that its claims can
remain precise. See [Trust and scope](docs/TRUST.md) before relying on a result.

## What is verified

- proof-carrying ordered table storage and recursive B+ tree operations;
- SQLite record, page, varint, freelist, rollback-journal, and WAL codecs;
- crash-atomic rollback-journal and abstract concurrency protocols;
- table/index mutation invariants and statement-level refinements;
- three-valued SQL and bag semantics for the supported query algebra;
- sound optimizer rewrites and exact primary/secondary index routing;
- live-path checks that tie the audited theorems to the shipped executable.

The executable can read and write real SQLite-format files within its supported
subset. Tables require exactly one `INTEGER PRIMARY KEY` or `TEXT PRIMARY KEY`;
the latter uses SQLite's hidden-rowid table plus implicit autoindex, including
the literal VeriBetrKV/YCSB `usertable(ycsb_key TEXT PRIMARY KEY, field0 TEXT)`
schema. Values include `NULL`, signed 64-bit `INTEGER`, bounded `TEXT`/`BLOB`,
and finite `REAL`.
Single-column indexes, transactions, common predicates, ordering, grouping,
aggregates, and a bounded join subset are supported. Unsupported SQL is
rejected instead of silently falling back to C SQLite.

## Build and run

Install [elan](https://github.com/leanprover/elan), a C compiler, and
`ripgrep`. The pinned toolchain is selected automatically.

```sh
lake build
lake exe sqleanite_tests
scripts/lean-verification-audit.sh
scripts/live-path-check.sh
```

Create a database using the rollback-journal path:

```sh
printf '%s\n' \
  'CREATE TABLE items(id INTEGER PRIMARY KEY, value TEXT NOT NULL);' \
  "INSERT INTO items VALUES(1, 'hello');" \
  'SELECT * FROM items;' > demo.sql
.lake/build/bin/sqleanite --verified-file demo.db demo.sql
```

This path keeps a pre-created, non-hot journal inode. Ordinary commits sync an
active undo record, the changed database pages, and an inactive marker; the
proved persistent-journal trace avoids per-commit directory operations.

The CLI also exposes `--verified-wal-file` and
`--verified-wal-checkpoint`; run it with `--help` for the exact syntax.

## Repository map

- `SQLeanite/`: implementation, specifications, and proofs;
- `Main.lean`: small file/CLI boundary for the verified core;
- `Tests.lean`: executable regression and interoperability tests;
- `native/`: nine narrow syscall bindings plus a test-only fault VFS;
- `tests/sql/`: differential, workload, and upstream-adapter inputs;
- `mutations/`: proof and C-SQLite mutation experiments;
- `scripts/`: audits, reproduction, benchmarks, and crash tests;
- `docs/`: architecture, trust boundary, results, and case studies.

Current comparative timings are in [docs/BENCHMARKS.md](docs/BENCHMARKS.md).

`Engine.lean` remains a test-only broad SQL conformance fixture. It is not
reachable from the shipped `sqleanite` binary. The live-path audit enforces
that separation.

## Verification and experiments

`scripts/reproduce-all.sh` runs the full public reproduction pipeline.
`QUICK=1` skips the slower mutation and crash sweeps. Comparative C mutation
and focused upstream Tcl runs require a separate clean SQLite checkout:

```sh
SQLITE_SOURCE_DIR=/path/to/sqlite scripts/run-c-mutation-pilot.sh
SQLITE_SOURCE_DIR=/path/to/sqlite scripts/run-focused-upstream.sh select1 insert
```

## Status and non-claims

The verified Core text path now uses a proof-producing lexer and an independent
token-to-AST grammar replay; its text-level semantic and durability theorems
carry that certificate. The strongest localized theorem now covers indexed
mutations in multi-table inline databases, deriving exact post-state bytes and
unchanged-table frames from the live prepared delta. Overflow-changing and
freelist-changing cases use the separately verified bulk/padded path; unifying
those cases under one localized theorem remains open. Other major gaps are an
unconditional refinement from the real OS/filesystem to the modeled VFS and
complete SQLite SQL/file-format coverage. Proofs establish conditional
properties under the documented host contracts; they do not prove Linux,
storage hardware, the Lean compiler/runtime, or the C syscall shim.

SQLeanite is independent research and is not affiliated with the SQLite
project. “SQLite” is used to describe file/protocol compatibility.

## License

SQLeanite is dedicated to the public domain; see [LICENSE.md](LICENSE.md).
