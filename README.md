# SQLeanite

SQLeanite ("sequel-lean-ite") is a research implementation of a
SQLite-compatible database core in Lean 4. Its storage algorithms, executable
semantics, and proofs live in the same codebase; the command-line program uses
the proof-carrying `Core` path rather than a shadow specification.

The project currently builds with Lean 4.35.0 and has no Lake dependencies.
The current suite passes all 182 executable tests and audits all
992 registered headline theorems. The verification audit reports no `sorry`,
`axiom`, `native_decide`, `unsafe`, or project-local `partial def`.
Generate current source counts and theorem dependencies with
`scripts/lean-manifest.sh`.

SQLeanite is not a drop-in replacement for SQLite and is not production-ready.
It deliberately implements a bounded SQL/storage subset so that its claims can
remain precise. See [Trust and scope](docs/TRUST.md) before relying on a result.

The ongoing [SQLite C-to-Lean port](docs/SQLITE_PORT.md) now includes the scalar
numeric layer, the original binary/decimal conversion algorithms, default
17-digit REAL formatting, CAST, conditional expressions, SELECT without FROM,
stored column affinity on writes, record reads and supported comparisons,
and 18 text/blob and scalar function names including `substr`, `replace`,
`unhex`, `unicode` and multi-argument `min`/`max`, plus row-dependent SELECT
projections using the same scalar evaluator and explicit column affinity.
The direct-column query path now applies LIMIT after stable duplicate removal;
remaining numeric DISTINCT differences are recorded in the port report.
SQL and storage run through the production Lean Core path without SQLite FFI;
the existing native shim only handles OS file operations and process liveness.
The port report distinguishes proved properties, differential evidence and
the substantial SQLite functionality that remains unported.

## What is verified

- proof-carrying ordered table storage and recursive B+ tree operations;
- SQLite record, page, varint, freelist, rollback-journal, and WAL codecs;
- crash-atomic rollback-journal and abstract concurrency protocols;
- table/index mutation invariants and statement-level refinements;
- three-valued SQL and bag semantics for the supported query algebra, on both
  sides: a `SELECT` denotes a bag query and an `INSERT` denotes bag union with a
  singleton, through one shared abstraction;
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

## Related work

Two papers set the targets this project measures itself against, and the two
sections after this one state exactly where it matches them and where it does not.

- **Malecha, Morrisett, Shinnar and Wisnesky, "Toward a verified relational
  database management system", POPL 2010.**
  [doi:10.1145/1707801.1706329](https://doi.org/10.1145/1707801.1706329) —
  the relational-algebra target. Six primitives verified in Coq over finite
  *sets*. Per-primitive witnesses for the corresponding theorems here are in
  [docs/PARITY.md](docs/PARITY.md); the difference in target (bags with
  three-valued predicates, not sets) is stated below and is an improvement in
  difficulty, never parity.
- **Chen, Ziegler, Chajed, Chlipala, Kaashoek and Zeldovich, "Using Crash Hoare
  logic for certifying the FSCQ file system", SOSP 2015.**
  [doi:10.1145/2815400.2815402](https://doi.org/10.1145/2815400.2815402) — the
  durability target. The crash theorems here have the same shape (every commit
  checkpoint, every modeled crash outcome, recovery proved old-or-new) and the
  same essential caveat: the result is conditional on a storage model, described
  in [docs/TRUST.md](docs/TRUST.md).

One more supplies the performance comparison's parameters rather than a
verification target:

- **Hance, Lattuada, Hawblitzel, Howell, Johnson and Parno, "Storage systems are
  distributed systems (so verify them that way!)", OSDI 2020.**
  [usenix.org/conference/osdi20/presentation/hance](https://www.usenix.org/conference/osdi20/presentation/hance)
  — VeriBetrKV. `scripts/run-ycsb-benchmark.sh` follows its YCSB parameters (one
  512-byte field, the A/B/C/D/F/Cuniform set, load and run phases timed
  separately) so the numbers in [docs/RESULTS.md](docs/RESULTS.md) are comparable
  to published ones rather than to a private harness.

## Relation to the POPL'10 verified RDBMS: bags, not sets

The nearest prior verified relational engine (Malecha et al., POPL 2010) verifies
six relational primitives over finite **sets**: no duplicates, no NULL logic.
SQLeanite's relations are **bags** — a multiplicity function `Row -> Nat` — under
SQLite's three-valued predicates, where `UNKNOWN` contributes zero multiplicity
rather than collapsing into false.

That is a strictly harder target and it must be stated as an improvement in
target, never as parity: duplicate-sensitive operators are distinct theorems
here, every operator theorem preserves multiplicity rather than membership, and a
rewrite that is sound over sets can be unsound over bags — which is why the live
optimizer selects only rewrites carrying a cost certificate, and why one rewrite
has a proved *negative* result.

Per-primitive witnesses are in [POPL'10 parity](docs/PARITY.md), generated from
the audited theorem set by `scripts/popl-parity.sh` and gated so it cannot drift.

## Relation to FSCQ: the durability theorem, not the evaluation

The crash-atomicity results here are FSCQ-shaped — `executeText_commit_crash_atomic`
and its family quantify over every commit checkpoint and every modeled crash
outcome, and recovery is proved to yield the old or the new database and never an
intermediate one. Two statements bound that comparison, and both matter:

1. **The durability claim is conditional on `SyscallVFS.Contract`.** No project
   axiom asserts that a particular kernel, filesystem or device satisfies it, so
   syscall, filesystem, device-cache and directory-durability behaviour stay in
   the documented TCB. See [Trust and scope](docs/TRUST.md). A crash theorem is
   only as strong as the storage model it quantifies over, and ours is a model.
2. **FSCQ's evaluation does not transfer, and is not being claimed.** FSCQ is
   evaluated as a filesystem — xv6 builds, a mail server, comparison against
   ext4 — which says nothing about a database's operation mix. The FSCQ
   comparison here is about the *shape of the durability theorem*; YCSB is about
   *performance comparability* with a production engine. Conflating the two would
   claim an evaluation nobody ran.

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
- `docs/`: architecture, trust boundary, results, and case studies. Four of these
  are generated and gated so they cannot drift: [`PARITY.md`](docs/PARITY.md)
  (POPL'10 witnesses), [`COMPATIBILITY.md`](docs/COMPATIBILITY.md) (what is
  accepted, rejected and untested in both directions),
  [`BOUNDARY.md`](docs/BOUNDARY.md) (where the proofs stop on the shipped path),
  and `manifest.json` (theorem, trust and parity counts).

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

Paper-facing numbers, from one full reproduction run, are in
[docs/RESULTS.md](docs/RESULTS.md).
