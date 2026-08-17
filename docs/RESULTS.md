# Results snapshot for the paper

One full `scripts/reproduce-all.sh` run, 2026-08-17, exit 0, every step green.
This is the artifact page: each row names the script that reproduces it, so
nothing here is a remembered number. Where a figure is machine-specific it says
so.

Reproduced with:

```sh
SQLITE_SOURCE_DIR=/path/to/sqlite ROWS=2000 scripts/reproduce-all.sh
SQLITE_SOURCE_DIR=/path/to/sqlite scripts/run-c-mutation-pilot.sh
RECORDS=1000 OPS=100 RUNS=3 scripts/run-ycsb-benchmark.sh
scripts/run-proof-latency.sh
```

## Verification inventory

| | | source |
|---|---:|---|
| theorem/lemma declarations | 2,039 | `scripts/lean-manifest.sh` |
| explicitly audited headline theorems | 896 | `SQLeanite/ProofAxioms.lean` |
| library modules | 94 | `scripts/lean-manifest.sh` |
| library lines | 84,486 | `scripts/lean-manifest.sh` |
| `sorry` / project `axiom` / `native_decide` / `unsafe` / `partial def` | 0 / 0 / 0 / 0 / 0 | `scripts/lean-verification-audit.sh` |
| opaque host bindings | 9 (8 syscalls + process liveness) | audit allowlist |
| live-path assertions | 73 / 73 | `scripts/live-path-check.sh` |
| executable tests | 151 | `lake exe sqleanite_tests` |

Every headline theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`; none depends on `sorryAx`, which the live-path check asserts
directly rather than by inspection.

## Compatibility with C SQLite, both directions

| arm | result | source |
|---|---|---|
| Core differential (our writes, both engines read) | 13 cases pass | `run-core-differential-smoke.sh` |
| Reverse (C writes, we read), default matrix | 20 accepted, 3 declared unsupported | `run-reverse-differential.sh` |
| Reverse, full feature x page-size cross | 53 accepted, 3 declared unsupported | `run-reverse-differential.sh --full` |
| Forward (we write, C reads) | 11 / 11 workload shapes, 1 with a declared bounded exception | `run-forward-compat.sh` |
| Page reclamation after an indexed shrink | transient only, does not accumulate over 5 cycles | `regress-page-reclaim.sh` |
| Upstream Tcl `select1` | 191 assertions green | `run-focused-upstream.sh` |

Read page sizes 1024 / 4096 / 8192 / 65536; write 4096 only. `WITHOUT ROWID`,
composite and absent primary keys are checked to fail closed as ordinary
diagnostics. Details, including the two CLI value-rendering differences, are in
[COMPATIBILITY.md](COMPATIBILITY.md).

## Mutation analysis: proofs versus tests, as detection distance

| arm | mutations | compiles / builds | detected | queries executed before detection |
|---|---:|---|---:|---:|
| Lean (proof) | 21 | 0 / 21 build | 21 / 21 | **0** |
| C SQLite (test) | 10 | 10 / 10 compile | 9 / 10 | 1 each |

The asymmetry is the finding, and it is a statement about *where* a defect
surfaces, not about wall-clock speed. Every Lean mutation falsifies a semantic
theorem, so the build fails before a single query runs. Every C mutation compiles
cleanly — the compiler has nothing to check against — and needs an executed
witness; `c-p1-and-as-or` is missed entirely by the bounded witness, which is the
honest failure mode of testing rather than an argument that ours is faster.

Median Lean mutation-to-detection is 1,776 ms (range 970 ms to 19,002 ms, the
tail being mutations that force a wide rebuild); the C arm's median
compile-plus-witness cycle is 8,219 ms (range 8,158 to 8,738). Do not report that
ratio as "proofs are 4.6x faster": the two measure different events, and the Lean
figure is a build while the C figure is a build plus an execution.

## Crash and power loss

| experiment | rounds | old-or-new | torn | corrupt | source |
|---|---:|---:|---:|---:|---|
| crash fault injection (control: stock `sqlite3`) | 25 | 25 | 0 | 0 | `run-crash-injection.sh` |
| power-loss injection (control: stock `sqlite3`) | 20 | 20 | 0 | 0 | `run-powerloss-injection.sh` |
| power-loss **mutation** (`c-p4-skip-journal-sync`, must tear) | 20 | 0 | **20** | 0 | `run-powerloss-mutation.sh` |

The third row is the one that gives the first two meaning: a control that cannot
fail is not a control. Removing the journal sync tears every round, so the
harness demonstrably detects the failure it is looking for.

All three are conditional evidence about a real system. The theorems are
conditional on `SyscallVFS.Contract`; see [TRUST.md](TRUST.md).

## Performance: the twelve public workloads and YCSB, side by side

`ROWS=2000`, all outputs verified equal to C SQLite per case. C SQLite is
`/usr/bin/sqlite3` 3.34.1; times are whole-process wall clock, which is the
honest unit because both are invoked as a CLI.

| workload | SQLeanite | C SQLite | ratio |
|---|---:|---:|---:|
| 02 autocommit inserts (100) | 1,405 ms | 1,153 ms | **1.2x** |
| 05 range scan + predicate | 13 ms | 8 ms | 1.6x |
| 04 indexed lookup (secondary) | 13 ms | 7 ms | 1.9x |
| 03 point lookup by PK | 14 ms | 7 ms | 2.0x |
| 11 cold open + 1 read | 14 ms | 7 ms | 2.0x |
| 09 inner join (2 tables) | 15 ms | 7 ms | 2.1x |
| 01 bulk load (2,000 rows, 1 txn) | 167 ms | 58 ms | 2.9x |
| 12 mixed read/write session | 149 ms | 34 ms | 4.4x |
| 10 read-modify-write txn | 96 ms | 20 ms | 4.8x |
| 07 bulk UPDATE by predicate | 133 ms | 21 ms | 6.3x |
| 08 bulk DELETE by predicate | 138 ms | 20 ms | 6.9x |
| 06 ORDER BY + LIMIT 20 | 53 ms | 7 ms | 7.6x |

Spread 1.2x to 7.6x. Two rows deserve their explanation stated rather than
buried: **bulk UPDATE and bulk DELETE (6.3x, 6.9x) pay an O(index)
decode-and-compare per commit** to admit a page-directed index write with an
exact decoded post-state certificate. That is the price of replacing an opaque
post-image premise with a constructive one, measured at 38 ms per commit at 1,000
index entries and 158 ms at 8,000. See
[BENCHMARK_HISTORY.md](BENCHMARK_HISTORY.md).

### YCSB, VeriBetrKV parameters (one 512-byte field, workloads A/B/C/D/F/Cuniform)

`RECORDS=1000 OPS=100 RUNS=3`. Load and run phases are timed separately because
VeriBetrKV's insertion claim is the load phase alone. A timing is reported only
when both engines produced identical run-phase output; all six did.

| workload | load ratio | run ratio | SQLeanite p50 | SQLeanite p99 |
|---|---:|---:|---:|---:|
| A (50/50 read-update) | 5.5x | **9.7x** | 1.95 ms | 115.40 ms |
| B (95/5 read-update) | 5.7x | **13.6x** | 0.68 ms | 114.11 ms |
| C (read only) | 5.7x | 3.4x | 0.04 ms | 0.10 ms |
| D (read latest) | 5.6x | 3.9x | 0.64 ms | 17.96 ms |
| F (read-modify-write) | 5.8x | **10.0x** | 1.50 ms | 115.87 ms |
| Cuniform (read only, uniform) | 5.5x | 4.0x | 0.04 ms | 0.21 ms |

**Stated plainly: the write-heavy workloads A, B and F run 9.7x to 13.6x C
SQLite, and that is the weakest number in this document.** Read-only C and
Cuniform are 3.4x–4.0x at 0.04 ms p50. The p99 gap on A/B/F is the same
per-commit certificate cost as workloads 07 and 08 above, arriving once per
update rather than amortized. Reporting only the read workloads, or only the
medians, would hide it.

At the exact one-million-row 512-byte load: 220.76 s, 625,565,696 bytes against C
SQLite's 622,739,456 (1.0045x), `integrity_check=ok`, one million rows, 512-byte
minimum and maximum payloads, peak RSS 44.2 GiB. Memory is an engineering
limitation and is not improved by any of this work.

### Scaling shape

Cold reads are flat in database size where a certified page-directed path applies
(12 ms at 250 rows through 4,000 rows for both primary hits and stamped misses),
and open+`ORDER BY` is not (16 ms at 250 rows to 321 ms at 20,000), because that
shape still materializes. Capacity probes pass at 60,000 and 100,000 rows.

## Maintenance cost

`scripts/run-proof-latency.sh`, this machine (166 cores, Lean 4.19.0):

| scenario | elapsed |
|---|---:|
| no-op rebuild | 0.4 s |
| whitespace touch of `CoreEngine.lean` | 386.6 s |
| whitespace touch of `CellPagination.lean` | 386.9 s |
| whitespace touch of `GrowableStorage.lean` | 398.9 s |
| full rebuild from clean | 447.9 s |

The shape here is the finding, and it is not a good one: **a whitespace edit to
any of the three probed modules costs 86-89% of a clean rebuild.** Incremental
compilation is therefore close to no help, because the modules that matter are
imported, directly or transitively, by most of the tree -- `Core` and
`CoreEngine` sit under the codecs, the deltas, the durability layer and
`ProofAxioms`.

The practical consequence for anyone extending this work: expect a ~6.5 minute
proof-check cycle per edit regardless of where the edit is, and budget review
accordingly. Splitting `Core` so that statement semantics and storage
representation do not co-import would be the obvious structural fix, and it is not
attempted here.

## What this snapshot does not show

- the page-local write path, which is proved but not deployed (see
  [TRUST.md](TRUST.md)); no number here includes it;
- the C mutation arm's coverage of storage-level properties, which is thinner
  than P1/P2: 6 of the 10 C mutations are P1 predicate faults;
- any claim about a real filesystem satisfying `SyscallVFS.Contract`;
- progress: every theorem here is conditional on the statement succeeding, so a
  mutant that made every `INSERT` return an error would satisfy all 896 headline
  theorems. That is workstream H and is not done.
