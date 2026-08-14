# Lean mutation benchmark

Run with:

```sh
LAKE_BIN=lake scripts/run-lean-mutations.sh
```

The registry is committed before execution. Each patch introduces a named
semantic defect, the runner rebuilds the project, and the source is restored
exactly from Git before the next mutation. Generated logs are intentionally
ignored; `results.tsv` is the machine-readable summary.

## Current result

| Metric | Result |
|---|---:|
| Registered Lean mutations | 22 |
| Rejected by build/proof checking | 22/22 |
| Queries executed before detection | 0 |
| Median mutation-to-detection | 1,555 ms |
| Mean mutation-to-detection | 3,029 ms |

The suite covers optimizer and three-valued logic rewrites, live index
planning, B+ tree split/merge/order defects, rollback-journal ordering and
recovery, WAL publication/locking, and the WAL-reset generation race.

The WAL-reset mutation replaces the post-lock generation comparison with the
historically insufficient `nBackfill` test. It fails in 652 ms because Lean can
no longer construct `CopyPlan.withinLiveWAL`. No injected schedule or query is
needed to discover the omission.

## Interpretation

Most mutations directly falsify a semantic theorem. One B+ tree mutation is
rejected even earlier because a proof-carrying constructor cannot be filled.
The `p4-commit-without-delete-sync` mutation remains a useful specification
audit: the broad old-or-new crash theorem permits recovery of old state at that
checkpoint, while the stronger committed-phase theorem rules it out. Raw build
failure is therefore reported separately from any claim that every failed
proof has equal semantic strength.

The C comparison arm is in `c-results.tsv`. It applies preregistered patches to
a separate checkout supplied through `SQLITE_SOURCE_DIR`, compiles each mutant,
and executes a bounded witness. The C compiler accepts these semantic faults;
detection requires an executed query or crash schedule. This comparison is
about detection distance and coverage, not a claim that Lean always reports a
defect faster in wall-clock time.
