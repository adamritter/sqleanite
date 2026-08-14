# C mutations requiring specialized witnesses

These compile and were pre-registered, but the original completing-execution
witness could not distinguish them from stock SQLite, even under an aggressive
probe: WAL mode, 2,000 rows, deletes, close, reopen, `integrity_check`, and
main/WAL file sizes. A dedicated power-loss witness now detects the rollback-
journal ordering mutation; the remaining cases are still held out.

They are held here rather than counted, because two very different situations
produce the same evidence and this harness cannot tell them apart:

1. **Dead mutation** — the edited code is not reached, or a later computation
   overwrites it. `c-p3-balance-drop-cell` decrements `cntNew[i]` inside a loop
   that may recompute it, so this is plausible.
2. **Live but crash-only** — the mutation changes only the durability ordering,
   which no completing run can reveal. `c-p4-skip-journal-sync` removes the
   `syncJournal` before `pager_write_pagelist`: every non-crashing run is
   correct by construction.

Counting these as "missed by testing" would overstate the benchmark — it would
credit the proof arm for bugs that may not exist. Counting them as dead would
understate it. Settling them requires fault injection matched to the affected
recovery mechanism.

Until then they were excluded from every reported figure.

## Process-crash injection cannot settle durability ordering

`scripts/run-crash-injection.sh` kills the writer at 25 randomised points inside a
4,000-row transaction, reopens, and requires `integrity_check = ok` with a row
count that is either the old state or the new one. Stock SQLite passes 25/25,
so the harness works and the control is meaningful.

Run against the held-out mutants, all still pass 25/25. That is **not** evidence
the mutations are dead, because of a structural limit:

> `SIGKILL` terminates the process but leaves the operating system page cache
> intact, so writes that were issued without an `fsync` still reach the disk.
> Process-kill injection therefore cannot observe a missing or misordered
> durability barrier at all.

Detecting `c-p4-skip-journal-sync` needs simulated **power loss**: a VFS shim
that discards unsynced writes on crash, which is how SQLite's own suite tests
this. `native/powerloss-vfs.c` now provides that missing test-only boundary. It
buffers rollback-journal and main-file writes, then at the first main-file
sync persists a seeded subset and terminates the writer.

`scripts/run-powerloss-injection.sh` establishes the control: stock SQLite
recovered an integral old or new database in 20/20 deterministic rounds.
`scripts/run-powerloss-mutation.sh` builds the held-out mutation in an isolated
worktree and runs the identical oracle. The mutant produced a partial commit in
20/20 rounds (alternating 73 and 240 new rows out of 2,000), so the removed
journal durability barrier is now observably live.

The current classification is:

| Mutation | Status |
|---|---|
| `c-p4-skip-journal-sync` | **detected 20/20** by the power-loss VFS; partial commit after reopen |
| `c-p4-journal-header-size` | affects rollback bookkeeping only; unobservable here |
| `c-p5-wal-frame-no-commit`, `c-p5-wal-bad-checksum` | affect WAL recovery only; unobservable here |
| `c-p3-balance-drop-cell` | probably genuinely dead -- `cntNew[i]` is recomputed by the balancer |

**This is the sharpest result in the benchmark.** For the durability-ordering
class, the C arm needs a device-level power-loss simulator to see the fault at
all, while the matched Lean mutation `p4-main-before-journal-sync` is rejected
at proof time in 1.1 seconds having executed zero queries. The comparison is not
"testing was unlucky"; it is that a completing execution contains no evidence
of the fault. The VFS and its oracle are unverified benchmark code, so this is a
focused detection result, not part of the verified core or its TCB claim.
