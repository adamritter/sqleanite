# Case study: the SQLite WAL-reset race

In August 2026, Tailscale described a rare SQLite race in
[How we tracked down a 16-year-old SQLite bug](https://tailscale.com/blog/sqlite-wal-reset-bug).
SQLite fixed it in check-in
[`3c7a03032f`](https://sqlite.org/src/info/3c7a03032f): after a checkpointer
acquires its read lock, it now compares the live WAL salt with the header it
read earlier.

## The race

The problematic execution has three steps:

1. A checkpointer remembers an old WAL generation with `mxFrame = 45`.
2. Before it obtains the read lock, a writer resets/wraps the WAL, changes its
   salt, resets `nBackfill` to zero, and commits a new four-frame generation.
3. The checkpointer sees `nBackfill < 45` and copies according to its stale
   45-frame snapshot. The new WAL only has four valid frames.

SQLite's regression test uses fault injection to force this timing. The fixed C
code performs the salt comparison at runtime and skips the stale checkpoint.

## The Lean version

[`WALResetProtocol.lean`](../SQLeanite/WALResetProtocol.lean) models the same
interleaving. `generation` abstracts SQLite's two salt words. A writer may
append frames without changing the generation, but any reset changes it.

The important difference is the API shape:

```lean
structure CopyPlan (view : LockedView snapshot) where
  upperFrame : Nat
  withinLiveWAL : upperFrame ≤ view.mxFrame
```

Checkpoint copying consumes a `CopyPlan`, not an unvalidated integer. The
post-lock generation check is what supplies `withinLiveWAL`: within one
generation the writer protocol proves that the WAL only grows. A reset changes
the generation, so `checkpointPlan?` returns `none`.

The model proves both halves of the example:

- `reported_race_passes_unsafe_test`: the historical `nBackfill` check accepts;
- `reported_race_requests_missing_frames`: 45 exceeds the four live frames;
- `reported_race_rejected`: the generation-indexed plan rejects it;
- `checkpointFrames?_safe`: every frame returned by the fixed decision exists
  in the locked WAL.

## What “caught at compile time” means

The salt comparison still happens at runtime because the race is a runtime
event. Lean checks at compile time that **every branch which returns a copy
plan has enough evidence to stay inside the current generation**. If a
maintainer deletes the post-lock generation check, the program can no longer
construct `withinLiveWAL`; weakening the type instead breaks the general safety
theorem. The included mutation experiment makes that omission turn the build
red.

This is stronger than only reproducing the bad timing in a test: it covers all
states admitted by the model, not just the injected execution. It is also a
conditional result. The proof assumes the writer really changes generation on
reset and only appends within a generation. Connecting those assumptions to a
concrete shared-memory WAL implementation and OS locking primitives would be
additional refinement work.

SQLeanite's current production WAL adapter publishes self-contained WAL images
under a serialized writer lock; it does not implement SQLite's exact in-place
wal-index reset/checkpoint algorithm. Therefore this case study demonstrates
how that algorithm can be designed and reviewed in Lean, not that an otherwise
latent copy of the historical bug was removed from SQLeanite's live code.

