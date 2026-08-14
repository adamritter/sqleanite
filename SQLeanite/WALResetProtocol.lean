import Std

/-!
# WAL-reset generation safety

This is a small model of the SQLite WAL checkpoint/reset race described by
Tailscale in 2026 and fixed by SQLite check-in `3c7a03032f`.

A checkpointer first remembers `(generation, mxFrame)`. Before it obtains the
read lock, a writer may reset the WAL to a new generation containing fewer
frames. Looking only at `nBackfill` can then authorize copying the remembered
old frame range out of the new, shorter WAL.

`LockedView.sameGenerationMonotone` records the writer invariant that a WAL
only grows while its generation is unchanged. A `CopyPlan` carries the derived
bound on every frame it may read. The only constructor exposed here checks the
generation after the lock is held. Consequently a reset produces `none`, and
every produced frame number belongs to the current WAL.
-/

namespace SQLeanite.WALResetProtocol

/-- Header fields retained by a checkpointer before it acquires its read lock.
`generation` abstracts SQLite's pair of WAL salt words. -/
structure Snapshot where
  generation : Nat
  mxFrame : Nat
  deriving DecidableEq, Repr

/-- What the checkpointer observes after acquiring the read lock.

The proof field is the protocol invariant supplied by the writer transition:
within one generation, frames are appended and never removed. A reset may make
the WAL shorter, but must change the generation, so the implication is then
vacuously true. -/
structure LockedView (snapshot : Snapshot) where
  generation : Nat
  mxFrame : Nat
  nBackfill : Nat
  sameGenerationMonotone :
    snapshot.generation = generation → snapshot.mxFrame ≤ mxFrame

/-- No writer changed the WAL between the snapshot and the read lock. -/
def unchanged (snapshot : Snapshot) (nBackfill : Nat) :
    LockedView snapshot where
  generation := snapshot.generation
  mxFrame := snapshot.mxFrame
  nBackfill := nBackfill
  sameGenerationMonotone := fun _ => Nat.le_refl _

/-- A writer appended frames without resetting the WAL generation. -/
def appended (snapshot : Snapshot) (additional nBackfill : Nat) :
    LockedView snapshot where
  generation := snapshot.generation
  mxFrame := snapshot.mxFrame + additional
  nBackfill := nBackfill
  sameGenerationMonotone := by
    intro _
    omega

/-- A writer wrapped the WAL and started a shorter, fresh generation. -/
def reset (snapshot : Snapshot) (newFrames : Nat) : LockedView snapshot where
  generation := snapshot.generation + 1
  mxFrame := newFrames
  nBackfill := 0
  sameGenerationMonotone := by
    intro impossible
    omega

/-- The incomplete admission test used by the historical race: after a reset,
`nBackfill` is zero, so an old positive `mxFrame` looks eligible. -/
def unsafeAdmits (snapshot : Snapshot) (view : LockedView snapshot) : Prop :=
  view.nBackfill < snapshot.mxFrame

instance (snapshot : Snapshot) (view : LockedView snapshot) :
    Decidable (unsafeAdmits snapshot view) := by
  unfold unsafeAdmits
  infer_instance

/-- A copy request can only be constructed together with a proof that its
entire one-based frame range exists in the currently locked WAL. -/
structure CopyPlan {snapshot : Snapshot} (view : LockedView snapshot) where
  upperFrame : Nat
  withinLiveWAL : upperFrame ≤ view.mxFrame

/-- The fixed protocol rechecks the live generation after acquiring the lock.
The writer invariant turns that equality into the required frame bound. -/
def checkpointPlan? (snapshot : Snapshot) (view : LockedView snapshot) :
    Option (CopyPlan view) :=
  if generation : snapshot.generation = view.generation then
    some {
      upperFrame := snapshot.mxFrame
      withinLiveWAL := view.sameGenerationMonotone generation
    }
  else
    none

/-- One-based WAL frame numbers requested by a checked plan. -/
def CopyPlan.frames {snapshot : Snapshot} {view : LockedView snapshot}
    (plan : CopyPlan view) : List Nat :=
  (List.range plan.upperFrame).map Nat.succ

theorem CopyPlan.frames_positive {snapshot : Snapshot}
    {view : LockedView snapshot} (plan : CopyPlan view) {frame : Nat}
    (member : frame ∈ plan.frames) : 0 < frame := by
  simp only [CopyPlan.frames, List.mem_map] at member
  obtain ⟨index, _, rfl⟩ := member
  omega

/-- The central safety property: every authorized read is within the current
WAL, regardless of how many frames a same-generation writer appended. -/
theorem CopyPlan.frames_within_live {snapshot : Snapshot}
    {view : LockedView snapshot} (plan : CopyPlan view) {frame : Nat}
    (member : frame ∈ plan.frames) : frame ≤ view.mxFrame := by
  simp only [CopyPlan.frames, List.mem_map] at member
  obtain ⟨index, inRange, rfl⟩ := member
  have belowUpper : index < plan.upperFrame := List.mem_range.mp inRange
  have upperBound := plan.withinLiveWAL
  omega

/-- The executable checkpoint decision returns frame lists only after building
a proof-carrying plan. -/
def checkpointFrames? (snapshot : Snapshot) (view : LockedView snapshot) :
    Option (List Nat) :=
  (checkpointPlan? snapshot view).map CopyPlan.frames

theorem checkpointFrames?_safe {snapshot : Snapshot}
    {view : LockedView snapshot} {frames : List Nat}
    (approved : checkpointFrames? snapshot view = some frames) :
    ∀ frame ∈ frames, frame ≤ view.mxFrame := by
  unfold checkpointFrames? at approved
  cases planEq : checkpointPlan? snapshot view with
  | none => simp [planEq] at approved
  | some plan =>
      rw [planEq] at approved
      change some plan.frames = some frames at approved
      have framesEq : plan.frames = frames := Option.some.inj approved
      intro frame member
      rw [← framesEq] at member
      exact plan.frames_within_live member

theorem checkpointPlan?_reset_eq_none (snapshot : Snapshot) (newFrames : Nat) :
    checkpointPlan? snapshot (reset snapshot newFrames) = none := by
  simp [checkpointPlan?, reset]

theorem checkpointFrames?_reset_eq_none (snapshot : Snapshot) (newFrames : Nat) :
    checkpointFrames? snapshot (reset snapshot newFrames) = none := by
  simp [checkpointFrames?, checkpointPlan?_reset_eq_none]

/-! ## The concrete interleaving from the reported SQLite bug -/

/-- The old WAL was fully checkpointed through frame 45. -/
def reportedSnapshot : Snapshot := { generation := 7, mxFrame := 45 }

/-- A concurrent writer reset it and committed only four frames. -/
def reportedReset : LockedView reportedSnapshot := reset reportedSnapshot 4

/-- The old test based on `nBackfill` alone authorizes the stale snapshot. -/
theorem reported_race_passes_unsafe_test :
    unsafeAdmits reportedSnapshot reportedReset := by
  decide

/-- That stale request reaches beyond the live four-frame WAL. -/
theorem reported_race_requests_missing_frames :
    reportedReset.mxFrame < reportedSnapshot.mxFrame := by
  decide

/-- The generation-indexed protocol rejects the same interleaving. -/
theorem reported_race_rejected :
    checkpointFrames? reportedSnapshot reportedReset = none := by
  exact checkpointFrames?_reset_eq_none _ _

end SQLeanite.WALResetProtocol
