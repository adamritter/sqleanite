import SQLeanite.DiskFormat

namespace SQLeanite
namespace Durability

open Storage

/-- The proof obligation for connecting a logical state to fixed-size pages.
An SQLite file-format implementation must supply this round-trip theorem; the
durability argument does not assume an unverified decoder. -/
structure FixedDiskCodec (State : Type) (pageSize pageCount : Nat) where
  encode : State → Disk pageSize pageCount
  decode : Disk pageSize pageCount → Option State
  decode_encode : ∀ state, decode (encode state) = some state

/-- Recovery for the legacy fixed-geometry model followed by its decoder. -/
def recoverFixedState (codec : FixedDiskCodec State pageSize pageCount)
    (recoveredMain : Disk pageSize pageCount)
    (recoveredJournal : Option (Disk pageSize pageCount)) : Option State :=
  codec.decode (recoverWithJournal recoveredMain recoveredJournal)

/-- The page-level rollback-journal theorem lifts to any logical state with a
round-tripping codec. The only transaction-specific premise is that applying
the staged writes to the old encoding produces the new encoding. -/
theorem rollbackCommit_logical_crash_atomic
    (codec : FixedDiskCodec State pageSize pageCount)
    (old new : State) (writes : List (PageWrite pageSize pageCount))
    (phase : CommitPhase) (recoveredMain : Disk pageSize pageCount)
    (recoveredJournal : Option (Disk pageSize pageCount))
    (writesEncodeNew : applyWrites (codec.encode old) writes = codec.encode new)
    (outcome : JournaledCrashOutcome
      (rollbackCommitState (codec.encode old) writes phase)
      recoveredMain recoveredJournal) :
    recoverFixedState codec recoveredMain recoveredJournal = some old ∨
      recoverFixedState codec recoveredMain recoveredJournal = some new := by
  have diskAtomic := rollbackCommit_crash_atomic (codec.encode old) writes phase
    recoveredMain recoveredJournal outcome
  rcases diskAtomic with recoveredOld | recoveredNew
  · left
    simp only [recoverFixedState, recoveredOld, codec.decode_encode]
  · right
    rw [recoverFixedState, recoveredNew, writesEncodeNew, codec.decode_encode]

/-- The fixed-geometry codec obligation is impossible at zero pages for *any*
state type with two distinguishable values: there is exactly one zero-page
disk, so `encode` cannot be injective. Stated generically rather than for one
database type, which both strengthens it and keeps this module below `Core` in
the import graph. The growable codec used by the verified core must therefore
target a dependent database image. -/
theorem no_fixed_codec_at_zero {State : Type} (left right : State)
    (different : left ≠ right) (pageSize : Nat) :
    FixedDiskCodec State pageSize 0 → False := by
  intro codec
  have encodedEqual : codec.encode left = codec.encode right := by
    cases encodedLeft : codec.encode left with
    | mk readLeft =>
        cases encodedRight : codec.encode right with
        | mk readRight =>
            congr
            funext pageId
            exact Fin.elim0 pageId
  have decodedEqual := congrArg codec.decode encodedEqual
  rw [codec.decode_encode left, codec.decode_encode right] at decodedEqual
  exact different (Option.some.inj decodedEqual)

theorem rollbackCommit_state_crash_atomic {State : Type}
    (codec : FixedDiskCodec State pageSize pageCount)
    (old new : State) (writes : List (PageWrite pageSize pageCount))
    (phase : CommitPhase) (recoveredMain : Disk pageSize pageCount)
    (recoveredJournal : Option (Disk pageSize pageCount))
    (writesEncodeNew : applyWrites (codec.encode old) writes = codec.encode new)
    (outcome : JournaledCrashOutcome
      (rollbackCommitState (codec.encode old) writes phase)
      recoveredMain recoveredJournal) :
    recoverFixedState codec recoveredMain recoveredJournal = some old ∨
      recoverFixedState codec recoveredMain recoveredJournal = some new :=
  rollbackCommit_logical_crash_atomic codec old new writes phase recoveredMain
    recoveredJournal writesEncodeNew outcome

/-- A satisfiable codec targets a database image whose page count comes from
the encoded state. `Equiv` permits future state representations such as REAL
bit patterns without adding axioms about opaque runtime floats. -/
structure DiskCodec (State : Type) where
  Equiv : State → State → Prop
  encode : State → DiskFormat.DatabaseImage
  decode : DiskFormat.DatabaseImage → Option State
  decode_encode : ∀ state, ∃ decoded,
    decode (encode state) = some decoded ∧ Equiv decoded state

end Durability
end SQLeanite
