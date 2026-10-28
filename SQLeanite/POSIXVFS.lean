import SQLeanite.GrowableStorage.BuildUndoRecordExact

namespace SQLeanite
namespace POSIXVFS

/-!
# Explicit POSIX-like VFS refinement model

This model separates journal file-data durability from directory-entry
durability.  It does not assert that a host filesystem implements the model;
`Contract` is the obligation a concrete adapter must discharge.
-/

structure TempJournalCache (pageSize : Nat) where
  durable : Option (GrowableStorage.Journal pageSize) := none
  pending : Option (GrowableStorage.Journal pageSize) := none

def TempJournalCache.write (cache : TempJournalCache pageSize)
    (journal : GrowableStorage.Journal pageSize) : TempJournalCache pageSize :=
  { cache with pending := some journal }

def TempJournalCache.sync (cache : TempJournalCache pageSize) :
    TempJournalCache pageSize :=
  match cache.pending with
  | none => cache
  | some journal => { durable := some journal, pending := none }

structure State (pageSize : Nat) where
  main : GrowableStorage.Cache pageSize
  journalTemp : TempJournalCache pageSize := {}
  /-- This is a cache for the durable/pending directory entry and its immutable,
  already-synced journal contents. -/
  journalName : GrowableStorage.JournalCache pageSize := {}

def State.initial (old : GrowableStorage.Image pageSize) : State pageSize :=
  { main := { durable := old } }

def State.abstract (state : State pageSize) :
    GrowableStorage.JournaledState pageSize :=
  { main := state.main, journal := state.journalName }

inductive Request (pageSize : Nat) where
  | readMain (pageId : Nat)
  | pwriteMain (write : GrowableStorage.PageWrite pageSize)
  | fdatasyncMain
  | writeJournalTemp (journal : GrowableStorage.Journal pageSize)
  | fdatasyncJournalTemp
  | renameJournal
  | unlinkJournal
  | fsyncDirectory
  /-- Rewrite the already-durable persistent journal inode.  Unlike
  `renameJournal`, this changes file contents without changing a directory
  entry. -/
  | writePersistentJournal
      (journal : Option (GrowableStorage.Journal pageSize))
  | fdatasyncPersistentJournal

inductive Response (pageSize : Nat) where
  | page (value : Storage.Page pageSize)
  | unit

/-- Deterministic reference transition. `renameJournal` publishes only data
which has already crossed the journal-file sync barrier. -/
def modelStep (state : State pageSize) (request : Request pageSize) :
    State pageSize :=
  match request with
  | .readMain _ => state
  | .pwriteMain write => { state with main := state.main.write write }
  | .fdatasyncMain => { state with main := state.main.sync }
  | .writeJournalTemp journal =>
      { state with journalTemp := state.journalTemp.write journal }
  | .fdatasyncJournalTemp =>
      { state with journalTemp := state.journalTemp.sync }
  | .renameJournal =>
      match state.journalTemp.durable with
      | none => state
      | some journal =>
          { state with journalName := state.journalName.write (some journal) }
  | .unlinkJournal =>
      { state with journalName := state.journalName.write none }
  | .fsyncDirectory =>
      { state with journalName := state.journalName.sync }
  | .writePersistentJournal journal =>
      { state with journalName := state.journalName.write journal }
  | .fdatasyncPersistentJournal =>
      { state with journalName := state.journalName.sync }

def runPlan : State pageSize → List (Request pageSize) → State pageSize
  | state, [] => state
  | state, request :: requests => runPlan (modelStep state request) requests

def commitPlan (old : GrowableStorage.Image pageSize)
    (writes : List (GrowableStorage.PageWrite pageSize)) :
    List (Request pageSize) :=
  let journal := GrowableStorage.makeJournal old writes
  [.writeJournalTemp journal, .fdatasyncJournalTemp, .renameJournal,
    .fsyncDirectory] ++ writes.map Request.pwriteMain ++
    [.fdatasyncMain, .unlinkJournal, .fsyncDirectory]

/-- Recurrent commit plan for a journal inode whose inactive state was made
durable when the database was created (or during one-time migration).  It is
the same abstract rollback protocol as `commitPlan`, but file contents—not
directory entries—publish and retire the journal. -/
def persistentCommitPlan (old : GrowableStorage.Image pageSize)
    (writes : List (GrowableStorage.PageWrite pageSize)) :
    List (Request pageSize) :=
  let journal := GrowableStorage.makeJournal old writes
  [.writePersistentJournal (some journal), .fdatasyncPersistentJournal] ++
    writes.map Request.pwriteMain ++
      [.fdatasyncMain, .writePersistentJournal none,
        .fdatasyncPersistentJournal]

theorem runPlan_pwriteMain_append (state : State pageSize)
    (writes : List (GrowableStorage.PageWrite pageSize))
    (requests : List (Request pageSize)) :
    runPlan state (writes.map Request.pwriteMain ++ requests) =
      runPlan { state with main := state.main.writeAll writes } requests := by
  induction writes generalizing state with
  | nil => simp [runPlan, GrowableStorage.Cache.writeAll]
  | cons write writes induction =>
      simp only [List.map_cons, List.cons_append, runPlan, modelStep]
      rw [induction]
      congr 2
      simp [GrowableStorage.Cache.writeAll, GrowableStorage.Cache.write,
        List.append_assoc]

/-- The POSIX-like sequence, including both directory syncs, refines exactly
the committed checkpoint of the page-level rollback protocol. -/
theorem run_commitPlan (old : GrowableStorage.Image pageSize)
    (writes : List (GrowableStorage.PageWrite pageSize)) :
    (runPlan (State.initial old) (commitPlan old writes)).abstract =
      GrowableStorage.rollbackCommitState old writes .committed := by
  unfold commitPlan
  simp only [List.cons_append, List.nil_append, runPlan, modelStep,
    TempJournalCache.write, TempJournalCache.sync]
  rw [runPlan_pwriteMain_append]
  simp [runPlan, modelStep, State.initial, State.abstract,
    GrowableStorage.rollbackCommitState,
    GrowableStorage.JournaledState.initial,
    GrowableStorage.JournaledState.writeJournal,
    GrowableStorage.JournaledState.syncJournal,
    GrowableStorage.JournaledState.stageMainWrites,
    GrowableStorage.JournaledState.syncMain,
    GrowableStorage.JournaledState.deleteJournal,
    GrowableStorage.Cache.writeAll, GrowableStorage.Cache.write,
    GrowableStorage.JournalCache.write, GrowableStorage.JournalCache.sync]

/-- The persistent-inode sequence refines the identical committed checkpoint
without relying on a directory operation during the transaction. -/
theorem run_persistentCommitPlan (old : GrowableStorage.Image pageSize)
    (writes : List (GrowableStorage.PageWrite pageSize)) :
    (runPlan (State.initial old) (persistentCommitPlan old writes)).abstract =
      GrowableStorage.rollbackCommitState old writes .committed := by
  unfold persistentCommitPlan
  simp only [List.cons_append, List.nil_append, runPlan, modelStep]
  rw [runPlan_pwriteMain_append]
  simp [runPlan, modelStep, State.initial, State.abstract,
    GrowableStorage.rollbackCommitState,
    GrowableStorage.JournaledState.initial,
    GrowableStorage.JournaledState.writeJournal,
    GrowableStorage.JournaledState.syncJournal,
    GrowableStorage.JournaledState.stageMainWrites,
    GrowableStorage.JournaledState.syncMain,
    GrowableStorage.JournaledState.deleteJournal,
    GrowableStorage.Cache.writeAll, GrowableStorage.Cache.write,
    GrowableStorage.JournalCache.write, GrowableStorage.JournalCache.sync]

/-- The trusted boundary for an actual filesystem adapter.  `stepRefines`
requires every completed syscall to match the reference transition;
`crashRefines` covers main-file data, the directory entry, and journal data
together. -/
structure Contract (pageSize : Nat) where
  ConcreteState : Type
  view : ConcreteState → State pageSize
  step : ConcreteState → Request pageSize → Response pageSize →
    ConcreteState → Prop
  crash : ConcreteState → GrowableStorage.Image pageSize →
    Option (GrowableStorage.Journal pageSize) → Prop
  stepRefines : ∀ state request response next,
    step state request response next → view next = modelStep (view state) request
  readMainRefines : ∀ state pageId page next,
    step state (.readMain pageId) (.page page) next →
      pageId < (GrowableStorage.applyWrites (view state).main.durable
        (view state).main.pending).pageCount ∧
      page = (GrowableStorage.applyWrites (view state).main.durable
        (view state).main.pending).read pageId
  crashRefines : ∀ state recoveredMain recoveredJournal,
    crash state recoveredMain recoveredJournal →
      Nonempty (GrowableStorage.JournaledCrashOutcome
        (view state).abstract recoveredMain recoveredJournal)

/-- A completed concrete request sequence. Responses are retained because a
read has a value refinement obligation even though writes have unit response. -/
inductive Execution (contract : Contract pageSize) :
    contract.ConcreteState → List (Request pageSize) →
      contract.ConcreteState → Prop where
  | nil (state) : Execution contract state [] state
  | cons {state next final request response requests}
      (completed : contract.step state request response next)
      (remaining : Execution contract next requests final) :
      Execution contract state (request :: requests) final

theorem Execution.refines {contract : Contract pageSize}
    {initial final : contract.ConcreteState} {requests : List (Request pageSize)}
    (executed : Execution contract initial requests final) :
    contract.view final = runPlan (contract.view initial) requests := by
  induction executed with
  | nil => rfl
  | cons completed remaining induction =>
      rw [induction, contract.stepRefines _ _ _ _ completed]
      rfl

/-- Conditional end-to-end refinement for the concrete syscall sequence. The
only premise not proved in Lean is the `Contract` supplied by the host VFS. -/
theorem Execution.commit_refines {contract : Contract pageSize}
    {initial final : contract.ConcreteState}
    (old : GrowableStorage.Image pageSize)
    (writes : List (GrowableStorage.PageWrite pageSize))
    (initialView : contract.view initial = State.initial old)
    (executed : Execution contract initial (commitPlan old writes) final) :
    (contract.view final).abstract =
      GrowableStorage.rollbackCommitState old writes .committed := by
  rw [executed.refines, initialView, run_commitPlan]

theorem Execution.persistentCommit_refines {contract : Contract pageSize}
    {initial final : contract.ConcreteState}
    (old : GrowableStorage.Image pageSize)
    (writes : List (GrowableStorage.PageWrite pageSize))
    (initialView : contract.view initial = State.initial old)
    (executed : Execution contract initial (persistentCommitPlan old writes) final) :
    (contract.view final).abstract =
      GrowableStorage.rollbackCommitState old writes .committed := by
  rw [executed.refines, initialView, run_persistentCommitPlan]

end POSIXVFS
end SQLeanite
