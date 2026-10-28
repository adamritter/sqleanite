import SQLeanite.GrowableStorage.Image

namespace SQLeanite
namespace GrowableStorage

private theorem buildUndo_record_exact (old : Image pageSize)
    (writes : List (PageWrite pageSize))
    (record : UndoRecord pageSize) (member : record ∈ buildUndo old writes) :
    record.pageId < old.pageCount ∧
      record.before = old.read record.pageId ∧
      ∃ write ∈ writes, write.pageId = record.pageId := by
  induction writes with
  | nil => simp [buildUndo] at member
  | cons write writes induction =>
      unfold buildUndo at member
      split at member
      next withinOld =>
        simp only [List.mem_cons] at member
        rcases member with equal | tail
        · subst record
          exact ⟨withinOld, rfl, write, by simp⟩
        · rcases induction tail with ⟨within, before, witness, inTail, page⟩
          exact ⟨within, before, witness, by simp [inTail], page⟩
      next outside =>
        rcases induction member with ⟨within, before, witness, inTail, page⟩
        exact ⟨within, before, witness, by simp [inTail], page⟩

theorem makeJournal_exactPreimages (old : Image pageSize)
    (writes : List (PageWrite pageSize)) :
    (makeJournal old writes).ExactPreimages old writes := by
  constructor
  · rfl
  constructor
  · intro record member
    exact buildUndo_record_exact old writes record member
  · intro write member withinOld
    exact undoLookup_buildUndo_of_mem old writes write member withinOld

/-- Recovery copies recorded page pre-images and then truncates to the page
count saved in the journal header. -/
def recoverWithJournal (recoveredMain : Image pageSize)
    (recoveredJournal : Option (Journal pageSize)) : Image pageSize :=
  match recoveredJournal with
  | none => recoveredMain
  | some journal => {
      pageCount := journal.originalPageCount
      read := fun pageId =>
        (undoLookup pageId journal.undo).getD (recoveredMain.read pageId) }

/-- Replaying the same rollback journal is idempotent.  This matters when a
recovery attempt restores all pre-images but crashes before it can remove the
journal: the next process may safely replay it again. -/
theorem recoverWithJournal_idempotent (recoveredMain : Image pageSize)
    (recoveredJournal : Option (Journal pageSize)) :
    recoverWithJournal (recoverWithJournal recoveredMain recoveredJournal)
        recoveredJournal =
      recoverWithJournal recoveredMain recoveredJournal := by
  cases recoveredJournal with
  | none => rfl
  | some journal =>
      simp only [recoverWithJournal]
      congr
      funext pageId
      cases undoLookup pageId journal.undo <;> rfl

/-- The concrete page writes performed while replaying a rollback journal. -/
def recoveryWrites (journal : Journal pageSize) : List (PageWrite pageSize) :=
  journal.undo.map fun record => ⟨record.pageId, record.before⟩

private theorem undoLookup_none_excludes_record (pageId : Nat)
    (records : List (UndoRecord pageSize))
    (missing : undoLookup pageId records = none) :
    ∀ record ∈ records, record.pageId ≠ pageId := by
  induction records with
  | nil => simp
  | cons head records induction =>
      unfold undoLookup at missing
      split at missing
      next same => contradiction
      next different =>
        intro record member
        simp only [List.mem_cons] at member
        rcases member with equal | tail
        · subst record
          exact different
        · exact induction missing record tail

private theorem recoveryWrites_not_page_of_lookup_none
    (journal : Journal pageSize) (pageId : Nat)
    (missing : undoLookup pageId journal.undo = none) :
    ∀ write ∈ recoveryWrites journal, pageId ≠ write.pageId := by
  intro write member
  simp only [recoveryWrites, List.mem_map] at member
  rcases member with ⟨record, inJournal, equal⟩
  subst write
  exact (undoLookup_none_excludes_record pageId journal.undo missing
    record inJournal).symm

/-- Copying any subset of authentic journal records cannot change the result
of a subsequent complete recovery.  This is the page-by-page recovery
invariant: pages already copied are simply copied to the same value again. -/
theorem recoverWithJournal_apply_recovery_subset
    (recoveredMain : Image pageSize) (journal : Journal pageSize)
    (copied : List (PageWrite pageSize))
    (fromJournal : ∀ write ∈ copied, write ∈ recoveryWrites journal) :
    recoverWithJournal (applyWrites recoveredMain copied) (some journal) =
      recoverWithJournal recoveredMain (some journal) := by
  simp only [recoverWithJournal]
  congr
  funext pageId
  cases lookup : undoLookup pageId journal.undo with
  | none =>
      simp only [Option.getD_none]
      exact applyWrites_read_of_not_written recoveredMain copied pageId
        (fun write member =>
          recoveryWrites_not_page_of_lookup_none journal pageId lookup write
            (fromJournal write member))
  | some before => simp

/-- The result after the first recovery attempt and any finite number of
subsequent restarts which find the same journal.  `restartCount = 0` still
performs the initial recovery. -/
def recoverRepeatedly (recoveredMain : Image pageSize)
    (recoveredJournal : Option (Journal pageSize)) : Nat → Image pageSize
  | 0 => recoverWithJournal recoveredMain recoveredJournal
  | restartCount + 1 =>
      recoverWithJournal
        (recoverRepeatedly recoveredMain recoveredJournal restartCount)
        recoveredJournal

theorem recoverRepeatedly_eq_recover (recoveredMain : Image pageSize)
    (recoveredJournal : Option (Journal pageSize)) :
    ∀ restartCount,
      recoverRepeatedly recoveredMain recoveredJournal restartCount =
        recoverWithJournal recoveredMain recoveredJournal
  | 0 => rfl
  | restartCount + 1 => by
      rw [recoverRepeatedly, recoverRepeatedly_eq_recover,
        recoverWithJournal_idempotent]

theorem recover_makeJournal_apply_subset (old : Image pageSize)
    (writes survived : List (PageWrite pageSize))
    (survivedFromWrites : ∀ write ∈ survived, write ∈ writes) :
    (recoverWithJournal (applyWrites old survived) (some (makeJournal old writes))).Equiv
      old := by
  constructor
  · rfl
  · intro pageId withinOld
    by_cases modified : ∃ write ∈ writes, write.pageId = pageId
    · rcases modified with ⟨write, member, equal⟩
      subst pageId
      simp [recoverWithJournal, makeJournal,
        undoLookup_buildUndo_of_mem old writes write member withinOld]
    · have notWritten : ∀ write ∈ survived, pageId ≠ write.pageId := by
        intro write member equal
        apply modified
        exact ⟨write, survivedFromWrites write member, equal.symm⟩
      have unchanged := applyWrites_read_of_not_written old survived pageId notWritten
      simp only [recoverWithJournal, makeJournal]
      rw [unchanged]
      cases lookup : undoLookup pageId (buildUndo old writes) with
      | none => rfl
      | some before =>
          exfalso
          rcases undoLookup_buildUndo_some_implies_mem old writes pageId lookup with
            ⟨write, member, equal⟩
          exact modified ⟨write, member, equal⟩

structure Cache (pageSize : Nat) where
  durable : Image pageSize
  pending : List (PageWrite pageSize) := []

def Cache.write (cache : Cache pageSize) (write : PageWrite pageSize) :
    Cache pageSize :=
  { cache with pending := cache.pending ++ [write] }

def Cache.writeAll (cache : Cache pageSize) (writes : List (PageWrite pageSize)) :
    Cache pageSize :=
  { cache with pending := cache.pending ++ writes }

def Cache.sync (cache : Cache pageSize) : Cache pageSize :=
  { durable := applyWrites cache.durable cache.pending, pending := [] }

/-- Unsynced writes may survive in any subset and any order. -/
structure CrashOutcome (cache : Cache pageSize) (recovered : Image pageSize) where
  reordered : List (PageWrite pageSize)
  permutation : reordered.Perm cache.pending
  survived : List (PageWrite pageSize)
  sublist : survived.Sublist reordered
  recoveredEq : recovered = applyWrites cache.durable survived

def CrashOutcome.durable (cache : Cache pageSize) :
    CrashOutcome cache cache.durable := by
  exact ⟨cache.pending, List.Perm.refl _, [], List.nil_sublist _,
    by simp [applyWrites]⟩

def CrashOutcome.allPending (cache : Cache pageSize) :
    CrashOutcome cache (applyWrites cache.durable cache.pending) := by
  exact ⟨cache.pending, List.Perm.refl _, cache.pending,
    List.Sublist.refl _, rfl⟩

/-- A crash while copying rollback-journal pages.  The ordinary cache crash
model supplies the important adversarial behavior: any subset and permutation
of the unsynced preimage writes may reach the main file. -/
def RecoveryCrashOutcome (recoveredMain : Image pageSize)
    (journal : Journal pageSize) (crashedMain : Image pageSize) : Type :=
  CrashOutcome ⟨recoveredMain, recoveryWrites journal⟩ crashedMain

/-- A finite sequence of recovery attempts, each of which may itself crash
after an arbitrary allowed collection of page copies. -/
inductive RecoveryCrashTrace (journal : Journal pageSize) :
    Image pageSize → Image pageSize → Prop where
  | nil (main : Image pageSize) : RecoveryCrashTrace journal main main
  | cons {start after finish : Image pageSize}
      (crash : RecoveryCrashOutcome start journal after)
      (tail : RecoveryCrashTrace journal after finish) :
      RecoveryCrashTrace journal start finish

theorem recoverWithJournal_after_recovery_crash
    (recoveredMain crashedMain : Image pageSize)
    (journal : Journal pageSize)
    (outcome : RecoveryCrashOutcome recoveredMain journal crashedMain) :
    recoverWithJournal crashedMain (some journal) =
      recoverWithJournal recoveredMain (some journal) := by
  rcases outcome with ⟨reordered, permutation, survived, sublist, recoveredEq⟩
  subst crashedMain
  apply recoverWithJournal_apply_recovery_subset
  intro write member
  exact permutation.mem_iff.mp (sublist.subset member)

theorem recoverWithJournal_after_recovery_trace
    (journal : Journal pageSize) (start finish : Image pageSize)
    (trace : RecoveryCrashTrace journal start finish) :
    recoverWithJournal finish (some journal) =
      recoverWithJournal start (some journal) := by
  induction trace with
  | nil => rfl
  | cons crash tail induction =>
      exact induction.trans
        (recoverWithJournal_after_recovery_crash _ _ journal crash)

theorem CrashOutcome.noPending_unique (cache : Cache pageSize)
    (recovered : Image pageSize) (empty : cache.pending = [])
    (outcome : CrashOutcome cache recovered) : recovered = cache.durable := by
  rcases outcome with ⟨reordered, permutation, survived, sublist, recoveredEq⟩
  have reorderedEmpty : reordered = [] := by
    rw [empty] at permutation
    exact List.Perm.eq_nil permutation
  subst reordered
  have survivedEmpty : survived = [] := by simpa using sublist
  subst survived
  simpa [applyWrites] using recoveredEq

theorem CrashOutcome.restore_old (old : Image pageSize)
    (writes : List (PageWrite pageSize)) (recovered : Image pageSize)
    (outcome : CrashOutcome ⟨old, writes⟩ recovered) :
    (recoverWithJournal recovered (some (makeJournal old writes))).Equiv old := by
  rcases outcome with ⟨reordered, permutation, survived, sublist, recoveredEq⟩
  subst recovered
  apply recover_makeJournal_apply_subset old writes survived
  intro write member
  exact permutation.mem_iff.mp (sublist.subset member)

structure JournalCache (pageSize : Nat) where
  durable : Option (Journal pageSize) := none
  pending : Option (Option (Journal pageSize)) := none

def JournalCache.write (cache : JournalCache pageSize)
    (value : Option (Journal pageSize)) : JournalCache pageSize :=
  { cache with pending := some value }

def JournalCache.sync (cache : JournalCache pageSize) : JournalCache pageSize :=
  { durable := cache.pending.getD cache.durable, pending := none }

def JournalCrashOutcome (cache : JournalCache pageSize)
    (recovered : Option (Journal pageSize)) : Prop :=
  recovered = cache.durable ∨
    ∃ value, cache.pending = some value ∧ recovered = value

theorem JournalCrashOutcome.noPending_unique
    (cache : JournalCache pageSize) (recovered : Option (Journal pageSize))
    (empty : cache.pending = none) (outcome : JournalCrashOutcome cache recovered) :
    recovered = cache.durable := by
  rcases outcome with durable | ⟨value, pending, recovered⟩
  · exact durable
  · rw [empty] at pending
    contradiction

theorem JournalCrashOutcome.pending_cases
    (cache : JournalCache pageSize) (value : Option (Journal pageSize))
    (recovered : Option (Journal pageSize)) (pending : cache.pending = some value)
    (outcome : JournalCrashOutcome cache recovered) :
    recovered = cache.durable ∨ recovered = value := by
  rcases outcome with durable | ⟨candidate, candidatePending, recovered⟩
  · exact .inl durable
  · right
    rw [pending] at candidatePending
    injection candidatePending with equal
    exact recovered.trans equal.symm

structure JournaledState (pageSize : Nat) where
  main : Cache pageSize
  journal : JournalCache pageSize

def JournaledState.initial (old : Image pageSize) : JournaledState pageSize :=
  { main := { durable := old }, journal := {} }

def JournaledState.writeJournal (state : JournaledState pageSize)
    (journal : Journal pageSize) : JournaledState pageSize :=
  { state with journal := state.journal.write (some journal) }

def JournaledState.syncJournal (state : JournaledState pageSize) :
    JournaledState pageSize :=
  { state with journal := state.journal.sync }

def JournaledState.stageMainWrites (state : JournaledState pageSize)
    (writes : List (PageWrite pageSize)) : JournaledState pageSize :=
  { state with main := state.main.writeAll writes }

def JournaledState.syncMain (state : JournaledState pageSize) :
    JournaledState pageSize :=
  { state with main := state.main.sync }

def JournaledState.deleteJournal (state : JournaledState pageSize) :
    JournaledState pageSize :=
  { state with journal := state.journal.write none }

inductive CommitPhase where
  | initial
  | journalWritten
  | journalSynced
  | mainWritten
  | mainSynced
  | journalDeleted
  | committed
  deriving Repr, DecidableEq

def rollbackCommitState (old : Image pageSize) (writes : List (PageWrite pageSize)) :
    CommitPhase → JournaledState pageSize
  | CommitPhase.initial => JournaledState.initial old
  | CommitPhase.journalWritten =>
      (JournaledState.initial old).writeJournal (makeJournal old writes)
  | CommitPhase.journalSynced =>
      ((JournaledState.initial old).writeJournal (makeJournal old writes)).syncJournal
  | CommitPhase.mainWritten =>
      (((JournaledState.initial old).writeJournal
        (makeJournal old writes)).syncJournal).stageMainWrites writes
  | CommitPhase.mainSynced =>
      ((((JournaledState.initial old).writeJournal
        (makeJournal old writes)).syncJournal).stageMainWrites writes).syncMain
  | CommitPhase.journalDeleted =>
      (((((JournaledState.initial old).writeJournal
        (makeJournal old writes)).syncJournal).stageMainWrites writes).syncMain).deleteJournal
  | CommitPhase.committed =>
      ((((((JournaledState.initial old).writeJournal
        (makeJournal old writes)).syncJournal).stageMainWrites writes).syncMain).deleteJournal).syncJournal

structure JournaledCrashOutcome (state : JournaledState pageSize)
    (recoveredMain : Image pageSize)
    (recoveredJournal : Option (Journal pageSize)) where
  mainOutcome : CrashOutcome state.main recoveredMain
  journalOutcome : JournalCrashOutcome state.journal recoveredJournal

/-- Operations a thin filesystem adapter must implement for the growable
rollback protocol. Recovery itself remains the verified pure
`recoverWithJournal` function over the files returned after a crash. -/
inductive VFSRequest (pageSize : Nat) where
  | readMain (pageId : Nat)
  | writeMain (write : PageWrite pageSize)
  | syncMain
  | writeJournal (journal : Option (Journal pageSize))
  | syncJournal

inductive VFSResponse (pageSize : Nat) where
  | page (value : Storage.Page pageSize)
  | unit

/-- Explicit refinement boundary for a growable main file and rollback-journal
file. No real filesystem is assumed to satisfy it: an IO adapter must establish
these obligations separately. -/
structure VFSContract (pageSize : Nat) where
  State : Type
  view : State → JournaledState pageSize
  step : State → VFSRequest pageSize → VFSResponse pageSize → State → Prop
  crash : State → Image pageSize → Option (Journal pageSize) → Prop
  readMainRefines : ∀ state pageId page next,
    step state (.readMain pageId) (.page page) next →
      pageId < (applyWrites (view state).main.durable
        (view state).main.pending).pageCount ∧
      page = (applyWrites (view state).main.durable
        (view state).main.pending).read pageId ∧
      view next = view state
  writeMainRefines : ∀ state write next,
    step state (.writeMain write) .unit next →
      view next = { view state with main := (view state).main.write write }
  syncMainRefines : ∀ state next,
    step state .syncMain .unit next →
      view next = { view state with main := (view state).main.sync }
  writeJournalRefines : ∀ state journal next,
    step state (.writeJournal journal) .unit next →
      view next = { view state with journal := (view state).journal.write journal }
  syncJournalRefines : ∀ state next,
    step state .syncJournal .unit next →
      view next = { view state with journal := (view state).journal.sync }
  crashRefines : ∀ state recoveredMain recoveredJournal,
    crash state recoveredMain recoveredJournal →
      Nonempty (JournaledCrashOutcome (view state) recoveredMain recoveredJournal)

end GrowableStorage

end SQLeanite
