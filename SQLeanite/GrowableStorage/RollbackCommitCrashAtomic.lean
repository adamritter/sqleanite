import SQLeanite.GrowableStorage.BuildUndoRecordExact

namespace SQLeanite
namespace GrowableStorage

/-- Crash atomicity for growable images and a page-level undo journal. -/
theorem rollbackCommit_crash_atomic (old : Image pageSize)
    (writes : List (PageWrite pageSize)) (phase : CommitPhase)
    (recoveredMain : Image pageSize)
    (recoveredJournal : Option (Journal pageSize))
    (outcome : JournaledCrashOutcome (rollbackCommitState old writes phase)
      recoveredMain recoveredJournal) :
    (recoverWithJournal recoveredMain recoveredJournal).Equiv old ∨
      (recoverWithJournal recoveredMain recoveredJournal).Equiv
        (applyWrites old writes) := by
  rcases outcome with ⟨mainOutcome, journalOutcome⟩
  cases phase with
  | initial =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      left
      simp [rollbackCommitState, JournaledState.initial] at main journal
      simp [recoverWithJournal, main, journal, Image.Equiv.refl]
  | journalWritten =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.pending_cases _
        (some (makeJournal old writes)) _ rfl journalOutcome
      left
      rcases journal with journal | journal
      · simp [rollbackCommitState, JournaledState.initial,
          JournaledState.writeJournal, JournalCache.write] at main journal
        simp [recoverWithJournal, main, journal, Image.Equiv.refl]
      · simp [rollbackCommitState, JournaledState.initial,
          JournaledState.writeJournal, JournalCache.write] at main journal
        subst recoveredMain
        subst recoveredJournal
        exact recover_makeJournal_apply_subset old writes [] (by simp)
  | journalSynced =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      left
      simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
        JournaledState.syncJournal, JournalCache.write, JournalCache.sync] at main journal
      subst recoveredMain
      subst recoveredJournal
      exact recover_makeJournal_apply_subset old writes [] (by simp)
  | mainWritten =>
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      left
      simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
        JournaledState.syncJournal, JournaledState.stageMainWrites,
        Cache.writeAll, JournalCache.write, JournalCache.sync] at journal
      subst recoveredJournal
      exact CrashOutcome.restore_old old writes recoveredMain mainOutcome
  | mainSynced =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      left
      simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
        JournaledState.syncJournal, JournaledState.stageMainWrites,
        JournaledState.syncMain, Cache.writeAll, Cache.sync,
        JournalCache.write, JournalCache.sync] at main journal
      subst recoveredMain
      subst recoveredJournal
      exact recover_makeJournal_apply_subset old writes writes (by simp)
  | journalDeleted =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.pending_cases _ none _ rfl journalOutcome
      simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
        JournaledState.syncJournal, JournaledState.stageMainWrites,
        JournaledState.syncMain, JournaledState.deleteJournal,
        Cache.writeAll, Cache.sync, JournalCache.write, JournalCache.sync] at main journal
      rcases journal with journal | journal
      · left
        subst recoveredMain
        subst recoveredJournal
        exact recover_makeJournal_apply_subset old writes writes (by simp)
      · right
        subst recoveredMain
        subst recoveredJournal
        exact Image.Equiv.refl _
  | committed =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      right
      simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
        JournaledState.syncJournal, JournaledState.stageMainWrites,
        JournaledState.syncMain, JournaledState.deleteJournal,
        Cache.writeAll, Cache.sync, JournalCache.write, JournalCache.sync] at main journal
      subst recoveredMain
      subst recoveredJournal
      exact Image.Equiv.refl _

/-- Crash atomicity is stable under arbitrarily many recovery-process
restarts, provided every restart sees the same surviving journal.  This closes
the common "recovery crashed after copying pages but before unlink" case
without adding recovery itself to the trusted base. -/
theorem rollbackCommit_repeated_recovery_crash_atomic (old : Image pageSize)
    (writes : List (PageWrite pageSize)) (phase : CommitPhase)
    (recoveredMain : Image pageSize)
    (recoveredJournal : Option (Journal pageSize))
    (outcome : JournaledCrashOutcome (rollbackCommitState old writes phase)
      recoveredMain recoveredJournal) (restartCount : Nat) :
    (recoverRepeatedly recoveredMain recoveredJournal restartCount).Equiv old ∨
      (recoverRepeatedly recoveredMain recoveredJournal restartCount).Equiv
        (applyWrites old writes) := by
  rw [recoverRepeatedly_eq_recover]
  exact rollbackCommit_crash_atomic old writes phase recoveredMain
    recoveredJournal outcome

/-- Full FSCQ-style recovery-crash closure.  After a transaction crash leaves
a valid journal, recovery itself may crash any finite number of times.  Each
attempt may persist any subset/permutation of the page preimages it tried to
copy.  A final restart still observes only the transaction's old or new
image. -/
theorem rollbackCommit_recovery_crash_trace_atomic (old : Image pageSize)
    (writes : List (PageWrite pageSize)) (phase : CommitPhase)
    (recoveredMain finalMain : Image pageSize)
    (journal : Journal pageSize)
    (outcome : JournaledCrashOutcome (rollbackCommitState old writes phase)
      recoveredMain (some journal))
    (recoveryCrashes : RecoveryCrashTrace journal recoveredMain finalMain) :
    (recoverWithJournal finalMain (some journal)).Equiv old ∨
      (recoverWithJournal finalMain (some journal)).Equiv
        (applyWrites old writes) := by
  have stable := recoverWithJournal_after_recovery_trace journal recoveredMain
    finalMain recoveryCrashes
  rw [stable]
  exact rollbackCommit_crash_atomic old writes phase recoveredMain
    (some journal) outcome

/-- Once commit has returned, recovery must yield the new image. The more
general atomicity theorem intentionally allows old or new at earlier phases. -/
theorem rollbackCommit_committed_recovers_new (old : Image pageSize)
    (writes : List (PageWrite pageSize))
    (recoveredMain : Image pageSize)
    (recoveredJournal : Option (Journal pageSize))
    (outcome : JournaledCrashOutcome
      (rollbackCommitState old writes CommitPhase.committed)
      recoveredMain recoveredJournal) :
    (recoverWithJournal recoveredMain recoveredJournal).Equiv
      (applyWrites old writes) := by
  rcases outcome with ⟨mainOutcome, journalOutcome⟩
  have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
  have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
  simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
    JournaledState.syncJournal, JournaledState.stageMainWrites,
    JournaledState.syncMain, JournaledState.deleteJournal,
    Cache.writeAll, Cache.sync, JournalCache.write, JournalCache.sync] at main journal
  subst recoveredMain
  subst recoveredJournal
  exact Image.Equiv.refl _

theorem crash_can_lose_all_pending (cache : Cache pageSize) :
    ∃ recovered, Nonempty (CrashOutcome cache recovered) :=
  ⟨cache.durable, ⟨CrashOutcome.durable cache⟩⟩

theorem crash_can_keep_all_pending (cache : Cache pageSize) :
    ∃ recovered, Nonempty (CrashOutcome cache recovered) :=
  ⟨applyWrites cache.durable cache.pending, ⟨CrashOutcome.allPending cache⟩⟩

/-- Non-vacuity for the new growth case: a main-file growth write may survive,
yet the synced page-level journal restores the old page count and contents. -/
theorem crash_can_roll_back_growth (old : Image pageSize)
    (newPage : Storage.Page pageSize) :
    let growth : PageWrite pageSize := ⟨old.pageCount, newPage⟩
    let writes := [growth]
    ∃ recoveredMain recoveredJournal,
      Nonempty (JournaledCrashOutcome
        (rollbackCommitState old writes CommitPhase.mainWritten)
        recoveredMain recoveredJournal) ∧
      (recoverWithJournal recoveredMain recoveredJournal).Equiv old ∧
      old.pageCount < (applyWrites old writes).pageCount := by
  dsimp
  let growth : PageWrite pageSize := ⟨old.pageCount, newPage⟩
  let writes := [growth]
  let state := rollbackCommitState old writes CommitPhase.mainWritten
  let recoveredMain := applyWrites old writes
  let recoveredJournal := some (makeJournal old writes)
  refine ⟨recoveredMain, recoveredJournal, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    constructor
    · simpa [state, rollbackCommitState, JournaledState.initial,
        JournaledState.writeJournal, JournaledState.syncJournal,
        JournaledState.stageMainWrites, Cache.writeAll,
        JournalCache.write, JournalCache.sync, recoveredMain, writes, growth] using
          CrashOutcome.allPending
            (cache := (state.main : Cache pageSize))
    · left
      simp [state, rollbackCommitState, JournaledState.initial,
        JournaledState.writeJournal, JournaledState.syncJournal,
        JournaledState.stageMainWrites, Cache.writeAll,
        JournalCache.write, JournalCache.sync, recoveredJournal, writes, growth]
  · exact recover_makeJournal_apply_subset old writes writes (by simp)
  · simp [writes, growth, applyWrites, Image.write]

end GrowableStorage

end SQLeanite
