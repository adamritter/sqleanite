import Std

namespace SQLeanite
namespace Storage

/-- A database page whose byte length is fixed by its type. -/
structure Page (pageSize : Nat) where
  bytes : Array UInt8
  sizeInvariant : bytes.size = pageSize
  deriving DecidableEq

instance : Repr (Page pageSize) where
  reprPrec page precedence := reprPrec page.bytes precedence

def Page.zero (pageSize : Nat) : Page pageSize :=
  ⟨Array.replicate pageSize 0, by simp⟩

/-- Page references are in range by construction. -/
abbrev PageId (pageCount : Nat) := Fin pageCount

/-- A logical disk is exactly one fixed-size page at every valid page id. -/
structure Disk (pageSize pageCount : Nat) where
  read : PageId pageCount → Page pageSize

def Disk.constant (pageSize pageCount : Nat) (page : Page pageSize) :
    Disk pageSize pageCount :=
  ⟨fun _ => page⟩

def Disk.write (disk : Disk pageSize pageCount) (pageId : PageId pageCount)
    (page : Page pageSize) : Disk pageSize pageCount :=
  ⟨fun candidate => if candidate = pageId then page else disk.read candidate⟩

@[simp] theorem Disk.read_write_same (disk : Disk pageSize pageCount)
    (pageId : PageId pageCount) (page : Page pageSize) :
    (disk.write pageId page).read pageId = page := by
  simp [Disk.write]

@[simp] theorem Disk.read_write_other (disk : Disk pageSize pageCount)
    (written requested : PageId pageCount) (page : Page pageSize)
    (different : requested ≠ written) :
    (disk.write written page).read requested = disk.read requested := by
  simp [Disk.write, different]

structure PageWrite (pageSize pageCount : Nat) where
  pageId : PageId pageCount
  page : Page pageSize

def applyWrites (disk : Disk pageSize pageCount)
    (writes : List (PageWrite pageSize pageCount)) : Disk pageSize pageCount :=
  writes.foldl (fun state write => state.write write.pageId write.page) disk

@[simp] theorem applyWrites_nil (disk : Disk pageSize pageCount) :
    applyWrites disk [] = disk := rfl

theorem applyWrites_read_of_not_written
    (disk : Disk pageSize pageCount)
    (writes : List (PageWrite pageSize pageCount))
    (pageId : PageId pageCount)
    (notWritten : ∀ write ∈ writes, pageId ≠ write.pageId) :
    (applyWrites disk writes).read pageId = disk.read pageId := by
  induction writes generalizing disk with
  | nil => rfl
  | cons write writes induction =>
      unfold applyWrites
      simp only [List.foldl_cons]
      change (applyWrites (disk.write write.pageId write.page) writes).read pageId =
        disk.read pageId
      rw [induction]
      · exact Disk.read_write_other disk write.pageId pageId write.page
          (notWritten write (by simp))
      · intro later member
        exact notWritten later (by simp [member])

/-- `durable` contains data known to be behind a completed sync. `pending`
contains issued whole-page writes not yet covered by a durability barrier. -/
structure Cache (pageSize pageCount : Nat) where
  durable : Disk pageSize pageCount
  pending : List (PageWrite pageSize pageCount) := []

def Cache.write (cache : Cache pageSize pageCount)
    (write : PageWrite pageSize pageCount) : Cache pageSize pageCount :=
  { cache with pending := cache.pending ++ [write] }

def Cache.sync (cache : Cache pageSize pageCount) : Cache pageSize pageCount :=
  { durable := applyWrites cache.durable cache.pending, pending := [] }

private def latestPending? (pageId : PageId pageCount) :
    List (PageWrite pageSize pageCount) → Option (Page pageSize)
  | [] => none
  | write :: rest =>
    (latestPending? pageId rest).orElse fun _ =>
      if write.pageId = pageId then some write.page else none

def Cache.read (cache : Cache pageSize pageCount) (pageId : PageId pageCount) :
    Page pageSize :=
  (latestPending? pageId cache.pending).getD (cache.durable.read pageId)

@[simp] theorem Cache.sync_pending (cache : Cache pageSize pageCount) :
    cache.sync.pending = [] := rfl

@[simp] theorem Cache.sync_durable (cache : Cache pageSize pageCount) :
    cache.sync.durable = applyWrites cache.durable cache.pending := rfl

inductive Operation (pageSize pageCount : Nat) where
  | write (value : PageWrite pageSize pageCount)
  | sync

def runOperation (cache : Cache pageSize pageCount) :
    Operation pageSize pageCount → Cache pageSize pageCount
  | .write value => cache.write value
  | .sync => cache.sync

/-- Crash model for atomic page writes without torn pages. Writes not followed
by a completed sync may reach stable storage in any subset and order. Writes
already in `durable` cannot be lost. -/
def CrashOutcome (cache : Cache pageSize pageCount)
    (recovered : Disk pageSize pageCount) : Prop :=
  ∃ reordered, cache.pending.Perm reordered ∧
    ∃ survived, List.Sublist survived reordered ∧
      recovered = applyWrites cache.durable survived

/-- Losing every unsynced write is always permitted by the crash model. -/
theorem CrashOutcome.durable (cache : Cache pageSize pageCount) :
    CrashOutcome cache cache.durable := by
  refine ⟨cache.pending, List.Perm.refl _, [], ?_, ?_⟩
  · simp
  · simp [applyWrites]

/-- Letting all unsynced writes reach disk in their issued order is also a
permitted crash outcome. -/
theorem CrashOutcome.allPending (cache : Cache pageSize pageCount) :
    CrashOutcome cache (applyWrites cache.durable cache.pending) := by
  exact ⟨cache.pending, List.Perm.refl _, cache.pending,
    List.Sublist.refl cache.pending, rfl⟩

/-- A completed sync removes crash nondeterminism: every allowed recovered disk
is exactly the newly durable disk. -/
theorem CrashOutcome.afterSync_unique (cache : Cache pageSize pageCount)
    (recovered : Disk pageSize pageCount) (outcome : CrashOutcome cache.sync recovered) :
    recovered = cache.sync.durable := by
  rcases outcome with ⟨reordered, permutation, survived, sublist, recoveredEq⟩
  have reorderedEmpty : reordered = [] := by
    simpa using permutation
  subst reordered
  have survivedEmpty : survived = [] := by
    simpa using sublist
  subst survived
  simpa using recoveredEq

/-- A journal file has a durable value and at most one unsynced replacement.
`some old` creates the rollback journal; `none` deletes it. -/
structure JournalCache (pageSize pageCount : Nat) where
  durable : Option (Disk pageSize pageCount) := none
  pending : Option (Option (Disk pageSize pageCount)) := none

def JournalCache.write (journal : JournalCache pageSize pageCount)
    (value : Option (Disk pageSize pageCount)) : JournalCache pageSize pageCount :=
  { journal with pending := some value }

def JournalCache.sync (journal : JournalCache pageSize pageCount) :
    JournalCache pageSize pageCount :=
  { durable := journal.pending.getD journal.durable, pending := none }

/-- An unsynced journal replacement may survive or be lost. -/
def JournalCrashOutcome (journal : JournalCache pageSize pageCount)
    (recovered : Option (Disk pageSize pageCount)) : Prop :=
  recovered = journal.durable ∨
    ∃ value, journal.pending = some value ∧ recovered = value

theorem JournalCrashOutcome.noPending_unique
    (journal : JournalCache pageSize pageCount)
    (recovered : Option (Disk pageSize pageCount))
    (empty : journal.pending = none)
    (outcome : JournalCrashOutcome journal recovered) :
    recovered = journal.durable := by
  rcases outcome with durable | ⟨value, pending, recovered⟩
  · exact durable
  · rw [empty] at pending
    contradiction

theorem JournalCrashOutcome.pending_cases
    (journal : JournalCache pageSize pageCount)
    (value recovered : Option (Disk pageSize pageCount))
    (pending : journal.pending = some value)
    (outcome : JournalCrashOutcome journal recovered) :
    recovered = journal.durable ∨ recovered = value := by
  rcases outcome with durable | ⟨survivor, staged, recovered⟩
  · exact Or.inl durable
  · rw [pending] at staged
    cases staged
    exact Or.inr recovered

structure JournaledState (pageSize pageCount : Nat) where
  main : Cache pageSize pageCount
  journal : JournalCache pageSize pageCount

def JournaledState.initial (old : Disk pageSize pageCount) :
    JournaledState pageSize pageCount :=
  { main := { durable := old }, journal := {} }

def JournaledState.writeJournal (state : JournaledState pageSize pageCount) :
    JournaledState pageSize pageCount :=
  { state with journal := state.journal.write (some state.main.durable) }

def JournaledState.syncJournal (state : JournaledState pageSize pageCount) :
    JournaledState pageSize pageCount :=
  { state with journal := state.journal.sync }

def JournaledState.stageMainWrites (state : JournaledState pageSize pageCount)
    (writes : List (PageWrite pageSize pageCount)) : JournaledState pageSize pageCount :=
  { state with main := { state.main with pending := writes } }

def JournaledState.syncMain (state : JournaledState pageSize pageCount) :
    JournaledState pageSize pageCount :=
  { state with main := state.main.sync }

def JournaledState.deleteJournal (state : JournaledState pageSize pageCount) :
    JournaledState pageSize pageCount :=
  { state with journal := state.journal.write none }

/-- Observable commit checkpoints. A crash may occur at any of them. -/
inductive CommitPhase where
  | initial
  | journalWritten
  | journalSynced
  | mainWritten
  | mainSynced
  | journalDeleted
  | committed
  deriving DecidableEq, Repr

def rollbackCommitState (old : Disk pageSize pageCount)
    (writes : List (PageWrite pageSize pageCount)) :
    CommitPhase → JournaledState pageSize pageCount
  | .initial => JournaledState.initial old
  | .journalWritten => JournaledState.writeJournal (JournaledState.initial old)
  | .journalSynced =>
      JournaledState.syncJournal (JournaledState.writeJournal (JournaledState.initial old))
  | .mainWritten => JournaledState.stageMainWrites
      (JournaledState.syncJournal (JournaledState.writeJournal (JournaledState.initial old))) writes
  | .mainSynced => JournaledState.syncMain <| JournaledState.stageMainWrites
      (JournaledState.syncJournal (JournaledState.writeJournal (JournaledState.initial old))) writes
  | .journalDeleted =>
      JournaledState.deleteJournal <| JournaledState.syncMain <| JournaledState.stageMainWrites
        (JournaledState.syncJournal (JournaledState.writeJournal (JournaledState.initial old))) writes
  | .committed =>
      JournaledState.syncJournal <| JournaledState.deleteJournal <| JournaledState.syncMain <|
        JournaledState.stageMainWrites
          (JournaledState.syncJournal (JournaledState.writeJournal (JournaledState.initial old))) writes

def JournaledCrashOutcome (state : JournaledState pageSize pageCount)
    (recoveredMain : Disk pageSize pageCount)
    (recoveredJournal : Option (Disk pageSize pageCount)) : Prop :=
  CrashOutcome state.main recoveredMain ∧
    JournalCrashOutcome state.journal recoveredJournal

/-- Recovery rolls the main file back whenever a journal survived. -/
def recoverWithJournal (recoveredMain : Disk pageSize pageCount)
    (recoveredJournal : Option (Disk pageSize pageCount)) : Disk pageSize pageCount :=
  recoveredJournal.getD recoveredMain

private theorem CrashOutcome.noPending_unique (cache : Cache pageSize pageCount)
    (recovered : Disk pageSize pageCount) (empty : cache.pending = [])
    (outcome : CrashOutcome cache recovered) : recovered = cache.durable := by
  rcases outcome with ⟨reordered, permutation, survived, sublist, recoveredEq⟩
  have reorderedEmpty : reordered = [] := by
    rw [empty] at permutation
    simpa using permutation
  subst reordered
  have survivedEmpty : survived = [] := by simpa using sublist
  subst survived
  simpa [applyWrites] using recoveredEq

/-- Crash atomicity for the modeled rollback-journal commit protocol: at every
checkpoint and for every permitted main-file and journal crash outcome,
recovery returns exactly the old state or exactly the fully written new state. -/
theorem rollbackCommit_crash_atomic (old : Disk pageSize pageCount)
    (writes : List (PageWrite pageSize pageCount)) (phase : CommitPhase)
    (recoveredMain : Disk pageSize pageCount)
    (recoveredJournal : Option (Disk pageSize pageCount))
    (outcome : JournaledCrashOutcome (rollbackCommitState old writes phase)
      recoveredMain recoveredJournal) :
    recoverWithJournal recoveredMain recoveredJournal = old ∨
      recoverWithJournal recoveredMain recoveredJournal = applyWrites old writes := by
  rcases outcome with ⟨mainOutcome, journalOutcome⟩
  cases phase with
  | initial =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      left
      simp [rollbackCommitState, JournaledState.initial] at main journal
      simp [recoverWithJournal, main, journal]
  | journalWritten =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.pending_cases _ (some old) _ rfl journalOutcome
      left
      rcases journal with journal | journal <;>
        simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
          JournalCache.write] at main journal <;>
        simp [recoverWithJournal, main, journal]
  | journalSynced =>
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      left
      simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
        JournaledState.syncJournal, JournalCache.write, JournalCache.sync] at journal
      simp [recoverWithJournal, journal]
  | mainWritten =>
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      left
      simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
        JournaledState.syncJournal, JournaledState.stageMainWrites,
        JournalCache.write, JournalCache.sync] at journal
      simp [recoverWithJournal, journal]
  | mainSynced =>
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      left
      simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
        JournaledState.syncJournal, JournaledState.stageMainWrites, JournaledState.syncMain,
        JournalCache.write, JournalCache.sync] at journal
      simp [recoverWithJournal, journal]
  | journalDeleted =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.pending_cases _ none _ rfl journalOutcome
      rcases journal with journal | journal
      · left
        simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
          JournaledState.syncJournal, JournaledState.stageMainWrites, JournaledState.syncMain,
          JournaledState.deleteJournal, JournalCache.write, JournalCache.sync] at journal
        simp [recoverWithJournal, journal]
      · right
        simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
          JournaledState.syncJournal, JournaledState.stageMainWrites, JournaledState.syncMain,
          JournaledState.deleteJournal, JournalCache.write, JournalCache.sync] at main journal
        simp [recoverWithJournal, main, journal]
  | committed =>
      have main := CrashOutcome.noPending_unique _ _ rfl mainOutcome
      have journal := JournalCrashOutcome.noPending_unique _ _ rfl journalOutcome
      right
      simp [rollbackCommitState, JournaledState.initial, JournaledState.writeJournal,
        JournaledState.syncJournal, JournaledState.stageMainWrites, JournaledState.syncMain,
        JournaledState.deleteJournal, JournalCache.write, JournalCache.sync] at main journal
      simp [recoverWithJournal, main, journal]

/-- Requests emitted by the verified core. A platform adapter interprets these
requests; the core reasons only about the relation below. -/
inductive VFSRequest (pageSize pageCount : Nat) where
  | read (pageId : PageId pageCount)
  | write (value : PageWrite pageSize pageCount)
  | sync

inductive VFSResponse (pageSize : Nat) where
  | page (value : Page pageSize)
  | unit

/-- Formal boundary an OS/filesystem adapter must refine. A real adapter may
remain unverified, but its assumptions cannot be hidden: reads, writes, syncs,
and crash outcomes must be related to the explicit cache model. -/
structure VFSContract (pageSize pageCount : Nat) where
  State : Type
  view : State → Cache pageSize pageCount
  step : State → VFSRequest pageSize pageCount → VFSResponse pageSize → State → Prop
  crash : State → Disk pageSize pageCount → Prop
  readRefines : ∀ state pageId page next,
    step state (.read pageId) (.page page) next →
      page = (view state).read pageId ∧ view next = view state
  writeRefines : ∀ state write next,
    step state (.write write) .unit next → view next = (view state).write write
  syncRefines : ∀ state next,
    step state .sync .unit next → view next = (view state).sync
  crashRefines : ∀ state recovered,
    crash state recovered → CrashOutcome (view state) recovered

end Storage
end SQLeanite
