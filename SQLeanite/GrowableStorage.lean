import SQLeanite.Storage

namespace SQLeanite
namespace GrowableStorage

/-- A growable database image. Reads outside `pageCount` are deliberately
unobservable; valid clients use `readPage` with a `Fin pageCount`. -/
structure Image (pageSize : Nat) where
  pageCount : Nat
  read : Nat → Storage.Page pageSize

def Image.readPage (image : Image pageSize) (pageId : Fin image.pageCount) :
    Storage.Page pageSize :=
  image.read pageId.val

def Image.Equiv (left right : Image pageSize) : Prop :=
  left.pageCount = right.pageCount ∧
    ∀ pageId, pageId < left.pageCount → left.read pageId = right.read pageId

theorem Image.Equiv.refl (image : Image pageSize) : image.Equiv image := by
  exact ⟨rfl, fun _ _ => rfl⟩

theorem Image.Equiv.symm {left right : Image pageSize}
    (equivalent : left.Equiv right) : right.Equiv left := by
  constructor
  · exact equivalent.1.symm
  · intro pageId bound
    exact (equivalent.2 pageId (by simpa [equivalent.1] using bound)).symm

theorem Image.Equiv.trans {left middle right : Image pageSize}
    (leftMiddle : left.Equiv middle) (middleRight : middle.Equiv right) :
    left.Equiv right := by
  constructor
  · exact leftMiddle.1.trans middleRight.1
  · intro pageId bound
    rw [leftMiddle.2 pageId bound]
    exact middleRight.2 pageId (by simpa [leftMiddle.1] using bound)

structure PageWrite (pageSize : Nat) where
  pageId : Nat
  page : Storage.Page pageSize
  deriving Repr

def Image.write (image : Image pageSize) (write : PageWrite pageSize) :
    Image pageSize := {
  pageCount := max image.pageCount (write.pageId + 1)
  read := fun pageId => if pageId = write.pageId then write.page else image.read pageId }

@[simp] theorem Image.read_write_same (image : Image pageSize)
    (write : PageWrite pageSize) :
    (image.write write).read write.pageId = write.page := by
  simp [Image.write]

theorem Image.read_write_other (image : Image pageSize)
    (write : PageWrite pageSize) (pageId : Nat) (different : pageId ≠ write.pageId) :
    (image.write write).read pageId = image.read pageId := by
  simp [Image.write, different]

def applyWrites (image : Image pageSize) (writes : List (PageWrite pageSize)) :
    Image pageSize :=
  writes.foldl Image.write image

theorem applyWrites_read_of_not_written (image : Image pageSize)
    (writes : List (PageWrite pageSize)) (pageId : Nat)
    (notWritten : ∀ write ∈ writes, pageId ≠ write.pageId) :
    (applyWrites image writes).read pageId = image.read pageId := by
  induction writes generalizing image with
  | nil => rfl
  | cons write writes induction =>
      unfold applyWrites
      simp only [List.foldl_cons]
      change (applyWrites (image.write write) writes).read pageId = image.read pageId
      rw [induction]
      · exact image.read_write_other write pageId (notWritten write (by simp))
      · intro later member
        exact notWritten later (by simp [member])

/-- Emit every page in `[0, count)` in descending order.  This is the simple,
canonical transaction used when replacing a complete growable image. -/
def fullWrites (target : Image pageSize) : Nat → List (PageWrite pageSize)
  | 0 => []
  | count + 1 => ⟨count, target.read count⟩ :: fullWrites target count

theorem fullWrites_pageId_lt (target : Image pageSize) :
    ∀ {count : Nat} {write : PageWrite pageSize},
      write ∈ fullWrites target count → write.pageId < count
  | 0, write, member => by simp [fullWrites] at member
  | count + 1, write, member => by
      simp only [fullWrites, List.mem_cons] at member
      rcases member with equal | member
      · subst write
        simp
      · exact Nat.lt_trans (fullWrites_pageId_lt target member)
          (Nat.lt_succ_self count)

theorem apply_fullWrites_pageCount (old target : Image pageSize) :
    ∀ count,
      (applyWrites old (fullWrites target count)).pageCount =
        max old.pageCount count
  | 0 => by simp [applyWrites, fullWrites]
  | count + 1 => by
      change (applyWrites (old.write ⟨count, target.read count⟩)
        (fullWrites target count)).pageCount = max old.pageCount (count + 1)
      rw [apply_fullWrites_pageCount]
      simp [Image.write]

theorem apply_fullWrites_read (old target : Image pageSize) :
    ∀ {count pageId : Nat}, pageId < count →
      (applyWrites old (fullWrites target count)).read pageId =
        target.read pageId
  | 0, pageId, bound => by omega
  | count + 1, pageId, bound => by
      change (applyWrites (old.write ⟨count, target.read count⟩)
        (fullWrites target count)).read pageId = target.read pageId
      by_cases last : pageId = count
      · subst pageId
        rw [applyWrites_read_of_not_written]
        · exact Image.read_write_same old ⟨count, target.read count⟩
        · intro write member
          have below := fullWrites_pageId_lt target member
          omega
      · have below : pageId < count := by omega
        exact apply_fullWrites_read (old.write ⟨count, target.read count⟩)
          target below

def replaceWrites (target : Image pageSize) : List (PageWrite pageSize) :=
  fullWrites target target.pageCount

/-- Replacing all target pages refines the target image whenever the operation
does not shrink the main file. -/
theorem apply_replaceWrites_equiv (old target : Image pageSize)
    (doesNotShrink : old.pageCount ≤ target.pageCount) :
    (applyWrites old (replaceWrites target)).Equiv target := by
  constructor
  · rw [replaceWrites, apply_fullWrites_pageCount]
    omega
  · intro pageId bound
    have targetBound : pageId < target.pageCount := by
      rw [replaceWrites, apply_fullWrites_pageCount] at bound
      omega
    exact apply_fullWrites_read old target targetBound

/-- Emit only pages which are new or whose contents differ from the old
image.  Like `fullWrites`, the result is in descending page-id order. -/
def changedWrites (old target : Image pageSize) :
    Nat → List (PageWrite pageSize)
  | 0 => []
  | count + 1 =>
      if _unchanged : count < old.pageCount ∧
          old.read count = target.read count then
        changedWrites old target count
      else
        ⟨count, target.read count⟩ :: changedWrites old target count

theorem changedWrites_pageId_lt (old target : Image pageSize) :
    ∀ {count : Nat} {write : PageWrite pageSize},
      write ∈ changedWrites old target count → write.pageId < count
  | 0, write, member => by simp [changedWrites] at member
  | count + 1, write, member => by
      unfold changedWrites at member
      split at member
      next unchanged =>
        exact Nat.lt_trans (changedWrites_pageId_lt old target member)
          (Nat.lt_succ_self count)
      next changed =>
        simp only [List.mem_cons] at member
        rcases member with equal | tailMember
        · subst write
          simp
        · exact Nat.lt_trans (changedWrites_pageId_lt old target tailMember)
            (Nat.lt_succ_self count)

/-- Every emitted write is necessary: its page is outside the old image or
has contents different from the old page at that id. -/
theorem changedWrites_is_changed (old target : Image pageSize) :
    ∀ {count : Nat} {write : PageWrite pageSize},
      write ∈ changedWrites old target count →
        ¬ (write.pageId < old.pageCount ∧
          old.read write.pageId = target.read write.pageId)
  | 0, write, member => by simp [changedWrites] at member
  | count + 1, write, member => by
      unfold changedWrites at member
      split at member
      next unchanged => exact changedWrites_is_changed old target member
      next changed =>
        simp only [List.mem_cons] at member
        rcases member with equal | tailMember
        · subst write
          exact changed
        · exact changedWrites_is_changed old target tailMember

private theorem apply_changedWrites_pageCount_aux
    (old target base : Image pageSize) (oldLeBase : old.pageCount ≤ base.pageCount) :
    ∀ count,
      (applyWrites base (changedWrites old target count)).pageCount =
        max base.pageCount count
  | 0 => by simp [applyWrites, changedWrites]
  | count + 1 => by
      unfold changedWrites
      split
      next unchanged =>
        rw [apply_changedWrites_pageCount_aux old target base oldLeBase]
        omega
      next changed =>
        change (applyWrites (base.write ⟨count, target.read count⟩)
          (changedWrites old target count)).pageCount =
            max base.pageCount (count + 1)
        rw [apply_changedWrites_pageCount_aux old target
          (base.write ⟨count, target.read count⟩)]
        simp [Image.write]
        simp [Image.write]
        omega

theorem apply_changedWrites_pageCount (old target : Image pageSize) :
    ∀ count,
      (applyWrites old (changedWrites old target count)).pageCount =
        max old.pageCount count := by
  intro count
  exact apply_changedWrites_pageCount_aux old target old (Nat.le_refl _) count

private theorem apply_changedWrites_read_aux
    (old target base : Image pageSize) :
    ∀ {count pageId : Nat}, pageId < count →
      (∀ candidate, candidate < count →
        base.read candidate = old.read candidate) →
      (applyWrites base (changedWrites old target count)).read pageId =
        target.read pageId
  | 0, pageId, bound => by omega
  | count + 1, pageId, bound => by
      intro baseOld
      unfold changedWrites
      split
      next unchanged =>
        by_cases last : pageId = count
        · subst pageId
          rw [applyWrites_read_of_not_written]
          · exact (baseOld count (by omega)).trans unchanged.2
          · intro write member
            have below := changedWrites_pageId_lt old target member
            omega
        · have below : pageId < count := by omega
          exact apply_changedWrites_read_aux old target base below
            (fun candidate candidateBelow => baseOld candidate (by omega))
      next changed =>
        change (applyWrites (base.write ⟨count, target.read count⟩)
          (changedWrites old target count)).read pageId = target.read pageId
        by_cases last : pageId = count
        · subst pageId
          rw [applyWrites_read_of_not_written]
          · exact Image.read_write_same base ⟨count, target.read count⟩
          · intro write member
            have below := changedWrites_pageId_lt old target member
            omega
        · have below : pageId < count := by omega
          exact apply_changedWrites_read_aux old target
            (base.write ⟨count, target.read count⟩) below
            (fun candidate candidateBelow => by
              rw [Image.read_write_other]
              · exact baseOld candidate (by omega)
              · simpa using (Nat.ne_of_lt candidateBelow))

theorem apply_changedWrites_read (old target : Image pageSize) :
    ∀ {count pageId : Nat}, pageId < count →
      (applyWrites old (changedWrites old target count)).read pageId =
        target.read pageId := by
  intro count pageId bound
  exact apply_changedWrites_read_aux old target old bound
    (fun _ _ => rfl)

/-- The minimal whole-image update used by live commits. -/
def deltaWrites (old target : Image pageSize) :
    List (PageWrite pageSize) :=
  changedWrites old target target.pageCount

/-- Applying the changed-page transaction yields exactly the target image
whenever the file is not being shrunk. -/
theorem apply_deltaWrites_equiv (old target : Image pageSize)
    (doesNotShrink : old.pageCount ≤ target.pageCount) :
    (applyWrites old (deltaWrites old target)).Equiv target := by
  constructor
  · rw [deltaWrites, apply_changedWrites_pageCount]
    omega
  · intro pageId bound
    have targetBound : pageId < target.pageCount := by
      rw [deltaWrites, apply_changedWrites_pageCount] at bound
      omega
    exact apply_changedWrites_read old target targetBound

theorem deltaWrites_is_changed (old target : Image pageSize)
    {write : PageWrite pageSize} (member : write ∈ deltaWrites old target) :
    ¬ (write.pageId < old.pageCount ∧
      old.read write.pageId = target.read write.pageId) :=
  changedWrites_is_changed old target member

structure UndoRecord (pageSize : Nat) where
  pageId : Nat
  before : Storage.Page pageSize
  deriving Repr

structure Journal (pageSize : Nat) where
  originalPageCount : Nat
  undo : List (UndoRecord pageSize)
  deriving Repr

def buildUndo (old : Image pageSize) :
    List (PageWrite pageSize) → List (UndoRecord pageSize)
  | [] => []
  | write :: writes =>
      if write.pageId < old.pageCount then
        ⟨write.pageId, old.read write.pageId⟩ :: buildUndo old writes
      else
        buildUndo old writes

def makeJournal (old : Image pageSize) (writes : List (PageWrite pageSize)) :
    Journal pageSize := {
  originalPageCount := old.pageCount
  undo := buildUndo old writes }

def undoLookup (pageId : Nat) : List (UndoRecord pageSize) →
    Option (Storage.Page pageSize)
  | [] => none
  | record :: records =>
      if record.pageId = pageId then some record.before
      else undoLookup pageId records

/-- Exact page-level meaning of a rollback journal.  Every stored record is a
pre-image of a page actually targeted by the transaction, and every targeted
page that existed in the old image is recoverable through `undoLookup`. -/
def Journal.ExactPreimages (journal : Journal pageSize) (old : Image pageSize)
    (writes : List (PageWrite pageSize)) : Prop :=
  journal.originalPageCount = old.pageCount ∧
    (∀ record ∈ journal.undo,
      record.pageId < old.pageCount ∧
      record.before = old.read record.pageId ∧
      ∃ write ∈ writes, write.pageId = record.pageId) ∧
    (∀ write ∈ writes, write.pageId < old.pageCount →
      undoLookup write.pageId journal.undo = some (old.read write.pageId))

theorem undoLookup_buildUndo_of_mem (old : Image pageSize)
    (writes : List (PageWrite pageSize)) (write : PageWrite pageSize)
    (member : write ∈ writes) (withinOld : write.pageId < old.pageCount) :
    undoLookup write.pageId (buildUndo old writes) = some (old.read write.pageId) := by
  induction writes with
  | nil => simp at member
  | cons head writes induction =>
      simp only [List.mem_cons] at member
      unfold buildUndo
      split
      next headWithin =>
        unfold undoLookup
        split
        next same =>
          have pageIdEqual : head.pageId = write.pageId := same
          simp [pageIdEqual]
        next different =>
          rcases member with equal | tailMember
          · subst write
            exact (different rfl).elim
          · exact induction tailMember
      next headOutside =>
        rcases member with equal | tailMember
        · subst write
          exact (headOutside withinOld).elim
        · exact induction tailMember

theorem undoLookup_buildUndo_some_implies_mem (old : Image pageSize)
    (writes : List (PageWrite pageSize)) (pageId : Nat)
    {before : Storage.Page pageSize}
    (lookup : undoLookup pageId (buildUndo old writes) = some before) :
    ∃ write ∈ writes, write.pageId = pageId := by
  induction writes with
  | nil => simp [buildUndo, undoLookup] at lookup
  | cons write writes induction =>
      unfold buildUndo at lookup
      split at lookup
      next withinOld =>
        unfold undoLookup at lookup
        split at lookup
        next same => exact ⟨write, by simp, same⟩
        next different =>
          rcases induction lookup with ⟨witness, member, equal⟩
          exact ⟨witness, by simp [member], equal⟩
      next outside =>
        rcases induction lookup with ⟨witness, member, equal⟩
        exact ⟨witness, by simp [member], equal⟩

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

private theorem CrashOutcome.noPending_unique (cache : Cache pageSize)
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

private theorem CrashOutcome.restore_old (old : Image pageSize)
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

private theorem JournalCrashOutcome.noPending_unique
    (cache : JournalCache pageSize) (recovered : Option (Journal pageSize))
    (empty : cache.pending = none) (outcome : JournalCrashOutcome cache recovered) :
    recovered = cache.durable := by
  rcases outcome with durable | ⟨value, pending, recovered⟩
  · exact durable
  · rw [empty] at pending
    contradiction

private theorem JournalCrashOutcome.pending_cases
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
