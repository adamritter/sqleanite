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

/-- A write set confined to existing page identifiers cannot grow the image.
This is the page-count frame used by localized point updates: it lets the old
SQLite header remain valid without reopening or decoding the whole file. -/
theorem applyWrites_pageCount_eq_of_forall_lt
    (image : Image pageSize) :
    ∀ (writes : List (PageWrite pageSize)),
      (∀ write ∈ writes, write.pageId < image.pageCount) →
      (applyWrites image writes).pageCount = image.pageCount
  | [], _ => rfl
  | head :: tail, bounded => by
      have headBound : head.pageId < image.pageCount :=
        bounded head (by simp)
      have headCount : (image.write head).pageCount = image.pageCount := by
        simp only [Image.write]
        omega
      change (applyWrites (image.write head) tail).pageCount = image.pageCount
      rw [applyWrites_pageCount_eq_of_forall_lt (image.write head) tail]
      · exact headCount
      · intro write member
        rw [headCount]
        exact bounded write (by simp [member])

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

/-- Tail-recursive implementation of `changedWrites` used by compiled commits.

The proof-facing definition above retains the direct descending-page
specification.  Its changed-page branch, however, waits to cons the current
write until the recursive call returns and therefore consumes one native stack
frame per page.  Large initial images reached that limit around 160,000 YCSB
rows.  This loop accumulates the same descending write sequence in reverse and
performs one tail-recursive reversal at the end. -/
def changedWritesGo (old target : Image pageSize) :
    Nat → List (PageWrite pageSize) → List (PageWrite pageSize)
  | 0, reversed => reversed.reverse
  | count + 1, reversed =>
      if _unchanged : count < old.pageCount ∧
          old.read count = target.read count then
        changedWritesGo old target count reversed
      else
        changedWritesGo old target count
          (⟨count, target.read count⟩ :: reversed)

def changedWritesTR (old target : Image pageSize)
    (count : Nat) : List (PageWrite pageSize) :=
  changedWritesGo old target count []

theorem changedWritesGo_eq (old target : Image pageSize) (count : Nat)
    (reversed : List (PageWrite pageSize)) :
    changedWritesGo old target count reversed =
      reversed.reverse ++ changedWrites old target count := by
  induction count generalizing reversed with
  | zero => simp [changedWritesGo, changedWrites]
  | succ count induction =>
      simp only [changedWritesGo, changedWrites]
      split
      next => exact induction reversed
      next =>
        rw [induction]
        simp [List.reverse_cons, List.append_assoc]

@[csimp] theorem changedWrites_eq_changedWritesTR :
    @changedWrites = @changedWritesTR := by
  funext pageSize old target count
  rw [changedWritesTR, changedWritesGo_eq]
  simp

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

end GrowableStorage

end SQLeanite
