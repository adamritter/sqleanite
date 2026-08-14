namespace SQLeanite
namespace PageReuse

/-!
# Safe page reuse across durability and reader epochs

A freed page is reusable only after its freeing transaction is durable and
after every reader which could still reference its previous contents has
finished. `oldestReaderEpoch` is the lower bound of active snapshots.
-/

structure FreePage where
  pageId : Nat
  safeAfterEpoch : Nat
  durable : Bool := false
  deriving DecidableEq, Repr

def FreePage.CanReuse (page : FreePage) (oldestReaderEpoch : Nat) : Prop :=
  page.durable = true ∧ page.safeAfterEpoch < oldestReaderEpoch

/-- A durability barrier publishes all page-free records in this batch. -/
def crossDurabilityBarrier (pages : List FreePage) : List FreePage :=
  pages.map fun page => { page with durable := true }

/-- Remove and return the first page satisfying both reuse barriers. -/
def takeReusable (oldestReaderEpoch : Nat) : List FreePage →
    Option (FreePage × List FreePage)
  | [] => none
  | page :: pages =>
      if page.durable && decide (page.safeAfterEpoch < oldestReaderEpoch) then
        some (page, pages)
      else
        match takeReusable oldestReaderEpoch pages with
        | none => none
        | some (chosen, remaining) => some (chosen, page :: remaining)

theorem takeReusable_sound {oldestReaderEpoch : Nat} {pages : List FreePage}
    {chosen : FreePage} {remaining : List FreePage}
    (selected : takeReusable oldestReaderEpoch pages = some (chosen, remaining)) :
    chosen.CanReuse oldestReaderEpoch := by
  induction pages generalizing chosen remaining with
  | nil => simp [takeReusable] at selected
  | cons page pages induction =>
      simp only [takeReusable] at selected
      split at selected
      next reusable =>
        simp only [Option.some.injEq, Prod.mk.injEq] at selected
        rcases selected with ⟨chosenEqual, remainingEqual⟩
        subst chosen
        simp only [Bool.and_eq_true, decide_eq_true_eq] at reusable
        exact reusable
      next notReusable =>
        cases tail : takeReusable oldestReaderEpoch pages with
        | none => simp [tail] at selected
        | some result =>
            rcases result with ⟨tailChosen, tailRemaining⟩
            simp only [tail, Option.some.injEq] at selected
            injection selected with chosenEqual remainingEqual
            subst chosen
            exact induction tail

theorem takeReusable_mem {oldestReaderEpoch : Nat} {pages : List FreePage}
    {chosen : FreePage} {remaining : List FreePage}
    (selected : takeReusable oldestReaderEpoch pages = some (chosen, remaining)) :
    chosen ∈ pages := by
  induction pages generalizing chosen remaining with
  | nil => simp [takeReusable] at selected
  | cons page pages induction =>
      simp only [takeReusable] at selected
      split at selected
      next reusable =>
        simp only [Option.some.injEq, Prod.mk.injEq] at selected
        rcases selected with ⟨chosenEqual, remainingEqual⟩
        subst chosen
        simp
      next notReusable =>
        cases tail : takeReusable oldestReaderEpoch pages with
        | none => simp [tail] at selected
        | some result =>
            rcases result with ⟨tailChosen, tailRemaining⟩
            simp only [tail, Option.some.injEq] at selected
            injection selected with chosenEqual remainingEqual
            subst chosen
            exact List.mem_cons_of_mem _ (induction tail)

theorem takeReusable_pending_none (pages : List FreePage)
    (pending : ∀ page ∈ pages, page.durable = false)
    (oldestReaderEpoch : Nat) :
    takeReusable oldestReaderEpoch pages = none := by
  induction pages with
  | nil => rfl
  | cons page pages induction =>
      have pagePending := pending page (by simp)
      have restPending : ∀ candidate ∈ pages, candidate.durable = false := by
        intro candidate member
        exact pending candidate (by simp [member])
      simp [takeReusable, pagePending, induction restPending]

theorem durabilityBarrier_preserves_pageIds (pages : List FreePage) :
    (crossDurabilityBarrier pages).map FreePage.pageId =
      pages.map FreePage.pageId := by
  simp [crossDurabilityBarrier]

theorem durabilityBarrier_makes_durable {page : FreePage} {pages : List FreePage}
    (member : page ∈ crossDurabilityBarrier pages) :
    page.durable = true := by
  simp only [crossDurabilityBarrier, List.mem_map] at member
  rcases member with ⟨before, _, equal⟩
  subst page
  rfl

/-- Even a durable free page cannot be reused while the oldest active reader
may still hold a reference from the page's freeing epoch. -/
theorem active_reader_blocks_reuse (page : FreePage) (oldestReaderEpoch : Nat)
    (readerMayReference : oldestReaderEpoch ≤ page.safeAfterEpoch) :
    ¬page.CanReuse oldestReaderEpoch := by
  intro reusable
  rcases reusable with ⟨_, safe⟩
  omega

end PageReuse
end SQLeanite
