import SQLeanite.Storage

namespace SQLeanite
namespace TornStorage

/-- Physical sector geometry within a database page.  A sector is the smallest
unit assumed to be atomically old or new after a torn page write. -/
structure SectorGeometry (pageSize : Nat) where
  sectorSize : Nat
  sectorSizePositive : 0 < sectorSize
  sectorsTilePage : pageSize % sectorSize = 0

def pageByte (page : Storage.Page pageSize) (offset : Fin pageSize) : UInt8 :=
  page.bytes[offset.val]'(by simp [page.sizeInvariant, offset.isLt])

/-- A crash may independently retain the old or new contents of each sector.
All bytes in one sector use the same choice, unlike an unconstrained byte-tear
model. -/
def SectorCrashOutcome (geometry : SectorGeometry pageSize)
    (old intended recovered : Storage.Page pageSize) : Prop :=
  ∃ newSectorSurvives : Nat → Bool,
    ∀ offset : Fin pageSize,
      pageByte recovered offset =
        if newSectorSurvives (offset.val / geometry.sectorSize) then
          pageByte intended offset
        else pageByte old offset

/-- Construct the exact post-crash page selected by a sector survival map. -/
def selectSectors (geometry : SectorGeometry pageSize)
    (newSectorSurvives : Nat → Bool)
    (old intended : Storage.Page pageSize) : Storage.Page pageSize := {
  bytes := Array.ofFn fun offset : Fin pageSize =>
    if newSectorSurvives (offset.val / geometry.sectorSize) then
      pageByte intended offset
    else pageByte old offset
  sizeInvariant := by simp }

theorem selectSectors_is_outcome (geometry : SectorGeometry pageSize)
    (newSectorSurvives : Nat → Bool)
    (old intended : Storage.Page pageSize) :
    SectorCrashOutcome geometry old intended
      (selectSectors geometry newSectorSurvives old intended) := by
  refine ⟨newSectorSurvives, ?_⟩
  intro offset
  simp [selectSectors, pageByte]

theorem old_is_outcome (geometry : SectorGeometry pageSize)
    (old intended : Storage.Page pageSize) :
    SectorCrashOutcome geometry old intended old := by
  refine ⟨fun _ => false, ?_⟩
  intro offset
  simp

theorem intended_is_outcome (geometry : SectorGeometry pageSize)
    (old intended : Storage.Page pageSize) :
    SectorCrashOutcome geometry old intended intended := by
  refine ⟨fun _ => true, ?_⟩
  intro offset
  simp

/-- The stronger assumption made by the original storage theorem. -/
def PageAtomicOutcome (old intended recovered : Storage.Page pageSize) : Prop :=
  recovered = old ∨ recovered = intended

theorem pageAtomic_is_sectorOutcome (geometry : SectorGeometry pageSize)
    (old intended recovered : Storage.Page pageSize)
    (atomic : PageAtomicOutcome old intended recovered) :
    SectorCrashOutcome geometry old intended recovered := by
  rcases atomic with equal | equal
  · subst recovered
    exact old_is_outcome geometry old intended
  · subst recovered
    exact intended_is_outcome geometry old intended

/-- Two two-byte sectors in a four-byte page, used for a constructive
non-vacuity witness. -/
def twoSectorGeometry : SectorGeometry 4 := {
  sectorSize := 2
  sectorSizePositive := by decide
  sectorsTilePage := by decide }

def oldWitnessPage : Storage.Page 4 := ⟨#[0, 0, 0, 0], by decide⟩
def intendedWitnessPage : Storage.Page 4 := ⟨#[1, 1, 1, 1], by decide⟩
def firstSectorSurvives (sector : Nat) : Bool := sector = 0
def tornWitnessPage : Storage.Page 4 :=
  selectSectors twoSectorGeometry firstSectorSurvives
    oldWitnessPage intendedWitnessPage

/-- Sector 0 survived while sector 1 did not: this is a genuinely torn page,
not merely another name for the atomic old/new outcomes. -/
theorem tornWitness_is_outcome :
    SectorCrashOutcome twoSectorGeometry oldWitnessPage intendedWitnessPage
      tornWitnessPage := by
  exact selectSectors_is_outcome twoSectorGeometry firstSectorSurvives
    oldWitnessPage intendedWitnessPage

theorem tornWitness_not_pageAtomic :
    ¬ PageAtomicOutcome oldWitnessPage intendedWitnessPage tornWitnessPage := by
  intro atomic
  rcases atomic with equal | equal
  · have firstEqual := congrArg
      (fun page => pageByte page (⟨0, by decide⟩ : Fin 4)) equal
    simp [tornWitnessPage, selectSectors, firstSectorSurvives, pageByte,
      twoSectorGeometry, oldWitnessPage, intendedWitnessPage] at firstEqual
  · have thirdEqual := congrArg
      (fun page => pageByte page (⟨2, by decide⟩ : Fin 4)) equal
    simp [tornWitnessPage, selectSectors, firstSectorSurvives, pageByte,
      twoSectorGeometry, oldWitnessPage, intendedWitnessPage] at thirdEqual

end TornStorage
end SQLeanite
