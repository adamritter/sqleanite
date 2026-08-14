import SQLeanite.PhysicalWAL

namespace SQLeanite
namespace PhysicalWALRecovery

open FileFormat

abbrev Image := GrowableStorage.Image PhysicalCodec.pageSize

def zeroU32 : U32Value := ⟨0, by decide⟩

def databaseSizeValue (image : Image) (fits : image.pageCount < 2 ^ 32) :
    U32Value :=
  ⟨image.pageCount, by simpa using fits⟩

/-- Emit every page in descending order.  The final frame is page one and is
the commit frame; its nonzero database-size field publishes the transaction. -/
def framesAux (target : Image) (databaseSize : U32Value) :
    (count : Nat) → count ≤ databaseSize.val → List PhysicalWAL.Frame
  | 0, _ => []
  | count + 1, within =>
      let pageValue : U32Value :=
        ⟨count + 1, Nat.lt_of_le_of_lt within databaseSize.isLt⟩
      let pageNumber : PageNumber := ⟨pageValue, Nat.zero_lt_succ count⟩
      let commitSize := if count = 0 then databaseSize else zeroU32
      { pageNumber := pageNumber
        databaseSize := commitSize
        page := target.read count } ::
      framesAux target databaseSize count (Nat.le_trans (Nat.le_succ count) within)

def frames (target : Image) (fits : target.pageCount < 2 ^ 32) :
    List PhysicalWAL.Frame :=
  framesAux target (databaseSizeValue target fits) target.pageCount
    (Nat.le_refl target.pageCount)

theorem framesAux_length (target : Image) (databaseSize : U32Value) :
    ∀ (count : Nat) (within : count ≤ databaseSize.val),
      (framesAux target databaseSize count within).length = count
  | 0, _ => rfl
  | count + 1, within => by
      simp only [framesAux, List.length_cons]
      rw [framesAux_length]

theorem frames_length (target : Image) (fits : target.pageCount < 2 ^ 32) :
    (frames target fits).length = target.pageCount := by
  exact framesAux_length target _ _ _

def frameWrite (frame : PhysicalWAL.Frame) :
    GrowableStorage.PageWrite PhysicalCodec.pageSize :=
  ⟨frame.pageNumber.value.val - 1, frame.page⟩

def applyFrames : Image → List PhysicalWAL.Frame → Image
  | image, [] => image
  | image, frame :: remaining =>
      applyFrames (image.write (frameWrite frame)) remaining

def resize (image : Image) (pageCount : Nat) : Image :=
  { pageCount, read := image.read }

/-- Scan every valid frame, remembering only states ended by a commit frame.
Trailing frames with database size zero are deliberately invisible after a
crash, while an earlier committed transaction remains recoverable. -/
def recoverFrames : Image → List PhysicalWAL.Frame → Option Image → Option Image
  | _, [], committed => committed
  | image, frame :: remaining, committed =>
      let next := image.write (frameWrite frame)
      let committed := if frame.databaseSize.val = 0 then committed
        else some (resize next frame.databaseSize.val)
      recoverFrames next remaining committed

def recover (main : Image) (wal : PhysicalWAL.WAL) : Option Image :=
  recoverFrames main wal.frames none

theorem framesAux_toWrites (target : Image) (databaseSize : U32Value) :
    ∀ (count : Nat) (within : count ≤ databaseSize.val),
      (framesAux target databaseSize count within).map
          frameWrite =
        GrowableStorage.fullWrites target count
  | 0, _ => rfl
  | count + 1, within => by
      simp only [framesAux, List.map_cons, GrowableStorage.fullWrites]
      rw [framesAux_toWrites]
      rfl

theorem frames_toWrites (target : Image) (fits : target.pageCount < 2 ^ 32) :
    (frames target fits).map frameWrite =
      GrowableStorage.replaceWrites target := by
  exact framesAux_toWrites target _ _ _

theorem applyFrames_eq_applyWrites (image : Image)
    (walFrames : List PhysicalWAL.Frame) :
    applyFrames image walFrames =
      GrowableStorage.applyWrites image
        (walFrames.map frameWrite) := by
  induction walFrames generalizing image with
  | nil => rfl
  | cons frame remaining induction =>
      simp only [applyFrames, List.map_cons, GrowableStorage.applyWrites,
        List.foldl_cons]
      exact induction _

theorem recoverFrames_framesAux (target : Image) (databaseSize : U32Value) :
    ∀ (count : Nat) (within : count ≤ databaseSize.val) (image : Image)
      (committed : Option Image), 0 < count →
      recoverFrames image (framesAux target databaseSize count within) committed =
        some (resize
          (GrowableStorage.applyWrites image
            (GrowableStorage.fullWrites target count)) databaseSize.val)
  | 0, _, _, _, positive => by omega
  | count + 1, within, image, committed, _ => by
      unfold framesAux recoverFrames
      by_cases last : count = 0
      · subst count
        have databaseSizePositive : databaseSize.val ≠ 0 := by omega
        simp [frameWrite, zeroU32, databaseSizePositive, framesAux,
          recoverFrames, GrowableStorage.fullWrites,
          GrowableStorage.applyWrites]
      · have countPositive : 0 < count := Nat.pos_of_ne_zero last
        simp only [last, if_false, zeroU32]
        simp only [if_pos True.intro]
        change recoverFrames
            (image.write ⟨count, target.read count⟩)
            (framesAux target databaseSize count _) committed = _
        rw [recoverFrames_framesAux target databaseSize count _ _ committed
          countPositive]
        rfl

theorem recover_frames (main target : Image)
    (fits : target.pageCount < 2 ^ 32) (targetPositive : 0 < target.pageCount)
    (header : PhysicalWAL.Header) :
    recover main { header, frames := frames target fits } =
      some (resize
        (GrowableStorage.applyWrites main
          (GrowableStorage.replaceWrites target)) target.pageCount) := by
  unfold recover frames GrowableStorage.replaceWrites databaseSizeValue
  exact recoverFrames_framesAux target _ target.pageCount _ main none targetPositive

theorem recover_frames_equiv (main target : Image)
    (fits : target.pageCount < 2 ^ 32) (targetPositive : 0 < target.pageCount)
    (header : PhysicalWAL.Header) :
    ∃ recovered,
      recover main { header, frames := frames target fits } = some recovered ∧
        recovered.Equiv target := by
  let applied := GrowableStorage.applyWrites main
    (GrowableStorage.replaceWrites target)
  let recovered := resize applied target.pageCount
  refine ⟨recovered, ?_, ?_⟩
  · exact recover_frames main target fits targetPositive header
  · constructor
    · rfl
    · intro pageId bound
      unfold recovered resize applied
      exact GrowableStorage.apply_fullWrites_read main target bound

end PhysicalWALRecovery
end SQLeanite
