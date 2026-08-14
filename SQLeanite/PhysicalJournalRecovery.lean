import SQLeanite.PhysicalJournalCodec

namespace SQLeanite
namespace PhysicalJournalRecovery

def imagePages (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    List (Storage.Page PhysicalCodec.pageSize) :=
  (List.range image.pageCount).map image.read

theorem imagePages_length (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    (imagePages image).length = image.pageCount := by
  simp [imagePages]

def imageSizedPages (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    DiskFormat.SizedPages PhysicalCodec.pageSize image.pageCount :=
  ⟨imagePages image, imagePages_length image⟩

def imageBytes (image : GrowableStorage.Image PhysicalCodec.pageSize) : List UInt8 :=
  DiskFormat.encodePages (imagePages image)

/-- Decode an exact number of raw pages without trusting the SQLite header,
which may itself be one of the pages being rolled back. -/
def decodeImage (pageCount : Nat) (input : List UInt8) :
    Option (GrowableStorage.Image PhysicalCodec.pageSize) := do
  let (pages, suffix) ←
    DiskFormat.decodeSizedPages PhysicalCodec.pageSize pageCount input
  if _consumed : suffix = [] then
    some {
      pageCount
      read := fun pageId => pages.pages[pageId]?.getD
        (Storage.Page.zero PhysicalCodec.pageSize) }
  else none

theorem imagePages_getElem? (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (pageId : Nat) (bound : pageId < image.pageCount) :
    (imagePages image)[pageId]? = some (image.read pageId) := by
  simp [imagePages, bound]

theorem decodeImage_imageBytes (image :
    GrowableStorage.Image PhysicalCodec.pageSize) :
    ∃ decoded, decodeImage image.pageCount (imageBytes image) = some decoded ∧
      decoded.Equiv image := by
  let sized := imageSizedPages image
  have decodedPages := DiskFormat.decodeSizedPages_encode sized []
  simp only [List.append_nil] at decodedPages
  let decoded : GrowableStorage.Image PhysicalCodec.pageSize := {
    pageCount := image.pageCount
    read := fun pageId => sized.pages[pageId]?.getD
      (Storage.Page.zero PhysicalCodec.pageSize) }
  refine ⟨decoded, ?_, rfl, ?_⟩
  · dsimp [sized, imageSizedPages] at decodedPages
    unfold decodeImage imageBytes
    rw [decodedPages]
    rfl
  · intro pageId bound
    change (imagePages image)[pageId]?.getD
        (Storage.Page.zero PhysicalCodec.pageSize) = image.read pageId
    rw [imagePages_getElem? image pageId bound]
    rfl

def recoverBytes (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize)) : List UInt8 :=
  imageBytes (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal)

theorem imageBytes_eq_of_equiv {left right :
    GrowableStorage.Image PhysicalCodec.pageSize}
    (equivalent : left.Equiv right) : imageBytes left = imageBytes right := by
  unfold imageBytes imagePages
  have countEqual := equivalent.1
  rw [countEqual]
  congr 1
  apply List.map_congr_left
  intro pageId member
  apply equivalent.2 pageId
  simpa [countEqual] using member

/-- Exact-byte lifting of the growable old-or-new theorem. This is the pure
function now called by both rollback-journal executables after page parsing. -/
theorem rollbackCommit_recovery_bytes_atomic
    (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState old writes phase)
      recoveredMain recoveredJournal) :
    recoverBytes recoveredMain recoveredJournal = imageBytes old ∨
      recoverBytes recoveredMain recoveredJournal =
        imageBytes (GrowableStorage.applyWrites old writes) := by
  rcases GrowableStorage.rollbackCommit_crash_atomic old writes phase
      recoveredMain recoveredJournal outcome with restored | committed
  · exact .inl (imageBytes_eq_of_equiv restored)
  · exact .inr (imageBytes_eq_of_equiv committed)

end PhysicalJournalRecovery
end SQLeanite
