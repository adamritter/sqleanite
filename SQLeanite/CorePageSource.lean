import SQLeanite.CoreDecode
import SQLeanite.PhysicalJournalRecovery

namespace SQLeanite
namespace CorePageSource

/-!
# Growable storage as a decoder page source

This is the refinement boundary shared by localized encoding and durability.
SQLite numbers pages from one, while the storage protocol numbers them from
zero.  The definitions below make that translation once and prove that page
writes have exactly the reads expected by the decoder.
-/

def ofStorageImage
    (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    CoreDecode.PageSource :=
  .ofList ((PhysicalJournalRecovery.imagePages image).map
    (fun page => page.bytes.toList))

theorem imageBytes_eq_flatten
    (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    PhysicalJournalRecovery.imageBytes image =
      ((PhysicalJournalRecovery.imagePages image).map
        (fun page => page.bytes.toList)).flatten := by
  unfold PhysicalJournalRecovery.imageBytes
  generalize PhysicalJournalRecovery.imagePages image = pages
  induction pages with
  | nil => rfl
  | cons page pages induction =>
      simp [DiskFormat.encodePages, induction]

theorem pages_imageBytes
    (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    CoreDecode.pages image.pageCount
        (PhysicalJournalRecovery.imageBytes image) =
      (PhysicalJournalRecovery.imagePages image).map
        (fun page => page.bytes.toList) := by
  rw [imageBytes_eq_flatten]
  rw [← show ((PhysicalJournalRecovery.imagePages image).map
      (fun page => page.bytes.toList)).length = image.pageCount by
    simp [PhysicalJournalRecovery.imagePages_length]]
  apply CoreDecode.pages_flatten
  intro bytes member
  simp only [List.mem_map] at member
  rcases member with ⟨page, _, rfl⟩
  simpa using page.sizeInvariant

@[simp] theorem ofStorageImage_pageCount
    (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    (ofStorageImage image).pageCount = image.pageCount := by
  simp [ofStorageImage, CoreDecode.PageSource.ofList,
    PhysicalJournalRecovery.imagePages_length]

theorem readPage_ofStorageImage
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (pageId : Nat) (bound : pageId < image.pageCount) :
    (ofStorageImage image).readPage (pageId + 1) =
      some (image.read pageId).bytes.toList := by
  simp [ofStorageImage, CoreDecode.PageSource.ofList, CoreDecode.page?,
    PhysicalJournalRecovery.imagePages, bound]

theorem readPage_zero
    (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    (ofStorageImage image).readPage 0 = none := by
  simp [ofStorageImage, CoreDecode.PageSource.ofList, CoreDecode.page?]

theorem applyWrites_pageCount_ge
    (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    ∀ writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize),
      image.pageCount ≤ (GrowableStorage.applyWrites image writes).pageCount
  | [] => by simp [GrowableStorage.applyWrites]
  | write :: writes => by
      change image.pageCount ≤
        (GrowableStorage.applyWrites (image.write write) writes).pageCount
      exact Nat.le_trans (Nat.le_max_left _ _)
        (applyWrites_pageCount_ge (image.write write) writes)

theorem pageId_lt_applyWrites_of_mem
    (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    ∀ {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
      {write : GrowableStorage.PageWrite PhysicalCodec.pageSize},
      write ∈ writes →
      write.pageId < (GrowableStorage.applyWrites image writes).pageCount
  | [], write, member => by simp at member
  | head :: writes, write, member => by
      change write.pageId <
        (GrowableStorage.applyWrites (image.write head) writes).pageCount
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst write
        apply Nat.lt_of_lt_of_le
        · exact Nat.lt_succ_self head.pageId
        · exact Nat.le_trans (Nat.le_max_right _ _)
            (applyWrites_pageCount_ge (image.write head) writes)
      · exact pageId_lt_applyWrites_of_mem (image.write head) member

theorem applyWrites_read_of_mem
    (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    ∀ {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
      (_distinct : writes.Pairwise
        (fun left right => left.pageId ≠ right.pageId))
      {write : GrowableStorage.PageWrite PhysicalCodec.pageSize},
      write ∈ writes →
      (GrowableStorage.applyWrites image writes).read write.pageId = write.page
  | [], _, write, member => by simp at member
  | head :: writes, distinct, write, member => by
      change (GrowableStorage.applyWrites (image.write head) writes).read
        write.pageId = write.page
      simp only [List.pairwise_cons] at distinct
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst write
        rw [GrowableStorage.applyWrites_read_of_not_written]
        · exact GrowableStorage.Image.read_write_same image head
        · intro later laterMember
          exact distinct.1 later laterMember
      · exact applyWrites_read_of_mem (image.write head) distinct.2 member

theorem readPage_applyWrites_of_mem
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {write : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (member : write ∈ writes) :
    (ofStorageImage (GrowableStorage.applyWrites image writes)).readPage
        (write.pageId + 1) = some write.page.bytes.toList := by
  rw [readPage_ofStorageImage]
  · rw [applyWrites_read_of_mem image distinct member]
  · exact pageId_lt_applyWrites_of_mem image member

theorem readPage_applyWrites_of_not_written
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (pageId : Nat)
    (bound : pageId < (GrowableStorage.applyWrites image writes).pageCount)
    (oldBound : pageId < image.pageCount)
    (notWritten : ∀ write ∈ writes, pageId ≠ write.pageId) :
    (ofStorageImage (GrowableStorage.applyWrites image writes)).readPage
        (pageId + 1) =
      (ofStorageImage image).readPage (pageId + 1) := by
  rw [readPage_ofStorageImage _ pageId bound,
    readPage_ofStorageImage image pageId oldBound]
  rw [GrowableStorage.applyWrites_read_of_not_written image writes pageId
    notWritten]

theorem readPage_write_same
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (write : GrowableStorage.PageWrite PhysicalCodec.pageSize) :
    (ofStorageImage (image.write write)).readPage (write.pageId + 1) =
      some write.page.bytes.toList := by
  rw [readPage_ofStorageImage]
  · rw [GrowableStorage.Image.read_write_same]
  · simp only [GrowableStorage.Image.write]
    omega

theorem readPage_write_other
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (write : GrowableStorage.PageWrite PhysicalCodec.pageSize)
    (pageId : Nat) (oldBound : pageId < image.pageCount)
    (different : pageId ≠ write.pageId) :
    (ofStorageImage (image.write write)).readPage (pageId + 1) =
      (ofStorageImage image).readPage (pageId + 1) := by
  rw [readPage_ofStorageImage, readPage_ofStorageImage image pageId oldBound]
  · rw [GrowableStorage.Image.read_write_other image write pageId different]
  · simp only [GrowableStorage.Image.write]
    omega

end CorePageSource
end SQLeanite
