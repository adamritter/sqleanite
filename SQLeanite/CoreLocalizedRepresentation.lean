import SQLeanite.CorePageCodec
import SQLeanite.CorePageSource
import SQLeanite.CoreChunkPageDelta

namespace SQLeanite
namespace CoreLocalizedRepresentation

/-!
# Local page deltas preserve table decoding

These lemmas isolate the two physical facts needed by the live localized
writer.  A changed encoded page is read from its exact write, and an omitted
page is read from the represented old image.  The resulting containment
certificate feeds the existing recursive table-decoder refinement directly;
there is no decode-and-compare admission check.
-/

/-- Every encoded page covered by one member of a distinct write set is
present in the page source obtained after applying that write set. -/
theorem pageSourceContains_applyWrites_of_covered
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pages : List CorePageCodec.NumberedPage)
    (covered : ∀ numbered ∈ pages,
      ∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) pages := by
  intro numbered member
  rcases covered numbered member with
    ⟨write, writeMember, pageNumber, bytes⟩
  rw [← pageNumber]
  rw [CorePageSource.readPage_applyWrites_of_mem image distinct writeMember]
  exact congrArg some bytes

/-- The write list emitted by `TableDelta.writes` immediately establishes the
decoder containment invariant for every page selected by that delta. -/
theorem pageSourceContains_tableDeltaPages
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (delta : CoreChunkPageDelta.TableDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (converted : CoreChunkPageDelta.writes delta = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId)) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.pages := by
  exact pageSourceContains_applyWrites_of_covered image writes distinct
    delta.pages (CoreChunkPageDelta.writes_covers_pages converted)

/-- A canonical old page that is in range and absent from the write set reads
identically after the delta. -/
theorem readPage_applyWrites_of_unchanged
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (numbered : CorePageCodec.NumberedPage)
    (positive : 0 < numbered.pageNumber)
    (oldBound : numbered.pageNumber ≤ image.pageCount)
    (oldRead : (CorePageSource.ofStorageImage image).readPage
      numbered.pageNumber = some numbered.page.bytes)
    (notWritten : ∀ write ∈ writes,
      write.pageId + 1 ≠ numbered.pageNumber) :
    (CorePageSource.ofStorageImage
      (GrowableStorage.applyWrites image writes)).readPage
        numbered.pageNumber = some numbered.page.bytes := by
  let pageId := numbered.pageNumber - 1
  have pageNumber : pageId + 1 = numbered.pageNumber := by
    simp only [pageId]
    omega
  have oldPageIdBound : pageId < image.pageCount := by
    simp only [pageId]
    omega
  have newPageIdBound :
      pageId < (GrowableStorage.applyWrites image writes).pageCount := by
    have growth := CorePageSource.applyWrites_pageCount_ge image writes
    omega
  rw [← pageNumber]
  rw [CorePageSource.readPage_applyWrites_of_not_written image writes pageId
    newPageIdBound oldPageIdBound]
  · simpa [pageNumber] using oldRead
  · intro write member equal
    exact notWritten write member (by omega)

/-- A mixed local delta contains a complete encoded page set when every page
is either supplied by the delta or certified unchanged from the old image. -/
theorem pageSourceContains_applyWrites
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pages : List CorePageCodec.NumberedPage)
    (accounted : ∀ numbered ∈ pages,
      (∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) ∨
      (0 < numbered.pageNumber ∧
        numbered.pageNumber ≤ image.pageCount ∧
        (CorePageSource.ofStorageImage image).readPage numbered.pageNumber =
          some numbered.page.bytes ∧
        ∀ write ∈ writes, write.pageId + 1 ≠ numbered.pageNumber)) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) pages := by
  intro numbered member
  rcases accounted numbered member with changed | unchanged
  · rcases changed with ⟨write, writeMember, pageNumber, bytes⟩
    rw [← pageNumber]
    rw [CorePageSource.readPage_applyWrites_of_mem image distinct writeMember]
    exact congrArg some bytes
  · exact readPage_applyWrites_of_unchanged image writes numbered
      unchanged.1 unchanged.2.1 unchanged.2.2.1 unchanged.2.2.2

/-- Decoding a canonical persistent table after a local page delta returns
exactly the logical table carried by the proof-carrying state.  Tree pages are
identified and may be sparse; overflow pages retain their separately allocated
contiguous interval. -/
theorem decodeTableFrom_of_pageSourceContains
    (source : CoreDecode.PageSource)
    (state : CoreChunkPageState.TableState)
    (nextOverflow : Nat) (encoding : CorePageCodec.OverflowEncoding)
    (encoded : CorePageCodec.encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (treeContains : CorePageCodec.PageSourceContains source
      encoding.treePages)
    (overflowContains : CoreDecode.ReadsPagesFrom source nextOverflow
      encoding.overflowPages)
    (heightBound : state.tree.root.erase.height < source.pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length < source.pageCount + 1) :
    CoreDecode.decodeTableFrom source
      (CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry state)) =
      some state.table.withoutIndexes := by
  exact CorePageCodec.decodeTableFrom_encodeChunkNodeWithOverflow source state
    nextOverflow encoding encoded treeContains overflowContains heightBound
    nextPositive pageBound fuelBound

/-- Direct storage-image specialization used by a localized table writer. -/
theorem decodeTableFrom_applyWrites
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (state : CoreChunkPageState.TableState)
    (nextOverflow : Nat) (encoding : CorePageCodec.OverflowEncoding)
    (encoded : CorePageCodec.encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (accounted : ∀ numbered ∈ encoding.treePages,
      (∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) ∨
      (0 < numbered.pageNumber ∧
        numbered.pageNumber ≤ image.pageCount ∧
        (CorePageSource.ofStorageImage image).readPage numbered.pageNumber =
          some numbered.page.bytes ∧
        ∀ write ∈ writes, write.pageId + 1 ≠ numbered.pageNumber))
    (overflowContains : CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      nextOverflow encoding.overflowPages)
    (heightBound : state.tree.root.erase.height <
      (GrowableStorage.applyWrites image writes).pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length <
      (GrowableStorage.applyWrites image writes).pageCount + 1) :
    CoreDecode.decodeTableFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      (CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry state)) =
      some state.table.withoutIndexes := by
  exact decodeTableFrom_of_pageSourceContains _ state nextOverflow encoding
    encoded
    (pageSourceContains_applyWrites image writes distinct encoding.treePages
      accounted)
    overflowContains (by simpa using heightBound) nextPositive pageBound
    (by simpa using fuelBound)

end CoreLocalizedRepresentation
end SQLeanite
