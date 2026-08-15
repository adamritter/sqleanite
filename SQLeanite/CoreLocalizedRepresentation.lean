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

/-- Per-table physical decoder certificates, aligned with the table entries in
the SQLite catalog.  This is the list-level bridge from each local tree proof
to `PageSourceRepresents.tablesRead`. -/
inductive TablesDecode (source : CoreDecode.PageSource) :
    List CoreDecode.CatalogEntry → List Core.Table → Prop where
  | nil : TablesDecode source [] []
  | cons {entry : CoreDecode.CatalogEntry}
      {entries : List CoreDecode.CatalogEntry}
      {table : Core.Table} {tables : List Core.Table}
      (head : CoreDecode.decodeTableFrom source entry =
        some table.withoutIndexes)
      (tail : TablesDecode source entries tables) :
      TablesDecode source (entry :: entries) (table :: tables)

theorem TablesDecode.mapM
    {source : CoreDecode.PageSource}
    {entries : List CoreDecode.CatalogEntry} {tables : List Core.Table}
    (decoded : TablesDecode source entries tables) :
    entries.mapM (CoreDecode.decodeTableFrom source) =
      some (tables.map Core.Table.withoutIndexes) := by
  induction decoded with
  | nil => rfl
  | cons head tail induction =>
      simp [head, induction]

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

private theorem numberedPage_eq_of_pageNumber_eq
    {pages : List CorePageCodec.NumberedPage}
    (unique : (pages.map CorePageCodec.NumberedPage.pageNumber).Nodup) :
    ∀ {left right : CorePageCodec.NumberedPage}, left ∈ pages →
      right ∈ pages → left.pageNumber = right.pageNumber → left = right := by
  induction pages with
  | nil => simp
  | cons head pages induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      intro left right leftMember rightMember pageNumber
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftLater
      · rcases rightMember with rfl | rightLater
        · rfl
        · exfalso
          exact unique.1 (List.mem_map.mpr
            ⟨right, rightLater, pageNumber.symm⟩)
      · rcases rightMember with rfl | rightLater
        · exfalso
          exact unique.1 (List.mem_map.mpr
            ⟨left, leftLater, pageNumber⟩)
        · exact induction unique.2 leftLater rightLater pageNumber

/-- Complete no-overflow table-page preservation from a `TableDelta`.

The accounting theorem supplies the logical partition; exact conversion gives
both directions between selected pages and writes; and unique post-state page
identities rule out a write aliasing an allegedly unchanged page.  This is the
component theorem needed before composing table pages with overflow, catalog,
freelist, and index components. -/
theorem pageSourceContains_tableDeltaComplete
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (delta : CoreChunkPageDelta.TableDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (converted : CoreChunkPageDelta.writes delta = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (accounted : ∀ page ∈ afterPages,
      page ∈ delta.pages ∨ page ∈ beforePages)
    (selected : ∀ page ∈ delta.pages, page ∈ afterPages)
    (unique : (afterPages.map
      CorePageCodec.NumberedPage.pageNumber).Nodup)
    (oldContains : CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage image) beforePages)
    (oldBounds : ∀ page ∈ beforePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) afterPages := by
  apply pageSourceContains_applyWrites image writes distinct afterPages
  intro page pageMember
  by_cases selectedMember : page ∈ delta.pages
  · left
    exact CoreChunkPageDelta.writes_covers_pages converted page selectedMember
  · right
    have oldMember : page ∈ beforePages := by
      rcases accounted page pageMember with changed | unchanged
      · exact False.elim (selectedMember changed)
      · exact unchanged
    refine ⟨(oldBounds page oldMember).1, (oldBounds page oldMember).2,
      oldContains page oldMember, ?_⟩
    intro write writeMember samePage
    rcases CoreChunkPageDelta.writes_sources_pages converted write writeMember
        with ⟨source, sourceMember, sourcePage, sourceBytes⟩
    have sourceAfter := selected source sourceMember
    have equal : source = page := numberedPage_eq_of_pageNumber_eq unique
      sourceAfter pageMember (sourcePage.symm.trans samePage)
    exact selectedMember (equal ▸ sourceMember)

/-- Live-state specialization.  The delta builder itself supplies accounting,
post-state selection, and active-page identity uniqueness; callers need only
provide the represented old bytes and the successful deterministic encodings.
-/
theorem pageSourceContains_updateStateTree
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (beforeEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some beforePages)
    (afterEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterPages)
    (oldContains : CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage image) beforePages)
    (oldBounds : ∀ page ∈ beforePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) afterPages := by
  apply pageSourceContains_tableDeltaComplete image delta.table writes
    beforePages afterPages converted distinct
  · exact CoreChunkPageDelta.updateState?_treePagesAccounted updated
      beforePages afterPages beforeEncoded afterEncoded
  · exact CoreChunkPageDelta.updateState?_treePagesSelected updated afterPages
      afterEncoded
  · rw [CorePageCodec.encodeChunkNode_pageNumbers _ _ _ afterEncoded]
    exact (CoreChunkPageDelta.updateState?_identityWellFormed updated).1
  · exact oldContains
  · exact oldBounds

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
