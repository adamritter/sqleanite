import SQLeanite.CoreChunkPageDelta.UpdateStateFreePagesEqOfIndexed
import SQLeanite.CoreLocalizedRepresentation.ExistsDatabaseOnSourceEncodeBulkIn

namespace SQLeanite
namespace CoreLocalizedRepresentation

/-- Extend an indexed table delta across a larger final write list.  Base
writes retain their provenance in the changed table; every framing write added
afterward is handled by a separate below-index proof.  This is the exact shape
of the live planner, which adds page zero (and, on shrinking commits, a
freelist trunk) before journaling. -/
def DatabaseOnSource.updateStateApplyWritesBelowExtension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (physical : DatabaseOnSource (CorePageSource.ofStorageImage image) state)
    (allocation : state.AllocationWellFormed)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage image).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites image finalWrites)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog))
    (retained : ∀ (old : CoreChunkPageState.TableState)
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      TableOnSource (CorePageSource.ofStorageImage image) old →
        TableOnSource
          (CorePageSource.ofStorageImage
            (GrowableStorage.applyWrites image finalWrites))
          (old.retarget table equivalent))
    (changed : TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) delta.table.after)
    (indexed : delta.table.before.table.indexes ≠ [])
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (addedBelow : ∀ entries,
      TablePagesBeforeIndexRoots state.tables entries →
      ∀ write ∈ finalWrites, write ∉ baseWrites →
        ∀ entry ∈ entries, write.pageId + 1 < entry.rootPage)
    (inline : changed.encoding.overflowPages = []) :
    DatabaseOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) delta.after := by
  refine physical.updateState allocation updated catalogPreserved retained
    changed ?_ ?_
  · intro entries metadata owned separation
    have afterEncoded := changed.inlineEncoded inline
    have selectedPages := CoreChunkPageDelta.updateState?_treePagesSelected
      updated changed.encoding.treePages afterEncoded
    have selectedTable :=
      CoreChunkPageDelta.updateState?_selected_mem updated
    have activePages :=
      CoreChunkPageDelta.updateState?_activePageIds_eq_of_indexed updated
        indexed
    have below : ∀ entry ∈ entries, ∀ write ∈ finalWrites,
        write.pageId + 1 < entry.rootPage := by
      intro entry entryMember write writeMember
      by_cases base : write ∈ baseWrites
      · rcases CoreChunkPageDelta.writes_sources_pages converted write base
            with ⟨page, pageMember, pageNumber, pageBytes⟩
        have selectedPage := selectedPages page pageMember
        have pageNumberMember : page.pageNumber ∈
            delta.table.after.tree.root.pageIds := by
          rw [← CorePageCodec.encodeChunkNodeWithOverflow_pageNumbers
            delta.table.after.table.schema delta.table.after.tree.root
            changed.nextOverflow changed.encoding changed.encoded]
          exact List.mem_map_of_mem selectedPage
        have afterActive : page.pageNumber ∈ delta.after.activePageIds := by
          unfold CoreChunkPageState.State.activePageIds
            CoreChunkPageState.tablePageIds
          exact List.mem_flatMap.mpr ⟨delta.table.after, selectedTable.2,
            by simpa [CoreChunkPageState.TableState.pageIds] using
              pageNumberMember⟩
        have beforeActive : page.pageNumber ∈ state.activePageIds := by
          rw [← activePages]
          exact afterActive
        rw [pageNumber]
        exact separation page.pageNumber beforeActive entry entryMember
      · exact addedBelow entries separation write writeMember base entry
          entryMember
    exact (owned.applyWritesBelow image finalWrites distinct below).retarget
      (updateState?_indexImagesAligned updated)
  · intro entries metadata separation
    unfold TablePagesBeforeIndexRoots at separation ⊢
    intro pageId pageMember entry entryMember
    have active : pageId ∈ delta.after.activePageIds := pageMember
    rw [CoreChunkPageDelta.updateState?_activePageIds_eq_of_indexed updated
      indexed] at active
    exact separation pageId active entry entryMember

/-- Storage-image specialization of `updateState`.  It derives—rather than
assumes—that every emitted indexed-table write is below every catalogued index
root. Exact index bytes and the separation invariant are then transported by
the ownership certificate itself. -/
def DatabaseOnSource.updateStateApplyWritesBelow
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (physical : DatabaseOnSource (CorePageSource.ofStorageImage image) state)
    (allocation : state.AllocationWellFormed)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage image).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites image writes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog))
    (retained : ∀ (old : CoreChunkPageState.TableState)
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      TableOnSource (CorePageSource.ofStorageImage image) old →
        TableOnSource
          (CorePageSource.ofStorageImage
            (GrowableStorage.applyWrites image writes))
          (old.retarget table equivalent))
    (changed : TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.table.after)
    (indexed : delta.table.before.table.indexes ≠ [])
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (inline : changed.encoding.overflowPages = []) :
    DatabaseOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.after := by
  apply physical.updateStateApplyWritesBelowExtension image writes writes
    distinct allocation updated catalogPreserved retained changed indexed
    converted
  · intro entries separation write member notBase
    exact False.elim (notBase member)
  · exact inline

/-- A successfully encoded index run plus exact post-write page reads gives
the physical index premise consumed by `IndexGroupsDecode`. -/
theorem IndexesDecode.consEncoded
    {source : CoreDecode.PageSource} {table : Core.Table}
    {entry : CoreDecode.CatalogEntry}
    {entries : List CoreDecode.CatalogEntry} {index : Core.Index}
    {rootPage : Nat} {encoding : CoreOverflow.IndexEncoding}
    (sameTable : entry.table = table.schema.name)
    (sameRoot : entry.rootPage = rootPage)
    (metadata : CoreDecode.decodeCanonicalIndex table.schema
      table.schema.name entry = some index)
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : CoreDecode.ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (tail : IndexesDecode source table entries) :
    IndexesDecode source table (entry :: entries) := by
  refine IndexesDecode.cons sameTable metadata ?_ tail
  rw [sameRoot]
  simpa only [CoreDecode.expectedIndexEntries] using
    CoreDecode.decodeIndexSubtreeFrom_encodeIndex source encoded reads
      rootPositive pageBound withinSource

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

/-- Transport an unchanged table certificate across a disjoint physical write
set.  Every tree and overflow byte is read from the old image; the proof makes
the noninterference condition explicit instead of relying on a whole-file
decode after the write. -/
def TableOnSource.applyWritesOfUntouched
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (state : CoreChunkPageState.TableState)
    (physical : TableOnSource (CorePageSource.ofStorageImage image) state)
    (treeBounds : ∀ numbered ∈ physical.encoding.treePages,
      0 < numbered.pageNumber ∧ numbered.pageNumber ≤ image.pageCount)
    (treeUntouched : ∀ numbered ∈ physical.encoding.treePages,
      ∀ write ∈ writes, write.pageId + 1 ≠ numbered.pageNumber)
    (overflowBounds : ∀ (offset : Nat)
      (_inBounds : offset < physical.encoding.overflowPages.length),
      0 < physical.nextOverflow + offset ∧
        physical.nextOverflow + offset ≤ image.pageCount)
    (overflowUntouched : ∀ (offset : Nat)
      (_inBounds : offset < physical.encoding.overflowPages.length),
      ∀ write ∈ writes,
        write.pageId + 1 ≠ physical.nextOverflow + offset) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) state := by
  refine TableOnSource.transport
    (newSource := CorePageSource.ofStorageImage
      (GrowableStorage.applyWrites image writes)) physical (by
        simpa only [CorePageSource.ofStorageImage_pageCount] using
          CorePageSource.applyWrites_pageCount_ge image writes) ?_ ?_
  · apply pageSourceContains_applyWrites image writes distinct
      physical.encoding.treePages
    intro numbered member
    exact .inr ⟨(treeBounds numbered member).1,
      (treeBounds numbered member).2, physical.treeContains numbered member,
      treeUntouched numbered member⟩
  · apply readsPagesFrom_applyWrites image writes distinct
      physical.nextOverflow physical.encoding.overflowPages
    intro offset inBounds
    exact .inr ⟨(overflowBounds offset inBounds).1,
      (overflowBounds offset inBounds).2,
      physical.overflowContains offset inBounds,
      overflowUntouched offset inBounds⟩

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

/-- Frame `pageSourceContains_tableDeltaComplete` across the header/freelist
augmentation performed immediately before the live syscall trace.  The base
delta still supplies every changed table page, while the final write set is
allowed to contain additional pages provided those additions cannot alias a
post-state table page.

This is deliberately phrased over membership rather than list concatenation:
the live planner may prepend page zero and a freelist trunk, and the exact
ordering of the final distinct writes is irrelevant to the represented table
bytes. -/
theorem pageSourceContains_tableDeltaComplete_extension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (delta : CoreChunkPageDelta.TableDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (converted : CoreChunkPageDelta.writes delta = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterPages, write.pageId + 1 ≠ page.pageNumber)
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
        (GrowableStorage.applyWrites image finalWrites)) afterPages := by
  apply pageSourceContains_applyWrites image finalWrites distinct afterPages
  intro page pageMember
  by_cases selectedMember : page ∈ delta.pages
  · left
    rcases CoreChunkPageDelta.writes_covers_pages converted page selectedMember
        with ⟨write, writeMember, pageNumber, bytes⟩
    exact ⟨write, baseMember write writeMember, pageNumber, bytes⟩
  · right
    have oldMember : page ∈ beforePages := by
      rcases accounted page pageMember with changed | unchanged
      · exact False.elim (selectedMember changed)
      · exact unchanged
    refine ⟨(oldBounds page oldMember).1, (oldBounds page oldMember).2,
      oldContains page oldMember, ?_⟩
    intro write writeMember samePage
    by_cases baseWrite : write ∈ baseWrites
    · rcases CoreChunkPageDelta.writes_sources_pages converted write baseWrite
          with ⟨source, sourceMember, sourcePage, sourceBytes⟩
      have sourceAfter := selected source sourceMember
      have equal : source = page := numberedPage_eq_of_pageNumber_eq unique
        sourceAfter pageMember (sourcePage.symm.trans samePage)
      exact selectedMember (equal ▸ sourceMember)
    · exact addedUntouched write writeMember baseWrite page pageMember samePage

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

end CoreLocalizedRepresentation

end SQLeanite
