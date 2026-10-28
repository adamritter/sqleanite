import SQLeanite.CoreDurability.SqliteHeaderMatchesStorageImageEncodeBulkFreelistEmpty

namespace SQLeanite
namespace CoreDurability

/-- Indexed ordinary mutations discharge the post-state allocator premise from
the same stable-identity delta and the old allocation proof already stored in
`PreparedOrdinaryDelta`; no decidable allocation check is executed again. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.changedTableOnFinalWritesIndexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (indexed : delta.table.before.table.indexes ≠ [])
    (final : CoreFileAdapter.PreparedLocalizedWrites delta.after.freePages
      prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (beforeInline :
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem
          prepared.updated).1)).encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem prepared.updated).1)).nextOverflow =
        some afterEncoding)
    (afterInline : afterEncoding.overflowPages = []) :
    CoreLocalizedRepresentation.TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage final.writes))
      delta.table.after := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  have sameHeight :=
    CoreChunkPageDelta.updateState?_selectedHeight_eq_of_indexed
      prepared.updated indexed
  have growth := CorePageSource.applyWrites_pageCount_ge oldImage final.writes
  have heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage final.writes)).pageCount + 1 := by
    rw [sameHeight]
    exact Nat.lt_of_lt_of_le before.heightBound
      (by simpa using Nat.add_le_add_right growth 1)
  exact CoreFileAdapter.PreparedOrdinaryDelta.changedTableOnFinalWrites prepared
    final oldImage physical
    (CoreChunkPageDelta.updateState?_allocationWellFormed_of_indexed
      prepared.allocation prepared.updated indexed)
    beforeInline afterEncoding afterEncoded afterInline heightBound

/-- Every write in the no-freelist indexed point-update plan targets an
already existing page.  Base writes inherit the unchanged persistent page-ID
set; the only possible framing addition is page zero. -/
theorem
    CoreFileAdapter.PreparedOrdinaryDelta.finalWrites_pageId_lt_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (indexed : delta.table.before.table.indexes ≠ [])
    (final : CoreFileAdapter.PreparedLocalizedWrites delta.after.freePages
      prepared.writes)
    (noFree : delta.after.freePages = [])
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (beforeInline :
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem
          prepared.updated).1)).encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem prepared.updated).1)).nextOverflow =
        some afterEncoding)
    (afterInline : afterEncoding.overflowPages = []) :
    ∀ write ∈ final.writes, write.pageId < oldImage.pageCount := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  have beforeInline' : before.encoding.overflowPages = [] := by
    simpa [before, selected] using beforeInline
  have beforeTree := before.inlineEncoded beforeInline'
  have afterEncoded' : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding := by
    simpa [before, selected] using afterEncoded
  have afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterEncoding.treePages :=
    CorePageCodec.encodeChunkNodeWithOverflow_noOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow afterEncoding afterEncoded' afterInline
  have sameIds := CoreChunkPageDelta.updateState?_selectedPageIds_of_indexed
    prepared.updated indexed
  have beforeNumbers := CorePageCodec.encodeChunkNode_pageNumbers
    delta.table.before.table.schema delta.table.before.tree.root
    before.encoding.treePages beforeTree
  have oldPositive : 0 < oldImage.pageCount := by
    have rootMember : delta.table.before.tree.root.rootId ∈
        delta.table.before.tree.root.pageIds :=
      PersistentPageTree.Node.rootId_mem_pageIds _
    rw [← beforeNumbers] at rootMember
    rcases List.mem_map.mp rootMember with
      ⟨rootPage, rootPageMember, rootNumber⟩
    have rootBound := before.treeBounds oldImage rootPage rootPageMember
    omega
  intro write writeMember
  rcases final.sources write writeMember with base | pageZero | trunk
  · rcases CoreChunkPageDelta.writes_sources_pages prepared.writesEq write base
        with ⟨page, pageMember, pageNumber, pageBytes⟩
    have selectedPage := CoreChunkPageDelta.updateState?_treePagesSelected
      prepared.updated afterEncoding.treePages afterTree page pageMember
    have afterId : page.pageNumber ∈
        delta.table.after.tree.root.pageIds := by
      rw [← CorePageCodec.encodeChunkNode_pageNumbers
        delta.table.after.table.schema delta.table.after.tree.root
          afterEncoding.treePages afterTree]
      exact List.mem_map_of_mem selectedPage
    rw [sameIds] at afterId
    rw [← beforeNumbers] at afterId
    rcases List.mem_map.mp afterId with
      ⟨oldPage, oldPageMember, oldNumber⟩
    have oldBound := before.treeBounds oldImage oldPage oldPageMember
    omega
  · rw [pageZero]
    exact oldPositive
  · rcases trunk with ⟨trunk, member, equal⟩
    rw [noFree] at member
    simp at member

/-- Indexed localized base writes cannot target page zero: every emitted page
belongs to the selected post-tree, whose stable page identity is an active
pre-state page strictly after the SQLite catalog page. -/
theorem CoreFileAdapter.PreparedOrdinaryDelta.baseWrites_pageId_pos_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (indexed : delta.table.before.table.indexes ≠ [])
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem prepared.updated).1)).nextOverflow =
        some afterEncoding)
    (afterInline : afterEncoding.overflowPages = []) :
    ∀ write ∈ prepared.writes, 0 < write.pageId := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  have afterEncoded' : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding := by
    simpa [before, selected] using afterEncoded
  have afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterEncoding.treePages :=
    CorePageCodec.encodeChunkNodeWithOverflow_noOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow afterEncoding afterEncoded' afterInline
  have activeIds := CoreChunkPageDelta.updateState?_activePageIds_eq_of_indexed
    prepared.updated indexed
  intro write writeMember
  rcases CoreChunkPageDelta.writes_sources_pages prepared.writesEq write
      writeMember with ⟨page, pageMember, pageNumber, pageBytes⟩
  have selectedPage := CoreChunkPageDelta.updateState?_treePagesSelected
    prepared.updated afterEncoding.treePages afterTree page pageMember
  have pageIdMember : page.pageNumber ∈
      delta.table.after.tree.root.pageIds := by
    rw [← CorePageCodec.encodeChunkNode_pageNumbers
      delta.table.after.table.schema delta.table.after.tree.root
        afterEncoding.treePages afterTree]
    exact List.mem_map_of_mem selectedPage
  have afterActive : page.pageNumber ∈ delta.after.activePageIds := by
    unfold CoreChunkPageState.State.activePageIds
      CoreChunkPageState.tablePageIds
    exact List.mem_flatMap.mpr ⟨delta.table.after, selected.2,
      by simpa [CoreChunkPageState.TableState.pageIds] using pageIdMember⟩
  have beforeActive : page.pageNumber ∈ state.activePageIds := by
    rw [← activeIds]
    exact afterActive
  have afterCatalog := prepared.allocation.active_after_catalog
    page.pageNumber beforeActive
  omega

/-- Transport an arbitrary unchanged inline table across the exact final write
list of an indexed localized commit.  Base writes are pages of the selected
post-tree; stable indexed page identity and allocator uniqueness separate them
from every other table.  Header/freelist additions use the planner's existing
active-page frame theorem.  This is the multi-table frame missing from the
former one-table specialization. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.retainedTableOnFinalWritesIndexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (indexed : delta.table.before.table.indexes ≠ [])
    (final : CoreFileAdapter.PreparedLocalizedWrites delta.after.freePages
      prepared.writes)
    (noFree : delta.after.freePages = [])
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (nextOverflow : Nat)
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      nextOverflow = some afterEncoding)
    (afterInline : afterEncoding.overflowPages = [])
    (old : CoreChunkPageState.TableState) (oldMember : old ∈ state.tables)
    (table : Core.Table) (equivalent : old.table.Equiv table)
    (different : old ≠ delta.table.before)
    (oldPhysical : CoreLocalizedRepresentation.TableOnSource
      (CorePageSource.ofStorageImage oldImage) old)
    (oldInline : oldPhysical.encoding.overflowPages = []) :
    CoreLocalizedRepresentation.TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage final.writes))
      (old.retarget table equivalent) := by
  have afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterEncoding.treePages :=
    CorePageCodec.encodeChunkNodeWithOverflow_noOverflow
      delta.table.after.table.schema delta.table.after.tree.root nextOverflow
      afterEncoding afterEncoded afterInline
  have selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  have stableIds := CoreChunkPageDelta.updateState?_selectedPageIds_of_indexed
    prepared.updated indexed
  have treeUntouched : ∀ numbered ∈ oldPhysical.encoding.treePages,
      ∀ write ∈ final.writes,
        write.pageId + 1 ≠ numbered.pageNumber := by
    intro numbered numberedMember write writeMember
    by_cases base : write ∈ prepared.writes
    · rcases CoreChunkPageDelta.writes_sources_pages prepared.writesEq
          write base with ⟨page, pageMember, pageNumber, pageBytes⟩
      have selectedPage := CoreChunkPageDelta.updateState?_treePagesSelected
        prepared.updated afterEncoding.treePages afterTree page pageMember
      have afterId : page.pageNumber ∈
          delta.table.after.tree.root.pageIds := by
        rw [← CorePageCodec.encodeChunkNode_pageNumbers
          delta.table.after.table.schema delta.table.after.tree.root
            afterEncoding.treePages afterTree]
        exact List.mem_map_of_mem selectedPage
      rw [stableIds] at afterId
      have oldPage : numbered.pageNumber ∈ old.tree.root.pageIds := by
        rw [← CorePageCodec.encodeChunkNodeWithOverflow_pageNumbers
          old.table.schema old.tree.root oldPhysical.nextOverflow
            oldPhysical.encoding oldPhysical.encoded]
        exact List.mem_map_of_mem numberedMember
      have separated := CoreChunkPageState.pageIds_disjoint_of_nodup
        prepared.allocation.1 delta.table.before selected.1 old oldMember
          different.symm page.pageNumber afterId
      intro alias
      have equalNumbers : page.pageNumber = numbered.pageNumber :=
        pageNumber.symm.trans alias
      apply separated
      simpa [equalNumbers, CoreChunkPageState.TableState.pageIds] using oldPage
    · have pageZero := final.added_pageZero_of_noFreePages noFree
          writeMember base
      have pageNumberMember : numbered.pageNumber ∈ old.tree.root.pageIds := by
        rw [← CorePageCodec.encodeChunkNodeWithOverflow_pageNumbers
          old.table.schema old.tree.root oldPhysical.nextOverflow
            oldPhysical.encoding oldPhysical.encoded]
        exact List.mem_map_of_mem numberedMember
      have active : numbered.pageNumber ∈ state.activePageIds := by
        unfold CoreChunkPageState.State.activePageIds
          CoreChunkPageState.tablePageIds
        exact List.mem_flatMap.mpr ⟨old, oldMember, by
          simpa [CoreChunkPageState.TableState.pageIds] using pageNumberMember⟩
      have afterCatalog := prepared.allocation.active_after_catalog
        numbered.pageNumber active
      intro alias
      rw [pageZero] at alias
      omega
  have overflowBounds : ∀ (offset : Nat)
      (_inBounds : offset < oldPhysical.encoding.overflowPages.length),
      0 < oldPhysical.nextOverflow + offset ∧
        oldPhysical.nextOverflow + offset ≤ oldImage.pageCount := by
    intro offset inBounds
    rw [oldInline] at inBounds
    simp at inBounds
  have overflowUntouched : ∀ (offset : Nat)
      (_inBounds : offset < oldPhysical.encoding.overflowPages.length),
      ∀ write ∈ final.writes,
        write.pageId + 1 ≠ oldPhysical.nextOverflow + offset := by
    intro offset inBounds
    rw [oldInline] at inBounds
    simp at inBounds
  have transported := oldPhysical.applyWritesOfUntouched oldImage final.writes
    final.distinct old (oldPhysical.treeBounds oldImage) treeUntouched
      overflowBounds overflowUntouched
  exact transported.retarget table equivalent

/-- Complete the table/index part of a one-table indexed commit over the
planner's exact final write list.  The no-freelist premise is the ordinary
point-update/YCSB case: every non-delta write is then page zero, whose page
number is strictly below every table and index root. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.databaseOnFinalWritesIndexedSingle
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (indexed : delta.table.before.table.indexes ≠ [])
    (single : state.tables = [delta.table.before])
    (final : CoreFileAdapter.PreparedLocalizedWrites delta.after.freePages
      prepared.writes)
    (noFree : delta.after.freePages = [])
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage oldImage).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites oldImage final.writes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog))
    (beforeInline :
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem
          prepared.updated).1)).encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem prepared.updated).1)).nextOverflow =
        some afterEncoding)
    (afterInline : afterEncoding.overflowPages = []) :
    CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage final.writes)) delta.after := by
  let changed :=
    SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.changedTableOnFinalWritesIndexed
      prepared indexed final oldImage physical beforeInline afterEncoding
        afterEncoded afterInline
  have retained : ∀ (old : CoreChunkPageState.TableState),
      old ∈ state.tables → ∀ (table : Core.Table)
        (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      CoreLocalizedRepresentation.TableOnSource
          (CorePageSource.ofStorageImage oldImage) old →
        CoreLocalizedRepresentation.TableOnSource
          (CorePageSource.ofStorageImage
            (GrowableStorage.applyWrites oldImage final.writes))
          (old.retarget table equivalent) := by
    intro old member table equivalent different oldPhysical
    rw [single] at member
    simp only [List.mem_singleton] at member
    exact False.elim (different member)
  have addedBelow : ∀ entries,
      CoreLocalizedRepresentation.TablePagesBeforeIndexRoots
        state.tables entries →
      ∀ write ∈ final.writes, write ∉ prepared.writes →
        ∀ entry ∈ entries, write.pageId + 1 < entry.rootPage := by
    intro entries separation write writeMember notBase entry entryMember
    have pageZero := final.added_pageZero_of_noFreePages noFree writeMember
      notBase
    have selected := CoreChunkPageDelta.updateState?_selected_mem
      prepared.updated
    have rootActive : delta.table.before.tree.root.rootId ∈
        state.activePageIds := by
      unfold CoreChunkPageState.State.activePageIds
        CoreChunkPageState.tablePageIds
      exact List.mem_flatMap.mpr ⟨delta.table.before, selected.1,
        PersistentPageTree.Node.rootId_mem_pageIds
          delta.table.before.tree.root⟩
    have rootBelow := separation delta.table.before.tree.root.rootId
      rootActive entry entryMember
    have rootAfterCatalog := prepared.allocation.active_after_catalog
      delta.table.before.tree.root.rootId rootActive
    rw [pageZero]
    omega
  have changedInline : changed.encoding.overflowPages = [] := by
    simpa [changed,
      SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.changedTableOnFinalWritesIndexed,
      SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.changedTableOnFinalWrites,
      CoreLocalizedRepresentation.TableOnSource.updateStateInlineExtension]
      using afterInline
  exact physical.updateStateApplyWritesBelowExtension oldImage prepared.writes
    final.writes final.distinct prepared.allocation prepared.updated
    catalogPreserved retained changed indexed prepared.writesEq addedBelow
    changedInline

end CoreDurability

end SQLeanite
