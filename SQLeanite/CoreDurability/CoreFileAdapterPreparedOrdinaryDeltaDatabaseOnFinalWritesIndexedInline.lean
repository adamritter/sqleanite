import SQLeanite.CoreDurability.CoreFileAdapterPreparedOrdinaryDeltaChangedTableOnFinalWritesIndexed
import SQLeanite.CoreFileAdapter.LookupGeneratedIndexCandidates

namespace SQLeanite
namespace CoreDurability

/-- Multi-table counterpart of `databaseOnFinalWritesIndexedSingle` for the
semantic inline-row bound used by the localized writer.  The selected table is
rebuilt from its exact changed pages; every other table is transported by
`retainedTableOnFinalWritesIndexed`, whose cross-table separation follows from
the allocator invariant rather than from a one-table shortcut. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.databaseOnFinalWritesIndexedInline
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
    (catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage oldImage).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites oldImage final.writes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog))
    (allRowsInline : ∀ old ∈ state.tables,
      CorePageCodec.NodeRowsInline old.table.schema old.tree.root)
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
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  let changed :=
    SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.changedTableOnFinalWritesIndexed
      prepared indexed final oldImage physical beforeInline afterEncoding
        afterEncoded afterInline
  have afterEncoded' : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding := by
    simpa [before, selected] using afterEncoded
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
    have oldInline : oldPhysical.encoding.overflowPages = [] :=
      CorePageCodec.encodeChunkNodeWithOverflow_inline old.table.schema
        old.tree.root oldPhysical.nextOverflow oldPhysical.encoding
          (allRowsInline old member) oldPhysical.encoded
    exact
      SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.retainedTableOnFinalWritesIndexed
        prepared indexed final noFree oldImage before.nextOverflow afterEncoding
          afterEncoded' afterInline old member table equivalent different
            oldPhysical oldInline
  have addedBelow : ∀ entries,
      CoreLocalizedRepresentation.TablePagesBeforeIndexRoots
        state.tables entries →
      ∀ write ∈ final.writes, write ∉ prepared.writes →
        ∀ entry ∈ entries, write.pageId + 1 < entry.rootPage := by
    intro entries separation write writeMember notBase entry entryMember
    have pageZero := final.added_pageZero_of_noFreePages noFree writeMember
      notBase
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

/-- Package the exact one-table indexed final-write proof as the public
localized post-image certificate.  Page-zero omission is derived from the
planner equation and the validated empty-freelist header, rather than supplied
as an independent premise. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.localizedOnFinalWritesIndexedSingle
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
    (onImage : final.OnImage oldImage)
    (oldHeader : SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
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
    LocalizedRepresentation oldImage final.writes delta.after.database := by
  have selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  have positive := physical.pageCount_pos_of_table oldImage
    delta.table.before selected.1
  have bounded :=
    SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.finalWrites_pageId_lt_of_indexed
      prepared indexed final noFree oldImage physical beforeInline
        afterEncoding afterEncoded afterInline
  have baseBound : ∀ write ∈ prepared.writes,
      write.pageId < final.currentPageCount := by
    intro write member
    rw [onImage.pageCount]
    exact bounded write (final.base_mem write member)
  have basePositive :=
    SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.baseWrites_pageId_pos_of_indexed
      prepared indexed oldImage physical afterEncoding afterEncoded afterInline
  have baseNoZero : ∀ write ∈ prepared.writes, 0 ≠ write.pageId := by
    intro write member equal
    have positiveWrite := basePositive write member
    omega
  rcases oldHeader.firstPage_of_freelistEmpty emptyFreelist positive with
    ⟨decodedHeader, pageSuffix, pageBytes, headerCount, _, _, _, firstFree,
      freeCount⟩
  have decodedFirst : FileFormat.decodeDatabaseHeader final.firstPage =
      some (decodedHeader, pageSuffix) := by
    rw [onImage.pageZero, pageBytes]
    exact FileFormat.decodeDatabaseHeader_encode decodedHeader pageSuffix
  have canonicalFirst : final.firstPage =
      FileFormat.encodeDatabaseHeader decodedHeader ++ pageSuffix := by
    rw [onImage.pageZero]
    exact pageBytes
  have countMatches : decodedHeader.databaseSizePages.val =
      final.currentPageCount := headerCount.trans onImage.pageCount.symm
  have notWritten := final.pageZero_not_mem_of_stable noFree baseBound
    baseNoZero decodedHeader pageSuffix decodedFirst canonicalFirst countMatches
      firstFree freeCount
  have stableCount := GrowableStorage.applyWrites_pageCount_eq_of_forall_lt
    oldImage final.writes bounded
  have header := oldHeader.applyWritesOfUnchangedPageZero final.writes positive
    notWritten stableCount
  have catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage oldImage).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites oldImage final.writes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog) := by
    intro catalog decoded
    exact catalogRead_of_unchangedPageZero oldImage final.writes positive
      notWritten catalog decoded
  have post :=
    SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.databaseOnFinalWritesIndexedSingle
      prepared indexed single final noFree oldImage physical catalogPreserved
        beforeInline afterEncoding afterEncoded afterInline
  exact localizedRepresentation_of_databaseOnSource oldImage final.writes
    delta.after header post

/-- Header/catalog-framed multi-table localized representation.  Compared
with the one-table theorem above, the only extra premise is the semantic
inline-row bound for each pre-state table; cross-table byte separation is now
derived internally by `databaseOnFinalWritesIndexedInline`. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.localizedOnFinalWritesIndexedInline
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
    (onImage : final.OnImage oldImage)
    (oldHeader : SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
    (allRowsInline : ∀ old ∈ state.tables,
      CorePageCodec.NodeRowsInline old.table.schema old.tree.root)
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
    LocalizedRepresentation oldImage final.writes delta.after.database := by
  have selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  have positive := physical.pageCount_pos_of_table oldImage
    delta.table.before selected.1
  have bounded :=
    SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.finalWrites_pageId_lt_of_indexed
      prepared indexed final noFree oldImage physical beforeInline
        afterEncoding afterEncoded afterInline
  have baseBound : ∀ write ∈ prepared.writes,
      write.pageId < final.currentPageCount := by
    intro write member
    rw [onImage.pageCount]
    exact bounded write (final.base_mem write member)
  have basePositive :=
    SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.baseWrites_pageId_pos_of_indexed
      prepared indexed oldImage physical afterEncoding afterEncoded afterInline
  have baseNoZero : ∀ write ∈ prepared.writes, 0 ≠ write.pageId := by
    intro write member equal
    have positiveWrite := basePositive write member
    omega
  rcases oldHeader.firstPage_of_freelistEmpty emptyFreelist positive with
    ⟨decodedHeader, pageSuffix, pageBytes, headerCount, _, _, _, firstFree,
      freeCount⟩
  have decodedFirst : FileFormat.decodeDatabaseHeader final.firstPage =
      some (decodedHeader, pageSuffix) := by
    rw [onImage.pageZero, pageBytes]
    exact FileFormat.decodeDatabaseHeader_encode decodedHeader pageSuffix
  have canonicalFirst : final.firstPage =
      FileFormat.encodeDatabaseHeader decodedHeader ++ pageSuffix := by
    rw [onImage.pageZero]
    exact pageBytes
  have countMatches : decodedHeader.databaseSizePages.val =
      final.currentPageCount := headerCount.trans onImage.pageCount.symm
  have notWritten := final.pageZero_not_mem_of_stable noFree baseBound
    baseNoZero decodedHeader pageSuffix decodedFirst canonicalFirst countMatches
      firstFree freeCount
  have stableCount := GrowableStorage.applyWrites_pageCount_eq_of_forall_lt
    oldImage final.writes bounded
  have header := oldHeader.applyWritesOfUnchangedPageZero final.writes positive
    notWritten stableCount
  have catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage oldImage).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites oldImage final.writes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog) := by
    intro catalog decoded
    exact catalogRead_of_unchangedPageZero oldImage final.writes positive
      notWritten catalog decoded
  have post :=
    SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.databaseOnFinalWritesIndexedInline
      prepared indexed final noFree oldImage physical catalogPreserved
        allRowsInline beforeInline afterEncoding afterEncoded afterInline
  exact localizedRepresentation_of_databaseOnSource oldImage final.writes
    delta.after header post

/-- The dependent object selected by the live ordinary-delta branch supplies
all executable equations of `OrdinaryLocalizedCommit`.  The remaining
arguments are precisely the erased physical component witnesses: the old
validated layout, header/catalog frame, retained tables, and changed table.
Keeping this constructor here (above the adapter import cycle) prevents a
caller from proving durability for a write list different from the one the
live engine passes to `commitLocalized`. -/
def CoreFileAdapter.PreparedOrdinaryDelta.ordinaryLocalizedCommit
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (header : SQLiteHeaderMatches
      (GrowableStorage.applyWrites oldImage prepared.writes))
    (catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage oldImage).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites oldImage prepared.writes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog))
    (retained : ∀ (old : CoreChunkPageState.TableState)
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      CoreLocalizedRepresentation.TableOnSource
          (CorePageSource.ofStorageImage oldImage) old →
        ∃ _physical : CoreLocalizedRepresentation.TableOnSource
            (CorePageSource.ofStorageImage
              (GrowableStorage.applyWrites oldImage prepared.writes))
            (old.retarget table equivalent), True)
    (changed : ∃ physical : CoreLocalizedRepresentation.TableOnSource
        (CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites oldImage prepared.writes))
        delta.table.after, physical.encoding.overflowPages = []) :
    OrdinaryLocalizedCommit oldImage prepared.writes state database delta := {
  physical
  allocation := prepared.allocation
  updated := prepared.updated
  converted := prepared.writesEq
  distinct := prepared.distinct
  header
  catalogPreserved
  retained
  changed
  preservationMode := prepared.preservationMode }

/-- A one-table localized commit has no retained-table premise to supply.
This is the exact shape of the paper's YCSB database: the one logical table
may change, while the membership-aware frame theorem proves there cannot be a
second old table hidden behind the universal callback.  The result is still
schema-generic; in particular, it does not replace the literal TEXT primary
key with an integer surrogate. -/
def CoreFileAdapter.PreparedOrdinaryDelta.ordinaryLocalizedCommitSingle
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (single : state.tables = [delta.table.before])
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (header : SQLiteHeaderMatches
      (GrowableStorage.applyWrites oldImage prepared.writes))
    (catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage oldImage).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites oldImage prepared.writes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog))
    (changed : ∃ changedPhysical :
        CoreLocalizedRepresentation.TableOnSource
          (CorePageSource.ofStorageImage
            (GrowableStorage.applyWrites oldImage prepared.writes))
          delta.table.after,
        changedPhysical.encoding.overflowPages = []) :
    OrdinaryLocalizedCommit oldImage prepared.writes state database delta := by
  apply SQLeanite.CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.ordinaryLocalizedCommit
    prepared oldImage physical header catalogPreserved
  · intro old member table equivalent different oldPhysical
    rw [single] at member
    simp only [List.mem_singleton] at member
    exact False.elim (different member)
  · exact changed

/-- Constructive alternatives for the post-image premise of the public crash
theorem.  Every constructor exposes how the bytes were justified: an ordinary
localized delta, a canonical bulk image, or a verified freelist-padded image.
There is deliberately no constructor accepting an opaque decoder equation. -/
inductive PostImageCertificate
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (database : Core.Database) : Prop where
  | ordinary {state : CoreChunkPageState.State}
      {delta : CoreChunkPageDelta.StateDelta}
      (commit : OrdinaryLocalizedCommit oldImage writes state database delta) :
      PostImageCertificate oldImage writes database
  | components (certificate : LocalizedRepresentation oldImage writes
      database) : PostImageCertificate oldImage writes database
  | bulk (utf8 : CoreDecode.UTF8Roundtrips) (image : CoreFile.Image)
      (encoded : CorePageCodec.encodeBulk database = some image)
      (applied : (GrowableStorage.applyWrites oldImage writes).Equiv
        (CoreFileAdapter.storageImage image)) :
      PostImageCertificate oldImage writes database
  | padded (utf8 : CoreDecode.UTF8Roundtrips)
      (layout : CoreMultiFreelist.Layout)
      (encoded : CorePageCodec.encodeBulk database = some layout.image)
      (applied : (GrowableStorage.applyWrites oldImage writes).Equiv
        (CoreFileAdapter.storageImage layout.paddedImage)) :
      PostImageCertificate oldImage writes database
  | wideBulk (utf8 : CoreDecode.UTF8Roundtrips) (image : CoreFile.Image)
      (encoded : CoreWidePageCodec.encodeBulkInline database = some image)
      (applied : (GrowableStorage.applyWrites oldImage writes).Equiv
        (CoreFileAdapter.storageImage image)) :
      PostImageCertificate oldImage writes database

/-- The value returned by the live localized writer carries the exact final
write list consumed by both the syscall trace and the component proof.  This
constructor closes the one-table indexed point-update/YCSB post-image chain
without permitting a separately reconstructed list of pages. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingle
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (indexed : delta.table.before.table.indexes ≠ [])
    (single : state.tables = [delta.table.before])
    (noFree : delta.after.freePages = [])
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (onImage : committed.prepared.OnImage oldImage)
    (oldHeader : SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
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
    PostImageCertificate oldImage committed.prepared.writes
      delta.after.database :=
  .components
    (CoreFileAdapter.PreparedOrdinaryDelta.localizedOnFinalWritesIndexedSingle
      prepared indexed single committed.prepared noFree oldImage physical
      onImage oldHeader emptyFreelist beforeInline afterEncoding afterEncoded
      afterInline)

end CoreDurability

end SQLeanite
