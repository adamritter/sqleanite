import SQLeanite.CoreDurability.CoreFileAdapterPreparedOrdinaryDeltaDatabaseOnFinalWritesIndexedInline
import SQLeanite.CoreFreelistCodec
import SQLeanite.CoreWidePageInverse.PageSourceRepresentsEncodeBulkInlineWithState

namespace SQLeanite
namespace CoreDurability

/-- Public post-image certificate for an indexed localized mutation in a
multi-table inline database.  Unlike the former `...Single` constructor, this
one proves the frame condition for every unchanged table. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedInline
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (indexed : delta.table.before.table.indexes ≠ [])
    (noFree : delta.after.freePages = [])
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (onImage : committed.prepared.OnImage oldImage)
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
    PostImageCertificate oldImage committed.prepared.writes
      delta.after.database :=
  .components
    (CoreFileAdapter.PreparedOrdinaryDelta.localizedOnFinalWritesIndexedInline
      prepared indexed committed.prepared noFree oldImage physical onImage
        oldHeader emptyFreelist allRowsInline beforeInline afterEncoding
          afterEncoded afterInline)

/-- Semantic-row form of the multi-table post-image certificate.  Inline
overflow facts for the selected table are derived from the same per-table
bound that transports all unchanged tables. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedInlineOfRows
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (indexed : delta.table.before.table.indexes ≠ [])
    (noFree : delta.after.freePages = [])
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (onImage : committed.prepared.OnImage oldImage)
    (oldHeader : SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
    (allRowsInline : ∀ old ∈ state.tables,
      CorePageCodec.NodeRowsInline old.table.schema old.tree.root)
    (afterRowsInline : CorePageCodec.NodeRowsInline
      delta.table.after.table.schema delta.table.after.tree.root)
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem prepared.updated).1)).nextOverflow =
        some afterEncoding) :
    PostImageCertificate oldImage committed.prepared.writes
      delta.after.database := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  have beforeInline : before.encoding.overflowPages = [] :=
    CorePageCodec.encodeChunkNodeWithOverflow_inline
      delta.table.before.table.schema delta.table.before.tree.root
        before.nextOverflow before.encoding
          (allRowsInline delta.table.before selected.1) before.encoded
  have afterEncoded' : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding := by
    simpa [before, selected] using afterEncoded
  have afterInline : afterEncoding.overflowPages = [] :=
    CorePageCodec.encodeChunkNodeWithOverflow_inline
      delta.table.after.table.schema delta.table.after.tree.root
        before.nextOverflow afterEncoding afterRowsInline afterEncoded'
  exact
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedInline
      prepared indexed noFree committed oldImage physical onImage oldHeader
        emptyFreelist allRowsInline
          (by simpa [before, selected] using beforeInline) afterEncoding
            afterEncoded afterInline

/-- Semantic-row variant of the live one-table certificate.  The two overflow
equations are derived from the pre/post tree invariants, so callers cannot
claim the localized path merely because a separately supplied encoder result
happened to contain no overflow pages. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingleOfRowsInline
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
    (beforeRowsInline : CorePageCodec.NodeRowsInline
      delta.table.before.table.schema delta.table.before.tree.root)
    (afterRowsInline : CorePageCodec.NodeRowsInline
      delta.table.after.table.schema delta.table.after.tree.root)
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem prepared.updated).1)).nextOverflow =
        some afterEncoding) :
    PostImageCertificate oldImage committed.prepared.writes
      delta.after.database := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  have beforeInline : before.encoding.overflowPages = [] :=
    CorePageCodec.encodeChunkNodeWithOverflow_inline
      delta.table.before.table.schema delta.table.before.tree.root
        before.nextOverflow before.encoding beforeRowsInline before.encoded
  have afterEncoded' : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding := by
    simpa [before, selected] using afterEncoded
  have afterInline : afterEncoding.overflowPages = [] :=
    CorePageCodec.encodeChunkNodeWithOverflow_inline
      delta.table.after.table.schema delta.table.after.tree.root
        before.nextOverflow afterEncoding afterRowsInline afterEncoded'
  exact
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingle
      prepared indexed single noFree committed oldImage physical onImage
        oldHeader emptyFreelist (by simpa [before, selected] using beforeInline)
          afterEncoding afterEncoded afterInline

/-- Live-tree form of the semantic certificate.  The localized encoder's
ordinary `encodeChunkNode` equation determines the overflow-aware result, so
there is no caller-selected `OverflowEncoding` left in this interface. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingleOfInlineTree
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
    (beforeRowsInline : CorePageCodec.NodeRowsInline
      delta.table.before.table.schema delta.table.before.tree.root)
    (afterRowsInline : CorePageCodec.NodeRowsInline
      delta.table.after.table.schema delta.table.after.tree.root)
    (afterPages : List CorePageCodec.NumberedPage)
    (afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterPages) :
    PostImageCertificate oldImage committed.prepared.writes
      delta.after.database := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  let afterEncoding : CorePageCodec.OverflowEncoding := {
    treePages := afterPages
    overflowPages := []
    nextPage := before.nextOverflow }
  have afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding := by
    exact CorePageCodec.encodeChunkNodeWithOverflow_of_inline
      delta.table.after.table.schema delta.table.after.tree.root
        before.nextOverflow afterPages afterRowsInline afterTree
  exact
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingleOfRowsInline
      prepared indexed single noFree committed oldImage physical onImage
        oldHeader emptyFreelist beforeRowsInline afterRowsInline afterEncoding
          (by simpa [before, selected] using afterEncoded)

/-- Fully structural one-table certificate.  Successful `updateState?`
preserves full-tree encodability from its changed path/descriptors, so neither
the general encoder nor the full localized tree encoder appears as a premise. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingleOfInlineRows
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
    (beforeRowsInline : CorePageCodec.NodeRowsInline
      delta.table.before.table.schema delta.table.before.tree.root)
    (afterRowsInline : CorePageCodec.NodeRowsInline
      delta.table.after.table.schema delta.table.after.tree.root) :
    PostImageCertificate oldImage committed.prepared.writes
      delta.after.database := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  have beforeInline : before.encoding.overflowPages = [] :=
    CorePageCodec.encodeChunkNodeWithOverflow_inline
      delta.table.before.table.schema delta.table.before.tree.root
        before.nextOverflow before.encoding beforeRowsInline before.encoded
  have schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema :=
    (CoreChunkPageDelta.TableDelta.tablePagesSufficient_metadata delta.table
      (CoreChunkPageDelta.updateState?_tablePagesSufficient
        prepared.updated)).1
  have beforeTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some before.encoding.treePages := by
    rw [← schemaSame]
    exact before.inlineEncoded beforeInline
  rcases CoreChunkPageDelta.updateState?_encodabilityPreserved prepared.updated
      before.encoding.treePages beforeTree with ⟨afterPages, afterTree⟩
  exact
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingleOfInlineTree
      prepared indexed single noFree committed oldImage physical onImage
        oldHeader emptyFreelist beforeRowsInline afterRowsInline afterPages
          afterTree

/-- Fully structural multi-table certificate.  The represented selected tree
and successful live delta imply post-tree encodability; allocator separation
frames every other inline table.  No post-state encoder value or byte equation
is exposed as a premise. -/
noncomputable def
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedInlineOfInlineRows
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (indexed : delta.table.before.table.indexes ≠ [])
    (noFree : delta.after.freePages = [])
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (onImage : committed.prepared.OnImage oldImage)
    (oldHeader : SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
    (allRowsInline : ∀ old ∈ state.tables,
      CorePageCodec.NodeRowsInline old.table.schema old.tree.root)
    (afterRowsInline : CorePageCodec.NodeRowsInline
      delta.table.after.table.schema delta.table.after.tree.root) :
    PostImageCertificate oldImage committed.prepared.writes
      delta.after.database := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  have beforeInline : before.encoding.overflowPages = [] :=
    CorePageCodec.encodeChunkNodeWithOverflow_inline
      delta.table.before.table.schema delta.table.before.tree.root
        before.nextOverflow before.encoding
          (allRowsInline delta.table.before selected.1) before.encoded
  have schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema :=
    (CoreChunkPageDelta.TableDelta.tablePagesSufficient_metadata delta.table
      (CoreChunkPageDelta.updateState?_tablePagesSufficient
        prepared.updated)).1
  have beforeTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some before.encoding.treePages := by
    rw [← schemaSame]
    exact before.inlineEncoded beforeInline
  rcases CoreChunkPageDelta.updateState?_encodabilityPreserved prepared.updated
      before.encoding.treePages beforeTree with ⟨afterPages, afterTree⟩
  let afterEncoding : CorePageCodec.OverflowEncoding := {
    treePages := afterPages
    overflowPages := []
    nextPage := before.nextOverflow }
  have afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding := by
    exact CorePageCodec.encodeChunkNodeWithOverflow_of_inline
      delta.table.after.table.schema delta.table.after.tree.root
        before.nextOverflow afterPages afterRowsInline afterTree
  exact
    CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedInlineOfRows
      prepared indexed noFree committed oldImage physical onImage oldHeader
        emptyFreelist allRowsInline afterRowsInline afterEncoding
          (by simpa [before, selected] using afterEncoded)

/-- The exact pure object consumed by the live bulk writer selects a
constructive post-image constructor.  No decoder result or byte comparison is
accepted here: canonical and padded branches both retain the encoder equation
chosen before the syscall trace begins. -/
def postImageCertificate_of_preparedBulkImage
    (utf8 : CoreDecode.UTF8Roundtrips)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (database : Core.Database) (canonicalImage newImage : CoreFile.Image)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (encoded : CorePageCodec.encodeBulk database = some canonicalImage)
    (choice : CoreFileAdapter.PreparedBulkImage canonicalImage newImage)
    (doesNotShrink : oldImage.pageCount ≤
      (CoreFileAdapter.storageImage newImage).pageCount)
    (writesEq : writes = CoreFileAdapter.transactionWrites oldImage newImage) :
    PostImageCertificate oldImage writes database := by
  have applied : (GrowableStorage.applyWrites oldImage writes).Equiv
      (CoreFileAdapter.storageImage newImage) := by
    rw [writesEq]
    exact GrowableStorage.apply_deltaWrites_equiv oldImage
      (CoreFileAdapter.storageImage newImage) doesNotShrink
  cases choice with
  | canonical => exact .bulk utf8 canonicalImage encoded applied
  | padded layout sameImage =>
      have layoutEncoded : CorePageCodec.encodeBulk database =
          some layout.image := by
        rw [sameImage]
        exact encoded
      exact .padded utf8 layout layoutEncoded applied

/-- Every successful live bulk preparation already carries the public
post-image certificate; turning it into the crash theorem's premise is proof
only and performs no additional encoding, decoding, or file read. -/
def CoreFileAdapter.PreparedBulkCommit.postImageCertificate
    {oldImage : GrowableStorage.Image PhysicalCodec.pageSize}
    {database : Core.Database}
    (prepared : CoreFileAdapter.PreparedBulkCommit oldImage database)
    (utf8 : CoreDecode.UTF8Roundtrips) :
    PostImageCertificate oldImage prepared.writes database :=
  postImageCertificate_of_preparedBulkImage utf8 oldImage database
    prepared.canonicalImage prepared.newImage prepared.writes
    (CorePageCodec.encodeBulkWithState_image prepared.encodedWithState)
    prepared.choice prepared.doesNotShrink prepared.writesEq

def CoreFileAdapter.PreparedWideBulkCommit.postImageCertificate
    {oldImage : GrowableStorage.Image PhysicalCodec.pageSize}
    {database : Core.Database}
    (prepared : CoreFileAdapter.PreparedWideBulkCommit oldImage database)
    (utf8 : CoreDecode.UTF8Roundtrips) :
    PostImageCertificate oldImage prepared.writes database := by
  apply PostImageCertificate.wideBulk utf8 prepared.image
    (CoreWidePageCodec.encodeBulkInlineWithState_image
      prepared.encodedWithState)
  rw [prepared.writesEq]
  exact GrowableStorage.apply_deltaWrites_equiv oldImage
    (CoreFileAdapter.storageImage prepared.image) prepared.doesNotShrink

theorem PostImageCertificate.representsDatabase
    {oldImage : GrowableStorage.Image PhysicalCodec.pageSize}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    {database : Core.Database}
    (certificate : PostImageCertificate oldImage writes database) :
    RepresentsDatabase (GrowableStorage.applyWrites oldImage writes)
      database := by
  cases certificate with
  | ordinary commit =>
      rcases commit.localizedRepresentation with ⟨header, components⟩
      apply pageSourceRepresents_storageImage header
      rcases components with
        ⟨catalog, catalogRead, tablesRead, indexesRead⟩
      exact .intro catalog catalogRead tablesRead indexesRead
  | components certificate =>
      rcases certificate with ⟨header, components⟩
      apply pageSourceRepresents_storageImage header
      rcases components with
        ⟨catalog, catalogRead, tablesRead, indexesRead⟩
      exact .intro catalog catalogRead tablesRead indexesRead
  | bulk utf8 image encoded applied =>
      unfold RepresentsDatabase
      rw [PhysicalJournalRecovery.imageBytes_eq_of_equiv applied]
      exact decode_imageBytes_encodeBulk utf8 database image encoded
  | padded utf8 layout encoded applied =>
      unfold RepresentsDatabase
      rw [PhysicalJournalRecovery.imageBytes_eq_of_equiv applied,
        imageBytes_storageImage]
      exact CoreFreelistCodec.decode_paddedImage utf8 database layout encoded
  | wideBulk utf8 image encoded applied =>
      unfold RepresentsDatabase
      rw [PhysicalJournalRecovery.imageBytes_eq_of_equiv applied,
        imageBytes_storageImage]
      exact CoreWidePageInverse.decode_encodeBulkInline utf8 database image encoded

/-- Build the complete component certificate from one exact schema-page write
and the separately compositional table/index decoder facts. -/
def localizedRepresentation_of_pageZeroWrite
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (database : Core.Database)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pageZero : GrowableStorage.PageWrite PhysicalCodec.pageSize)
    (member : pageZero ∈ writes) (zero : pageZero.pageId = 0)
    (header : FileFormat.DatabaseHeader) (pageSuffix : List UInt8)
    (headerBytes : pageZero.page.bytes.toList =
      FileFormat.encodeDatabaseHeader header ++ pageSuffix)
    (pageCount : header.databaseSizePages.val =
      (GrowableStorage.applyWrites oldImage writes).pageCount)
    (pageSize : header.headerPrefix.pageSizeField.val =
      PhysicalCodec.pageSize)
    (reserved : header.headerPrefix.reservedSpace = 0)
    (utf8 : header.textEncoding.val = 1)
    (catalog : List CoreDecode.CatalogEntry)
    (catalogDecoded :
      CoreDecode.decodeCatalogForOpen pageZero.page.bytes.toList = some catalog)
    (tablesRead :
      (catalog.filter (fun entry => entry.kind == "table")).mapM
          (CoreDecode.decodeTableFrom (localizedSource oldImage writes)) =
        some (database.tables.map Core.Table.withoutIndexes))
    (indexesRead :
      CoreDecode.applyIndexesForOpen (localizedSource oldImage writes)
          database.withoutIndexes
          (catalog.filter (fun entry => entry.kind == "index")) =
        some database.canonicalize) :
    LocalizedRepresentation oldImage writes database := by
  exact {
    header := sqliteHeaderMatches_of_pageZeroWrite oldImage writes distinct
      pageZero member zero header pageSuffix headerBytes pageCount pageSize
      reserved utf8
    components := ⟨catalog,
      catalogRead_of_pageZeroWrite oldImage writes distinct
        pageZero member zero catalog catalogDecoded,
      tablesRead, indexesRead⟩ }

end CoreDurability

end SQLeanite
