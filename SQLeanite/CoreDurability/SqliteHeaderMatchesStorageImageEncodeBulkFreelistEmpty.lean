import SQLeanite.CoreDurability.ImagePagesStorageImage
import SQLeanite.CoreLocalizedRepresentation.PageSourceContainsUpdateStateTreeExtension

namespace SQLeanite
namespace CoreDurability

/-- Canonical bulk images begin with no freelist.  The proposition decodes
the same emitted header independently, so it remains meaningful even when
paired with a different proof term for `SQLiteHeaderMatches`. -/
theorem sqliteHeaderMatches_storageImage_encodeBulk_freelistEmpty
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image)
    (validHeader : SQLiteHeaderMatches
      (CoreFileAdapter.storageImage image)) :
    validHeader.FreelistEmpty := by
  rcases CorePageCodec.encodeBulk_header encoded with
    ⟨count, schema, remaining, body, pagesEqual, countEqual, headerEqual⟩
  let header := CoreFile.databaseHeader count
  let suffix := body ++ remaining.flatMap CoreFile.Page.bytes
  refine ⟨header, suffix, ?_, by rfl, by rfl⟩
  rw [imageBytes_storageImage]
  unfold CoreFile.Image.fileBytes
  rw [pagesEqual]
  simp only [List.flatMap_cons]
  rw [headerEqual]
  simpa [header, suffix, List.append_assoc] using
    FileFormat.decodeDatabaseHeader_encode header suffix

/-- One canonical bulk encode supplies the complete proof-carrying starting
state for localized transactions: logical allocator state, table/index page
ownership, SQLite header framing, and an empty freelist all refer to the same
concrete storage image. -/
theorem exists_framedDatabaseOnStorage_encodeBulk
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image) :
    ∃ state : CoreChunkPageState.State,
      CoreChunkPageState.State.build? database = some state ∧
      CoreLocalizedRepresentation.DatabaseOnSource
        (CorePageSource.ofStorageImage
          (CoreFileAdapter.storageImage image)) state ∧
      ∃ header : SQLiteHeaderMatches (CoreFileAdapter.storageImage image),
        header.FreelistEmpty := by
  rcases exists_databaseOnStorage_encodeBulk utf8 database image encoded with
    ⟨state, built, physical⟩
  let header := sqliteHeaderMatches_storageImage_encodeBulk database image
    encoded
  exact ⟨state, built, physical, header,
    sqliteHeaderMatches_storageImage_encodeBulk_freelistEmpty database image
      encoded header⟩

/-- Exact first-page decomposition including the empty-freelist fields. -/
theorem SQLiteHeaderMatches.firstPage_of_freelistEmpty
    {image : GrowableStorage.Image PhysicalCodec.pageSize}
    (validHeader : SQLiteHeaderMatches image)
    (empty : validHeader.FreelistEmpty) (positive : 0 < image.pageCount) :
    ∃ (header : FileFormat.DatabaseHeader) (pageSuffix : List UInt8),
      (image.read 0).bytes.toList =
        FileFormat.encodeDatabaseHeader header ++ pageSuffix ∧
      header.databaseSizePages.val = image.pageCount ∧
      header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize ∧
      header.headerPrefix.reservedSpace = 0 ∧
      header.textEncoding.val = 1 ∧
      header.firstFreelistTrunk.val = 0 ∧
      header.freelistPageCount.val = 0 := by
  rcases validHeader with
    ⟨header, suffix, decoded, pageCount, pageSize, reserved, utf8⟩
  rcases empty with
    ⟨emptyHeader, emptySuffix, emptyDecoded, emptyFirst, emptyCount⟩
  rw [decoded] at emptyDecoded
  have pairEq := Option.some.inj emptyDecoded
  injection pairEq with headerEq suffixEq
  subst emptyHeader
  subst emptySuffix
  rcases firstPage_of_decodedHeader image header suffix decoded positive with
    ⟨pageSuffix, bytes⟩
  exact ⟨header, pageSuffix, bytes, pageCount, pageSize, reserved, utf8,
    emptyFirst, emptyCount⟩

/-- An exact page-zero write establishes the SQLite framing part of a
localized representation certificate.  This theorem is the pure refinement
target for the live header/freelist planner. -/
theorem sqliteHeaderMatches_of_pageZeroWrite
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pageZero : GrowableStorage.PageWrite PhysicalCodec.pageSize)
    (member : pageZero ∈ writes) (zero : pageZero.pageId = 0)
    (header : FileFormat.DatabaseHeader) (pageSuffix : List UInt8)
    (bytes : pageZero.page.bytes.toList =
      FileFormat.encodeDatabaseHeader header ++ pageSuffix)
    (pageCount : header.databaseSizePages.val =
      (GrowableStorage.applyWrites oldImage writes).pageCount)
    (pageSize : header.headerPrefix.pageSizeField.val =
      PhysicalCodec.pageSize)
    (reserved : header.headerPrefix.reservedSpace = 0)
    (utf8 : header.textEncoding.val = 1) :
    SQLiteHeaderMatches (GrowableStorage.applyWrites oldImage writes) := by
  let image := GrowableStorage.applyWrites oldImage writes
  have bound := CorePageSource.pageId_lt_applyWrites_of_mem oldImage member
  have positive : 0 < image.pageCount := by simpa [image, zero] using bound
  rcases imageBytes_eq_firstPage_append image positive with
    ⟨suffix, imageBytes⟩
  have read : image.read 0 = pageZero.page := by
    have exactRead := CorePageSource.applyWrites_read_of_mem oldImage distinct
      member
    simpa [image, zero] using exactRead
  refine .intro header (pageSuffix ++ suffix) ?_ pageCount pageSize reserved utf8
  rw [imageBytes, read, bytes, List.append_assoc]
  exact FileFormat.decodeDatabaseHeader_encode header (pageSuffix ++ suffix)

/-- Localized row/index writes do not normally touch page zero.  In that
case the already-certified header bytes remain the header of the post-image.
The explicit page-count equality is the useful boundary: a growing write must
instead use `sqliteHeaderMatches_of_pageZeroWrite`, because SQLite records the
new size in page zero. -/
theorem sqliteHeaderMatches_of_unchangedPageZero
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (notWritten : ∀ write ∈ writes, 0 ≠ write.pageId)
    (positive : 0 < oldImage.pageCount)
    (header : FileFormat.DatabaseHeader) (pageSuffix : List UInt8)
    (bytes : (oldImage.read 0).bytes.toList =
      FileFormat.encodeDatabaseHeader header ++ pageSuffix)
    (pageCount : header.databaseSizePages.val =
      (GrowableStorage.applyWrites oldImage writes).pageCount)
    (pageSize : header.headerPrefix.pageSizeField.val =
      PhysicalCodec.pageSize)
    (reserved : header.headerPrefix.reservedSpace = 0)
    (utf8 : header.textEncoding.val = 1) :
    SQLiteHeaderMatches (GrowableStorage.applyWrites oldImage writes) := by
  let image := GrowableStorage.applyWrites oldImage writes
  have imagePositive : 0 < image.pageCount := by
    have growth := CorePageSource.applyWrites_pageCount_ge oldImage writes
    simpa [image] using Nat.lt_of_lt_of_le positive growth
  rcases imageBytes_eq_firstPage_append image imagePositive with
    ⟨suffix, imageBytes⟩
  have read : image.read 0 = oldImage.read 0 := by
    exact GrowableStorage.applyWrites_read_of_not_written oldImage writes 0
      notWritten
  refine .intro header (pageSuffix ++ suffix) ?_ pageCount pageSize reserved utf8
  rw [imageBytes, read, bytes, List.append_assoc]
  exact FileFormat.decodeDatabaseHeader_encode header (pageSuffix ++ suffix)

/-- A valid old header transports across a page-zero-free, non-growing write
set.  Decoder soundness supplies the exact first-page prefix, so callers no
longer have to unpack header fields manually. -/
theorem SQLiteHeaderMatches.applyWritesOfUnchangedPageZero
    {oldImage : GrowableStorage.Image PhysicalCodec.pageSize}
    (validHeader : SQLiteHeaderMatches oldImage)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (positive : 0 < oldImage.pageCount)
    (notWritten : ∀ write ∈ writes, 0 ≠ write.pageId)
    (stableCount :
      (GrowableStorage.applyWrites oldImage writes).pageCount =
        oldImage.pageCount) :
    SQLiteHeaderMatches (GrowableStorage.applyWrites oldImage writes) := by
  rcases validHeader.firstPage positive with
    ⟨header, pageSuffix, bytes, pageCount, pageSize, reserved, utf8⟩
  apply sqliteHeaderMatches_of_unchangedPageZero oldImage writes notWritten
    positive header pageSuffix bytes
  · rw [stableCount]
    exact pageCount
  · exact pageSize
  · exact reserved
  · exact utf8

/-- Empty-freelist framing is transported by the same page-zero frame as the
ordinary header.  This lets a sequence of allocation-preserving point updates
reuse the localized proof inductively instead of assuming an empty freelist at
every step. -/
theorem SQLiteHeaderMatches.FreelistEmpty.applyWritesOfUnchangedPageZero
    {oldImage : GrowableStorage.Image PhysicalCodec.pageSize}
    (oldHeader : SQLiteHeaderMatches oldImage)
    (empty : oldHeader.FreelistEmpty)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (positive : 0 < oldImage.pageCount)
    (notWritten : ∀ write ∈ writes, 0 ≠ write.pageId)
    (postHeader : SQLiteHeaderMatches
      (GrowableStorage.applyWrites oldImage writes)) :
    postHeader.FreelistEmpty := by
  rcases oldHeader.firstPage_of_freelistEmpty empty positive with
    ⟨header, pageSuffix, bytes, _, _, _, _, firstFree, freeCount⟩
  let image := GrowableStorage.applyWrites oldImage writes
  have imagePositive : 0 < image.pageCount := by
    have growth := CorePageSource.applyWrites_pageCount_ge oldImage writes
    simpa [image] using Nat.lt_of_lt_of_le positive growth
  rcases imageBytes_eq_firstPage_append image imagePositive with
    ⟨suffix, imageBytes⟩
  have read : image.read 0 = oldImage.read 0 := by
    exact GrowableStorage.applyWrites_read_of_not_written oldImage writes 0
      notWritten
  refine ⟨header, pageSuffix ++ suffix, ?_, firstFree, freeCount⟩
  rw [imageBytes, read, bytes, List.append_assoc]
  exact FileFormat.decodeDatabaseHeader_encode header (pageSuffix ++ suffix)

/-- The same exact page-zero write supplies the catalog component without
decoding or comparing the complete database. -/
theorem catalogRead_of_pageZeroWrite
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pageZero : GrowableStorage.PageWrite PhysicalCodec.pageSize)
    (member : pageZero ∈ writes) (zero : pageZero.pageId = 0)
    (catalog : List CoreDecode.CatalogEntry)
    (decoded : CoreDecode.decodeCatalogForOpen pageZero.page.bytes.toList =
      some catalog) :
    (localizedSource oldImage writes).readPage 1 >>=
        CoreDecode.decodeCatalogForOpen = some catalog := by
  have read := CorePageSource.readPage_applyWrites_of_mem oldImage distinct
    member
  rw [zero] at read
  change (CorePageSource.ofStorageImage
    (GrowableStorage.applyWrites oldImage writes)).readPage 1 >>=
      CoreDecode.decodeCatalogForOpen = some catalog
  rw [read]
  exact decoded

/-- A page-local write set which omits page zero preserves the exact catalog
read.  This closes the catalog component for the common constant-page-count
write path without re-decoding or comparing the database. -/
theorem catalogRead_of_unchangedPageZero
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (positive : 0 < oldImage.pageCount)
    (notWritten : ∀ write ∈ writes, 0 ≠ write.pageId)
    (catalog : List CoreDecode.CatalogEntry)
    (decoded : (CorePageSource.ofStorageImage oldImage).readPage 1 >>=
      CoreDecode.decodeCatalogForOpen = some catalog) :
    (localizedSource oldImage writes).readPage 1 >>=
        CoreDecode.decodeCatalogForOpen = some catalog := by
  have newBound :
      0 < (GrowableStorage.applyWrites oldImage writes).pageCount := by
    have growth := CorePageSource.applyWrites_pageCount_ge oldImage writes
    exact Nat.lt_of_lt_of_le positive growth
  have read := CorePageSource.readPage_applyWrites_of_not_written
    oldImage writes 0 newBound positive notWritten
  change (CorePageSource.ofStorageImage
    (GrowableStorage.applyWrites oldImage writes)).readPage 1 >>=
      CoreDecode.decodeCatalogForOpen = some catalog
  rw [read]
  exact decoded

/-- Component-wise certificate for a live localized commit.  This is stronger
and more informative than assuming `RepresentsDatabase` for the post-image:
it exposes the exact catalog read, all table decodes, index reconstruction,
and SQLite header framing that must be established by the delta builder.

The fields are propositions and erase at runtime.  In particular, carrying
this certificate cannot add the former decode-and-compare validation pass. -/
structure LocalizedRepresentation
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (database : Core.Database) : Prop where
  header : SQLiteHeaderMatches (GrowableStorage.applyWrites oldImage writes)
  components : ∃ catalog : List CoreDecode.CatalogEntry,
    ((localizedSource oldImage writes).readPage 1 >>=
        CoreDecode.decodeCatalogForOpen = some catalog) ∧
    ((catalog.filter (fun entry => entry.kind == "table")).mapM
        (CoreDecode.decodeTableFrom (localizedSource oldImage writes)) =
      some (database.tables.map Core.Table.withoutIndexes)) ∧
    (CoreDecode.applyIndexesForOpen (localizedSource oldImage writes)
        database.withoutIndexes
        (catalog.filter (fun entry => entry.kind == "index")) =
      some database.canonicalize)

/-- The strong proof-carrying physical-state invariant closes every logical
field of a localized durability certificate at once.  Only SQLite header
framing remains a separate obligation because it belongs to the growable
image rather than to table/index topology. -/
def localizedRepresentation_of_databaseOnSource
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (state : CoreChunkPageState.State)
    (header : SQLiteHeaderMatches
      (GrowableStorage.applyWrites oldImage writes))
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (localizedSource oldImage writes) state) :
    LocalizedRepresentation oldImage writes state.database := by
  rcases physical.pageSourceRepresents with
    ⟨catalog, catalogRead, tablesRead, indexesRead⟩
  exact { header, components := ⟨catalog, catalogRead, tablesRead, indexesRead⟩ }

/-- Transparent proof certificate for the ordinary live localized writer.

Unlike a bare post-image decoder equation, every field names a fact produced
by the actual delta pipeline: represented old components, exact numbered
writes, unchanged catalog/header bytes, retained-table noninterference, and
the exact changed table.  The final alternative is intentional: an indexed
table update preserves all page identities, while a wholly indexless database
has no physical index run to preserve.  Mixed databases growing an unindexed
table use the separately proved bulk compatibility path. -/
structure OrdinaryLocalizedCommit
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta) : Prop where
  physical : CoreLocalizedRepresentation.DatabaseOnSource
    (CorePageSource.ofStorageImage oldImage) state
  allocation : state.AllocationWellFormed
  updated : CoreChunkPageDelta.updateState? state database = some delta
  converted : CoreChunkPageDelta.writes delta.table = some writes
  distinct : writes.Pairwise (fun left right => left.pageId ≠ right.pageId)
  header : SQLiteHeaderMatches (GrowableStorage.applyWrites oldImage writes)
  catalogPreserved : ∀ catalog,
    ((CorePageSource.ofStorageImage oldImage).readPage 1 >>=
        CoreDecode.decodeCatalogForOpen = some catalog) →
    ((CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage writes)).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog)
  retained : ∀ (old : CoreChunkPageState.TableState)
    (_member : old ∈ state.tables)
    (table : Core.Table) (equivalent : old.table.Equiv table),
    old ≠ delta.table.before →
    CoreLocalizedRepresentation.TableOnSource
        (CorePageSource.ofStorageImage oldImage) old →
      ∃ _physical : CoreLocalizedRepresentation.TableOnSource
          (CorePageSource.ofStorageImage
            (GrowableStorage.applyWrites oldImage writes))
          (old.retarget table equivalent), True
  changed : ∃ physical : CoreLocalizedRepresentation.TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage writes)) delta.table.after,
      physical.encoding.overflowPages = []
  preservationMode : delta.table.before.table.indexes ≠ [] ∨
    ∀ table ∈ database.tables, table.indexes = []

def OrdinaryLocalizedCommit.databaseOnSource
    {oldImage : GrowableStorage.Image PhysicalCodec.pageSize}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (commit : OrdinaryLocalizedCommit oldImage writes state database delta) :
    CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage writes)) delta.after := by
  rcases commit.changed with ⟨changed, inline⟩
  have retained : ∀ (old : CoreChunkPageState.TableState)
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      CoreLocalizedRepresentation.TableOnSource
          (CorePageSource.ofStorageImage oldImage) old →
        CoreLocalizedRepresentation.TableOnSource
          (CorePageSource.ofStorageImage
            (GrowableStorage.applyWrites oldImage writes))
          (old.retarget table equivalent) := by
    intro old member table equivalent different physical
    exact Classical.choose
      (commit.retained old member table equivalent different physical)
  rcases commit.preservationMode with indexed | indexless
  · exact commit.physical.updateStateApplyWritesBelow oldImage writes
      commit.distinct commit.allocation commit.updated commit.catalogPreserved
      retained changed indexed commit.converted inline
  · exact commit.physical.updateStateIndexless commit.allocation commit.updated
      indexless commit.catalogPreserved retained changed

/-- The ordinary localized preparation certificate closes the complete
post-image representation premise consumed by crash atomicity. -/
def OrdinaryLocalizedCommit.localizedRepresentation
    {oldImage : GrowableStorage.Image PhysicalCodec.pageSize}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (commit : OrdinaryLocalizedCommit oldImage writes state database delta) :
    LocalizedRepresentation oldImage writes database := by
  have represented := localizedRepresentation_of_databaseOnSource oldImage
    writes delta.after commit.header commit.databaseOnSource
  have endpoints := CoreChunkPageDelta.updateState?_endpoints commit.updated
  simpa [endpoints.2] using represented

/-- Construct the changed-table component directly over the exact final write
list retained by `PreparedLocalizedWrites`.  The old table witness and its page
bounds are projected from the database invariant; the planner's base-write
membership and allocator frame theorem discharge the page-zero/freelist
extension.  Consequently callers no longer need to manufacture the changed
table certificate independently from the values consumed by the live writer.

The remaining explicit inputs describe the two inline overflow encodings and
the post-state allocator/decoder bounds.  They are the next, narrower adapter
obligations; none is a whole-database decode or byte comparison. -/
noncomputable def CoreFileAdapter.PreparedOrdinaryDelta.changedTableOnFinalWrites
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta state database delta)
    (final : CoreFileAdapter.PreparedLocalizedWrites delta.after.freePages
      prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) state)
    (afterAllocation : delta.after.AllocationWellFormed)
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
    (afterInline : afterEncoding.overflowPages = [])
    (heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage final.writes)).pageCount + 1) :
    CoreLocalizedRepresentation.TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage final.writes))
      delta.table.after := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  have beforeInline' : before.encoding.overflowPages = [] := by
    simpa [before, selected] using beforeInline
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
  have metadata := CoreChunkPageDelta.TableDelta.tablePagesSufficient_metadata
    delta.table (CoreChunkPageDelta.updateState?_tablePagesSufficient
      prepared.updated)
  apply before.updateStateInlineExtension oldImage state database delta
    prepared.writes final.writes prepared.updated prepared.writesEq final.distinct
    final.base_mem metadata.1 beforeInline' afterEncoding afterEncoded'
  · intro write writeMember notBase page pageMember
    exact final.added_disjoint_encoded_table_tree afterAllocation selected.2
      afterTree writeMember notBase pageMember
  · exact afterInline
  · exact before.treeBounds oldImage
  · exact heightBound

end CoreDurability

end SQLeanite
