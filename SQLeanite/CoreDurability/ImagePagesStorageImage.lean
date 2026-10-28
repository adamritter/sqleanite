import SQLeanite.CoreFileAdapter.ByteArrayPageSourceEqStorageImage
import SQLeanite.CoreLocalizedRepresentation.DatabaseOnSourceUpdateStateApplyWritesBelowExtension
import SQLeanite.CorePageCodec.PageSourceRepresentsEncodeBulkIn

namespace SQLeanite
namespace CoreDurability

theorem imagePages_storageImage (image : CoreFile.Image) :
    PhysicalJournalRecovery.imagePages (CoreFileAdapter.storageImage image) =
      image.pages.map CoreFile.Page.storage := by
  apply List.ext_getElem
  · rw [PhysicalJournalRecovery.imagePages_length]
    simp [CoreFileAdapter.storageImage, CoreFile.Image.pageCount]
  · intro index leftBound rightBound
    have bound : index < image.pages.length := by simpa using rightBound
    simp [PhysicalJournalRecovery.imagePages, CoreFileAdapter.storageImage,
      CoreFile.Image.pageCount, leftBound, rightBound, bound]

theorem imageBytes_storageImage (image : CoreFile.Image) :
    PhysicalJournalRecovery.imageBytes (CoreFileAdapter.storageImage image) =
      image.fileBytes := by
  unfold PhysicalJournalRecovery.imageBytes CoreFile.Image.fileBytes
  rw [imagePages_storageImage]
  induction image.pages with
  | nil => rfl
  | cons page pages induction =>
      simp [DiskFormat.encodePages, CoreFile.Page.storage, induction]

theorem readsPagesFrom_storageImage_tail (image : CoreFile.Image) :
    CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage (CoreFileAdapter.storageImage image)) 2
      image.pages.tail := by
  have sourceExact :
      CorePageSource.ofStorageImage (CoreFileAdapter.storageImage image) =
        CoreDecode.PageSource.ofList (image.pages.map CoreFile.Page.bytes) := by
    unfold CorePageSource.ofStorageImage
    rw [imagePages_storageImage]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro page _
    simp [CoreFile.Page.storage]
  rw [sourceExact]
  exact CoreDecode.ReadsPagesFrom.ofList_tail image.pages

/-- The array-backed live page source reads exactly the pages of its bulk
image.  The array is an execution optimization only; it does not alter the
logical source consumed by representation proofs. -/
theorem pageSource_storageImage (image : CoreFile.Image) :
    CorePageSource.ofStorageImage (CoreFileAdapter.storageImage image) =
      CoreDecode.PageSource.ofList
        (image.pages.map CoreFile.Page.bytes) := by
  unfold CorePageSource.ofStorageImage
  rw [imagePages_storageImage]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro page _
  simp [CoreFile.Page.storage]

/-- The concrete storage image emitted by the live bulk writer carries the
strong per-table physical-layout invariant, not only a whole-decoder
equation.  This is the initial generated-image witness localized commits
preserve. -/
theorem exists_tablesOnStorage_encodeBulk
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image) :
    ∃ state : CoreChunkPageState.State,
      CoreChunkPageState.State.build? database = some state ∧
      CoreLocalizedRepresentation.TablesOnSource
        (CorePageSource.ofStorageImage
          (CoreFileAdapter.storageImage image))
        (state.tables.map fun table => CoreDecode.CatalogEntry.ofEncoded
          (CorePageCodec.chunkTableCatalogEntry table)) state.tables := by
  apply CoreLocalizedRepresentation.exists_tablesOnSource_encodeBulk_in
    database image encoded
  · exact readsPagesFrom_storageImage_tail image
  · simp [CoreFileAdapter.storageImage, CoreFile.Image.pageCount]

/-- A canonical live bulk image establishes the complete proof-carrying
physical state: catalog, table/overflow topology, and promoted index entries
all refer to the exact bytes exposed by the live array-backed page source. -/
theorem exists_databaseOnStorage_encodeBulk
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image) :
    ∃ state : CoreChunkPageState.State,
      CoreChunkPageState.State.build? database = some state ∧
      CoreLocalizedRepresentation.DatabaseOnSource
        (CorePageSource.ofStorageImage
          (CoreFileAdapter.storageImage image)) state := by
  apply CoreLocalizedRepresentation.exists_databaseOnSource_encodeBulk_in
    utf8 database image encoded
  · rw [pageSource_storageImage]
  · exact readsPagesFrom_storageImage_tail image
  · simp [CoreFileAdapter.storageImage, CoreFile.Image.pageCount]

/-- Freelist padding changes page-zero framing and appends unreachable pages,
but preserves the complete active physical state.  This strengthens the
existing whole-decoder theorem for shrinking commits with the table/index
ownership evidence needed by the next localized transaction. -/
theorem exists_databaseOnStorage_padded
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (layout : CoreMultiFreelist.Layout)
    (encoded : CorePageCodec.encodeBulk database = some layout.image) :
    ∃ state : CoreChunkPageState.State,
      CoreChunkPageState.State.build? database = some state ∧
      CoreLocalizedRepresentation.DatabaseOnSource
        (CorePageSource.ofStorageImage
          (CoreFileAdapter.storageImage layout.paddedImage)) state := by
  let source : CoreDecode.PageSource :=
    .ofList (layout.paddedImage.pages.map CoreFile.Page.bytes)
  have physical :=
    CoreLocalizedRepresentation.exists_databaseOnSource_encodeBulk_in
      utf8 database layout.image encoded source
      (by
        have catalogSame :=
          CorePageCodec.decodeCatalogForOpen_encodeBulk_replaceHeader utf8
            database layout.image encoded layout.firstPage
            layout.remainingActive layout.pages_eq
            (FileFormat.encodeDatabaseHeader layout.databaseHeader)
            (FileFormat.encodeDatabaseHeader_length layout.databaseHeader)
        have paddedFirst : source.readPage 1 =
            some layout.schemaPage.bytes := by
          simp [source, CoreDecode.PageSource.ofList, CoreDecode.page?,
            CoreMultiFreelist.Layout.paddedImage,
            CoreMultiFreelist.Layout.pages,
            CoreMultiFreelist.Layout.activePages]
        have canonicalFirst :
            (CoreDecode.PageSource.ofList
              (layout.image.pages.map CoreFile.Page.bytes)).readPage 1 =
                some layout.firstPage.bytes := by
          rw [layout.pages_eq]
          simp [CoreDecode.PageSource.ofList, CoreDecode.page?]
        rw [paddedFirst, canonicalFirst]
        simp only [Option.bind_eq_bind, Option.bind]
        simpa [CoreMultiFreelist.Layout.schemaPage] using catalogSame)
      (by
        rw [layout.pages_eq]
        have reads := CoreDecode.ReadsPagesFrom.ofList_append
          [layout.schemaPage.bytes] layout.remainingActive
          (layout.freelistPages.map CoreFile.Page.bytes)
        simpa [source, CoreMultiFreelist.Layout.paddedImage,
          CoreMultiFreelist.Layout.pages,
          CoreMultiFreelist.Layout.activePages,
          List.map_append] using reads)
      (by
        change layout.image.pageCount ≤
          (layout.paddedImage.pages.map CoreFile.Page.bytes).length
        rw [List.length_map]
        change layout.image.pageCount ≤ layout.pages.length
        rw [CoreMultiFreelist.Layout.pages_length]
        exact layout.active_le_total)
  rw [pageSource_storageImage] at ⊢
  exact physical

theorem decode_imageBytes_encodeBulk (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image) :
    CoreDecode.decode
        (PhysicalJournalRecovery.imageBytes
          (CoreFileAdapter.storageImage image)) =
      some database.canonicalize := by
  rw [imageBytes_storageImage]
  exact CorePageCodec.decode_encodeBulk utf8 database image encoded

/-- A physical page image represents a Core database when the actual bytes
read by recovery decode to that database.  Keeping this relation independent
of a particular encoder is what lets the same crash theorem cover canonical
bulk images, freelist-padded images, and page-local updates. -/
def RepresentsDatabase
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (database : Core.Database) : Prop :=
  CoreDecode.decode (PhysicalJournalRecovery.imageBytes image) =
    some database.canonicalize

/-- The byte decoder's non-logical framing obligations for a growable image.
The catalog/table/index meaning is deliberately kept in
`PageSourceRepresents`; this relation records only the SQLite header fields
which connect the byte string to that page source. -/
inductive SQLiteHeaderMatches
    (image : GrowableStorage.Image PhysicalCodec.pageSize) : Prop where
  | intro (header : FileFormat.DatabaseHeader) (suffix : List UInt8)
      (decoded : FileFormat.decodeDatabaseHeader
        (PhysicalJournalRecovery.imageBytes image) = some (header, suffix))
      (pageCount : header.databaseSizePages.val = image.pageCount)
      (pageSize : header.headerPrefix.pageSizeField.val =
        PhysicalCodec.pageSize)
      (reserved : header.headerPrefix.reservedSpace = 0)
      (utf8 : header.textEncoding.val = 1) :
      SQLiteHeaderMatches image

/-- Component-wise physical representation plus the four SQLite framing
fields implies representation by the public whole-byte decoder.  This is the
composition rule needed by localized writes: they may preserve or re-prove
catalog/table/index components independently and close the byte-level result
without another execution or validation pass. -/
theorem pageSourceRepresents_storageImage
    {image : GrowableStorage.Image PhysicalCodec.pageSize}
    {database : Core.Database}
    (header : SQLiteHeaderMatches image)
    (represents : CoreDecode.PageSourceRepresents
      (CorePageSource.ofStorageImage image) database) :
    RepresentsDatabase image database := by
  rcases header with ⟨header, suffix, decoded, pageCount, pageSize,
    reserved, utf8⟩
  unfold RepresentsDatabase CoreDecode.decode
  rw [decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [pageCount]
  rw [dif_pos pageSize, dif_pos reserved, dif_pos utf8]
  have fileLength :
      (PhysicalJournalRecovery.imageBytes image).length =
        image.pageCount * PhysicalCodec.pageSize := by
    unfold PhysicalJournalRecovery.imageBytes
    rw [DiskFormat.encodePages_length,
      PhysicalJournalRecovery.imagePages_length]
    exact Nat.mul_comm _ _
  rw [dif_pos fileLength, CorePageSource.pages_imageBytes]
  exact represents.decode

/-- The exact page source produced by a localized write list.  Naming it once
keeps catalog, table, index, and header certificates definitionally aligned. -/
def localizedSource
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    CoreDecode.PageSource :=
  CorePageSource.ofStorageImage (GrowableStorage.applyWrites oldImage writes)

/-- Physical interpretation of the two changed-index certificates emitted by
the live adapter.  Rebuilt indexes carry encoder/read-coverage facts; routed
leaf mutations carry a decoder equation over the exact post-write source.
Keeping the cases in a proposition erases all of this evidence at runtime. -/
inductive LocalizedIndexReadable (source : CoreDecode.PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index} :
    CoreFileAdapter.LocalizedIndexCertificate rootPage table index → Prop where
  | encoded (certificate : CoreFileAdapter.CertifiedIndexEncoding
      rootPage table index)
      (reads : CoreDecode.ReadsPagesFrom source rootPage certificate.value.pages)
      (rootPositive : 0 < rootPage)
      (pageBound : rootPage + certificate.value.pages.length < 2 ^ 32)
      (withinSource : rootPage + certificate.value.pages.length ≤
        source.pageCount + 1) :
      LocalizedIndexReadable source (.encoded certificate)
  | decoded (certificate : CoreFileAdapter.DecodedIndexCertificate
      rootPage table index)
      (sourceExact : certificate.source = source) :
      LocalizedIndexReadable source (.decoded certificate)

/-- Either live changed-index certificate supplies exactly the physical head
of an `IndexesDecode` run.  In particular, the decoded fast path is accepted
only after its synthetic mutation source is identified with the actual
post-write source; this names the last nontrivial adapter obligation instead
of silently trusting that construction. -/
theorem indexesDecode_consLocalized
    {source : CoreDecode.PageSource} {table : Core.Table}
    {entry : CoreDecode.CatalogEntry}
    {entries : List CoreDecode.CatalogEntry} {index : Core.Index}
    {rootPage : Nat}
    {certificate : CoreFileAdapter.LocalizedIndexCertificate
      rootPage table index}
    (sameTable : entry.table = table.schema.name)
    (sameRoot : entry.rootPage = rootPage)
    (metadata : CoreDecode.decodeCanonicalIndex table.schema
      table.schema.name entry = some index)
    (readable : LocalizedIndexReadable source certificate)
    (tail : CoreLocalizedRepresentation.IndexesDecode source table entries) :
    CoreLocalizedRepresentation.IndexesDecode source table
      (entry :: entries) := by
  cases readable with
  | encoded certified reads rootPositive pageBound withinSource =>
      exact CoreLocalizedRepresentation.IndexesDecode.consEncoded
        sameTable sameRoot metadata certified.encoded reads rootPositive
        pageBound withinSource tail
  | decoded certified sourceExact =>
      refine .cons sameTable metadata ?_ tail
      rw [sameRoot, ← sourceExact]
      exact certified.exact

/-- The storage witness carried by a page-directed live mutation supplies the
exact `LocalizedIndexReadable` premise for its actual post-write image. -/
theorem localizedIndexReadable_of_onStorage
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (certificate : CoreFileAdapter.DecodedIndexCertificate
      rootPage table index)
    (onStorage : certificate.OnStorage writes) :
    ∃ oldImage : GrowableStorage.Image PhysicalCodec.pageSize,
      LocalizedIndexReadable (localizedSource oldImage writes)
        (.decoded certificate) := by
  rcases onStorage with ⟨oldImage, exactSource⟩
  refine ⟨oldImage, .decoded certificate ?_⟩
  simpa [localizedSource] using exactSource

/-- The storage witness carried by a rebuilt-index delta supplies the encoded
case of the same physical readability contract.  Unlike the historical
encode/decode validation pass, this proof permits unchanged pages to be
omitted from the write set: their exact old bytes are part of `OnStorage`. -/
theorem localizedIndexReadable_of_encodedOnStorage
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (certificate : CoreFileAdapter.CertifiedIndexEncoding
      rootPage table index)
    (onStorage : certificate.OnStorage writes) :
    ∃ oldImage : GrowableStorage.Image PhysicalCodec.pageSize,
      LocalizedIndexReadable (localizedSource oldImage writes)
        (.encoded certificate) := by
  rcases onStorage with
    ⟨oldImage, reads, rootPositive, pageBound, withinSource⟩
  refine ⟨oldImage, .encoded certificate reads rootPositive pageBound ?_⟩
  simpa [localizedSource] using withinSource

/-- A prepared live index mutation retains enough erased evidence to install
its physical entry into the exact catalog run.  In particular, this theorem
uses the catalog table/root/SQL fields carried by the preparation result; an
index byte certificate alone cannot be attached to an unrelated entry. -/
theorem localizedLastIndexDelta_cons
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.LocalizedLastIndexDelta delta) :
    ∃ oldImage : GrowableStorage.Image PhysicalCodec.pageSize,
      ∀ {entries : List CoreDecode.CatalogEntry},
        CoreLocalizedRepresentation.IndexesDecode
            (localizedSource oldImage prepared.writes)
            delta.table.after.table entries →
          CoreLocalizedRepresentation.IndexesDecode
            (localizedSource oldImage prepared.writes)
            delta.table.after.table (prepared.entry :: entries) := by
  cases certificateEq : prepared.certificate with
  | encoded certificate =>
      have onStorage : certificate.OnStorage prepared.writes := by
        simpa [certificateEq] using prepared.storage
      rcases localizedIndexReadable_of_encodedOnStorage certificate onStorage with
        ⟨oldImage, readable⟩
      refine ⟨oldImage, ?_⟩
      intro entries tail
      exact indexesDecode_consLocalized prepared.entryTable prepared.entryRoot
        prepared.entryMetadata readable tail

  | decoded certificate =>
      have onStorage : certificate.OnStorage prepared.writes := by
        simpa [certificateEq] using prepared.storage
      rcases localizedIndexReadable_of_onStorage certificate onStorage with
        ⟨oldImage, readable⟩
      refine ⟨oldImage, ?_⟩
      intro entries tail
      exact indexesDecode_consLocalized prepared.entryTable prepared.entryRoot
        prepared.entryMetadata readable tail

/-- The changed-index preparation selected by the live engine is tied to the
same logical state transition and table-page lists that produced its combined
table/index overlay.  These equations are kept together so a durability proof
cannot silently substitute a separately rebuilt table delta. -/
theorem CoreFileAdapter.LocalizedLastIndexDelta.liveDeltaEquations
    {delta : CoreChunkPageDelta.StateDelta}
    (prepared : CoreFileAdapter.LocalizedLastIndexDelta delta) :
    CoreChunkPageDelta.updateStateCandidate? delta.before
        delta.after.database = some delta ∧
      CoreChunkPageDelta.beforeWrites delta.table =
        some prepared.tableExpectedBefore ∧
      CoreChunkPageDelta.writes delta.table = some prepared.tableWrites := by
  exact ⟨prepared.candidate, prepared.tableExpectedBeforeEq,
    prepared.tableWritesEq⟩

/-- A nonempty growable image starts with the bytes returned by page zero.
The suffix is intentionally abstract: SQLite header decoding consumes exactly
the first 100 bytes and does not need to inspect the remaining pages. -/
theorem imageBytes_eq_firstPage_append
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (positive : 0 < image.pageCount) :
    ∃ suffix,
      PhysicalJournalRecovery.imageBytes image =
        (image.read 0).bytes.toList ++ suffix := by
  cases count : image.pageCount with
  | zero => simp [count] at positive
  | succ remaining =>
      unfold PhysicalJournalRecovery.imageBytes
      unfold PhysicalJournalRecovery.imagePages
      rw [count]
      rw [List.range_succ_eq_map]
      simp [DiskFormat.encodePages]

theorem firstPage_of_decodedHeader
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (header : FileFormat.DatabaseHeader) (suffix : List UInt8)
    (decoded : FileFormat.decodeDatabaseHeader
      (PhysicalJournalRecovery.imageBytes image) = some (header, suffix))
    (positive : 0 < image.pageCount) :
    ∃ pageSuffix, (image.read 0).bytes.toList =
      FileFormat.encodeDatabaseHeader header ++ pageSuffix := by
  have exactBytes := FileFormat.decodeDatabaseHeader_sound decoded
  rcases imageBytes_eq_firstPage_append image positive with
    ⟨imageSuffix, imageBytes⟩
  have joined : (image.read 0).bytes.toList ++ imageSuffix =
      FileFormat.encodeDatabaseHeader header ++ suffix :=
    imageBytes.symm.trans exactBytes
  have firstLength : (image.read 0).bytes.toList.length =
      PhysicalCodec.pageSize := by
    simpa using (image.read 0).sizeInvariant
  have firstLong : 100 ≤ (image.read 0).bytes.toList.length := by
    rw [firstLength]
    simp [PhysicalCodec.pageSize]
  have encodedLength : (FileFormat.encodeDatabaseHeader header).length = 100 :=
    FileFormat.encodeDatabaseHeader_length header
  have taken := congrArg (List.take 100) joined
  have firstPrefix : (image.read 0).bytes.toList.take 100 =
      FileFormat.encodeDatabaseHeader header := by
    rw [List.take_append_of_le_length firstLong,
      List.take_append_of_le_length (by omega :
        100 ≤ (FileFormat.encodeDatabaseHeader header).length)] at taken
    rw [List.take_of_length_le (Nat.le_of_eq encodedLength)] at taken
    exact taken
  refine ⟨(image.read 0).bytes.toList.drop 100, ?_⟩
  calc
    (image.read 0).bytes.toList =
        (image.read 0).bytes.toList.take 100 ++
          (image.read 0).bytes.toList.drop 100 :=
      (List.take_append_drop 100 (image.read 0).bytes.toList).symm
    _ = FileFormat.encodeDatabaseHeader header ++
          (image.read 0).bytes.toList.drop 100 := by rw [firstPrefix]

/-- A validated growable-image header yields the exact canonical first-page
prefix consumed by the localized header frame theorem. -/
theorem SQLiteHeaderMatches.firstPage
    {image : GrowableStorage.Image PhysicalCodec.pageSize}
    (validHeader : SQLiteHeaderMatches image) (positive : 0 < image.pageCount) :
    ∃ (header : FileFormat.DatabaseHeader) (pageSuffix : List UInt8),
      (image.read 0).bytes.toList =
        FileFormat.encodeDatabaseHeader header ++ pageSuffix ∧
      header.databaseSizePages.val = image.pageCount ∧
      header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize ∧
      header.headerPrefix.reservedSpace = 0 ∧ header.textEncoding.val = 1 := by
  rcases validHeader with
    ⟨header, suffix, decoded, pageCount, pageSize, reserved, utf8⟩
  rcases firstPage_of_decodedHeader image header suffix decoded positive with
    ⟨pageSuffix, bytes⟩
  exact ⟨header, pageSuffix, bytes, pageCount, pageSize, reserved, utf8⟩

/-- The generated/YCSB point-update case has no physical freelist.  Keeping
this as a property of the validated header ties the planner's empty logical
freelist to the two corresponding SQLite header fields. -/
def SQLiteHeaderMatches.FreelistEmpty
    {image : GrowableStorage.Image PhysicalCodec.pageSize}
    (_validHeader : SQLiteHeaderMatches image) : Prop :=
  ∃ header suffix,
    FileFormat.decodeDatabaseHeader (PhysicalJournalRecovery.imageBytes image) =
      some (header, suffix) ∧
    header.firstFreelistTrunk.val = 0 ∧
    header.freelistPageCount.val = 0

/-- The canonical bulk encoder establishes the exact SQLite framing consumed
by the first localized transaction.  This is derived from the emitted schema
page; no reopen or whole-file decoder is run to manufacture the proof. -/
theorem sqliteHeaderMatches_storageImage_encodeBulk
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image) :
    SQLiteHeaderMatches (CoreFileAdapter.storageImage image) := by
  rcases CorePageCodec.encodeBulk_header encoded with
    ⟨count, schema, remaining, body, pagesEqual, countEqual, headerEqual⟩
  let header := CoreFile.databaseHeader count
  let suffix := body ++ remaining.flatMap CoreFile.Page.bytes
  refine .intro header suffix ?_ ?_ (by rfl) (by rfl) (by rfl)
  · rw [imageBytes_storageImage]
    unfold CoreFile.Image.fileBytes
    rw [pagesEqual]
    simp only [List.flatMap_cons]
    rw [headerEqual]
    simpa [header, suffix, List.append_assoc] using
      FileFormat.decodeDatabaseHeader_encode header suffix
  · simpa [header, CoreFile.databaseHeader, CoreFileAdapter.storageImage,
      CoreFile.Image.pageCount] using countEqual.symm

end CoreDurability

end SQLeanite
