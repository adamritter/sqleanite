import SQLeanite.PageFormat.DecodeLeafIndexCellEncodeInline

namespace SQLeanite
namespace FileFormat

def BTreeCellBody.pageType {usable : UsablePageSize} :
    BTreeCellBody usable → BTreePageType
  | .interiorTable _ => .interiorTable
  | .leafTable _ => .leafTable
  | .interiorIndex _ => .interiorIndex
  | .leafIndex _ => .leafIndex

def BTreeCellBody.encode {usable : UsablePageSize} :
    BTreeCellBody usable → List UInt8
  | .interiorTable cell => cell.encode
  | .leafTable cell => cell.encode
  | .interiorIndex cell => cell.encode
  | .leafIndex cell => cell.encode

theorem BTreeCellBody.encode_length_pos {usable : UsablePageSize}
    (body : BTreeCellBody usable) : 0 < body.encode.length := by
  cases body with
  | interiorTable cell =>
      change 0 < cell.encode.length
      rw [InteriorTableCell.encode_length]
      omega
  | leafTable cell =>
      change 0 < cell.encode.length
      rw [TableLeafCell.encode_length]
      have sizePositive := sqliteVarintSize_positive cell.payloadSize.val
      omega
  | interiorIndex cell =>
      change 0 < cell.encode.length
      rw [InteriorIndexCell.encode_length]
      omega
  | leafIndex cell =>
      change 0 < cell.encode.length
      rw [LeafIndexCell.encode_length]
      have sizePositive := sqliteVarintSize_positive cell.payloadSize.val
      omega

theorem BTreeCellBody.encode_ne_nil {usable : UsablePageSize}
    (body : BTreeCellBody usable) : body.encode ≠ [] := by
  intro empty
  have positive := body.encode_length_pos
  rw [empty] at positive
  simp at positive

/-- A typed cell can only inhabit the matching kind of B-tree page. -/
structure TypedBTreeCell (usable : UsablePageSize) (pageType : BTreePageType) where
  offset : U16Value
  body : BTreeCellBody usable
  matchesPage : body.pageType = pageType
  endWithinPage : offset.val + body.encode.length ≤ usable.val
  deriving DecidableEq

def TypedBTreeCell.toPlacedCell {usable : UsablePageSize}
    {pageType : BTreePageType} (cell : TypedBTreeCell usable pageType) :
    PlacedCell usable.val := {
  offset := cell.offset
  bytes := cell.body.encode
  nonempty := cell.body.encode_ne_nil
  endWithinPage := cell.endWithinPage }

/-- Typed cells paired with the generic layout carrying pointer agreement and
interval disjointness. -/
structure TypedBTreePageLayout (usable : UsablePageSize) where
  generic : BTreeCellLayout usable.val
  cells : List (TypedBTreeCell usable generic.pagePrefix.header.header.pageType)
  placementsAgree : generic.cells = cells.map TypedBTreeCell.toPlacedCell
  deriving DecidableEq

def TypedBTreePageLayout.encodePage {usable : UsablePageSize}
    (layout : TypedBTreePageLayout usable) : Storage.Page usable.val :=
  layout.generic.encodePage

theorem TypedBTreePageLayout.cellCount_eq {usable : UsablePageSize}
    (layout : TypedBTreePageLayout usable) :
    layout.cells.length =
      layout.generic.pagePrefix.header.header.common.cellCount.val := by
  rw [← layout.generic.cellCount_eq]
  rw [layout.placementsAgree]
  simp

theorem TypedBTreePageLayout.all_cells_match {usable : UsablePageSize}
    (layout : TypedBTreePageLayout usable)
    (cell : TypedBTreeCell usable layout.generic.pagePrefix.header.header.pageType)
    (_member : cell ∈ layout.cells) :
    cell.body.pageType = layout.generic.pagePrefix.header.header.pageType :=
  cell.matchesPage

def PageNumber.WithinDatabase (pageCount : Nat) (number : PageNumber) : Prop :=
  number.value.val ≤ pageCount

instance (pageCount : Nat) (number : PageNumber) :
    Decidable (number.WithinDatabase pageCount) := by
  unfold PageNumber.WithinDatabase
  infer_instance

def BTreePageHeader.ReferencesWithin (pageCount : Nat) : BTreePageHeader → Prop
  | .interiorIndex _ rightmostPage | .interiorTable _ rightmostPage =>
    rightmostPage.val ≤ pageCount
  | .leafIndex _ | .leafTable _ => True

instance (pageCount : Nat) (header : BTreePageHeader) :
    Decidable (header.ReferencesWithin pageCount) := by
  cases header <;> simp [BTreePageHeader.ReferencesWithin] <;> infer_instance

def BTreePayloadData.ReferencesWithin (pageCount : Nat) : BTreePayloadData → Prop
  | .inline _ => True
  | .overflow _ firstOverflowPage => firstOverflowPage.WithinDatabase pageCount

instance (pageCount : Nat) (payload : BTreePayloadData) :
    Decidable (payload.ReferencesWithin pageCount) := by
  cases payload <;> simp [BTreePayloadData.ReferencesWithin] <;> infer_instance

def BTreeCellBody.ReferencesWithin {usable : UsablePageSize}
    (pageCount : Nat) : BTreeCellBody usable → Prop
  | .interiorTable cell =>
    cell.leftChildPage.WithinDatabase pageCount
  | .leafTable cell => cell.payload.data.ReferencesWithin pageCount
  | .interiorIndex cell =>
    cell.leftChildPage.WithinDatabase pageCount ∧
      cell.payload.data.ReferencesWithin pageCount
  | .leafIndex cell => cell.payload.data.ReferencesWithin pageCount

instance {usable : UsablePageSize} (pageCount : Nat) (body : BTreeCellBody usable) :
    Decidable (body.ReferencesWithin pageCount) := by
  cases body <;> simp [BTreeCellBody.ReferencesWithin] <;> infer_instance

def TypedBTreePageLayout.ReferencesWithin {usable : UsablePageSize}
    (layout : TypedBTreePageLayout usable) (pageCount : Nat) : Prop :=
  layout.generic.pagePrefix.header.header.ReferencesWithin pageCount ∧
    ∀ cell ∈ layout.cells, cell.body.ReferencesWithin pageCount

instance {usable : UsablePageSize} (layout : TypedBTreePageLayout usable)
    (pageCount : Nat) : Decidable (layout.ReferencesWithin pageCount) := by
  unfold TypedBTreePageLayout.ReferencesWithin
  infer_instance

theorem OverflowChainData.firstPage_mem_pageNumbers {usable : UsablePageSize}
    (chain : OverflowChainData usable) : chain.firstPage ∈ chain.pageNumbers := by
  cases chain <;> simp [OverflowChainData.firstPage, OverflowChainData.pageNumbers]

def OverflowChain.ReferencesWithin {usable : UsablePageSize}
    (chain : OverflowChain usable) (pageCount : Nat) : Prop :=
  ∀ number ∈ chain.data.pageNumbers, number.WithinDatabase pageCount

instance {usable : UsablePageSize} (chain : OverflowChain usable)
    (pageCount : Nat) : Decidable (chain.ReferencesWithin pageCount) := by
  unfold OverflowChain.ReferencesWithin
  infer_instance

structure BoundedOverflowChain (usable : UsablePageSize) (pageCount : Nat) where
  chain : OverflowChain usable
  referencesWithin : chain.ReferencesWithin pageCount
  deriving DecidableEq

def BoundedOverflowChain.firstPage {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount) : BoundedPageNumber pageCount := {
  number := chain.chain.firstPage
  withinDatabase := chain.referencesWithin _
    chain.chain.data.firstPage_mem_pageNumbers }

structure BoundedTypedBTreePageLayout (usable : UsablePageSize) (pageCount : Nat) where
  layout : TypedBTreePageLayout usable
  referencesWithin : layout.ReferencesWithin pageCount
  deriving DecidableEq

theorem BoundedTypedBTreePageLayout.header_references_within
    {usable : UsablePageSize} {pageCount : Nat}
    (layout : BoundedTypedBTreePageLayout usable pageCount) :
    layout.layout.generic.pagePrefix.header.header.ReferencesWithin pageCount :=
  layout.referencesWithin.1

theorem BoundedTypedBTreePageLayout.cell_references_within
    {usable : UsablePageSize} {pageCount : Nat}
    (layout : BoundedTypedBTreePageLayout usable pageCount)
    (cell : TypedBTreeCell usable
      layout.layout.generic.pagePrefix.header.header.pageType)
    (member : cell ∈ layout.layout.cells) :
    cell.body.ReferencesWithin pageCount :=
  layout.referencesWithin.2 cell member

def OverflowPage.toStoragePage {usable : UsablePageSize}
    (page : OverflowPage usable) : Storage.Page usable.val := {
  bytes := page.encode.toArray
  sizeInvariant := by simp [page.encode_length] }

theorem OverflowPage.toStoragePage_bytes {usable : UsablePageSize}
    (page : OverflowPage usable) : page.toStoragePage.bytes.toList = page.encode := by
  simp [OverflowPage.toStoragePage]

structure NumberedTypedBTreePage (usable : UsablePageSize) (pageCount : Nat) where
  pageNumber : BoundedPageNumber pageCount
  notFirstPage : pageNumber.number.value.val ≠ 1
  layout : BoundedTypedBTreePageLayout usable pageCount
  deriving DecidableEq

def NumberedTypedBTreePage.toPageWrite {usable : UsablePageSize} {pageCount : Nat}
    (page : NumberedTypedBTreePage usable pageCount) :
    Storage.PageWrite usable.val pageCount := {
  pageId := page.pageNumber.toPageId
  page := page.layout.layout.encodePage }

theorem NumberedTypedBTreePage.toPageWrite_pageId
    {usable : UsablePageSize} {pageCount : Nat}
    (page : NumberedTypedBTreePage usable pageCount) :
    page.toPageWrite.pageId = page.pageNumber.toPageId := rfl

theorem NumberedTypedBTreePage.write_read_same
    {usable : UsablePageSize} {pageCount : Nat}
    (disk : Storage.Disk usable.val pageCount)
    (page : NumberedTypedBTreePage usable pageCount) :
    (disk.write page.toPageWrite.pageId page.toPageWrite.page).read
      page.toPageWrite.pageId = page.toPageWrite.page := by
  exact Storage.Disk.read_write_same _ _ _

theorem BoundedOverflowChain.number_within_of_mem_toPages
    {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount)
    (numberedPage : PageNumber × OverflowPage usable)
    (member : numberedPage ∈ chain.chain.toPages) :
    numberedPage.1.WithinDatabase pageCount := by
  have mapped : numberedPage.1 ∈ chain.chain.toPages.map Prod.fst :=
    List.mem_map.mpr ⟨numberedPage, member, rfl⟩
  unfold OverflowChain.toPages at mapped
  rw [chain.chain.data.toPages_pageNumbers] at mapped
  exact chain.referencesWithin numberedPage.1 mapped

def BoundedOverflowChain.toPageWrites {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount) :
    List (Storage.PageWrite usable.val pageCount) :=
  chain.chain.toPages.attach.map fun attached =>
    let numberedPage := attached.val
    let boundedNumber : BoundedPageNumber pageCount := {
      number := numberedPage.1
      withinDatabase := by
        simpa [PageNumber.WithinDatabase] using
          chain.number_within_of_mem_toPages numberedPage attached.property }
    { pageId := boundedNumber.toPageId
      page := numberedPage.2.toStoragePage }

theorem BoundedOverflowChain.toPageWrites_length
    {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount) :
    chain.toPageWrites.length = chain.chain.data.pageCount := by
  simp [BoundedOverflowChain.toPageWrites,
    OverflowChain.toPages, chain.chain.data.toPages_length]

theorem BoundedOverflowChain.toPageWrites_nonempty
    {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount) : chain.toPageWrites ≠ [] := by
  intro empty
  have countPositive := chain.chain.data.pageCount_pos
  have lengthEquality := chain.toPageWrites_length
  rw [empty] at lengthEquality
  simp at lengthEquality
  omega

def collectVerifiedPageWrites {usable : UsablePageSize} {pageCount : Nat}
    (btreePages : List (NumberedTypedBTreePage usable pageCount))
    (overflowChains : List (BoundedOverflowChain usable pageCount)) :
    List (Storage.PageWrite usable.val pageCount) :=
  btreePages.map NumberedTypedBTreePage.toPageWrite ++
    overflowChains.flatMap BoundedOverflowChain.toPageWrites

/-- A set of writes produced only from verified typed B-tree pages and verified
overflow chains. Distinct pager ids prevent later writes from silently
overwriting an earlier page in the same batch. -/
structure VerifiedPageSet (usable : UsablePageSize) (pageCount : Nat) where
  btreePages : List (NumberedTypedBTreePage usable pageCount)
  overflowChains : List (BoundedOverflowChain usable pageCount)
  pageIdsNodup :
    (collectVerifiedPageWrites btreePages overflowChains).map
      (fun write => write.pageId) |>.Nodup
  deriving DecidableEq

def VerifiedPageSet.writes {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedPageSet usable pageCount) :
    List (Storage.PageWrite usable.val pageCount) :=
  collectVerifiedPageWrites pages.btreePages pages.overflowChains

theorem VerifiedPageSet.write_page_ids_nodup
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedPageSet usable pageCount) :
    (pages.writes.map (fun write => write.pageId)).Nodup :=
  pages.pageIdsNodup

/-- The rollback-journal old-or-new theorem instantiated with writes emitted by
the verified physical page layer. -/
theorem VerifiedPageSet.rollbackCommit_crash_atomic
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedPageSet usable pageCount)
    (old : Storage.Disk usable.val pageCount) (phase : Storage.CommitPhase)
    (recoveredMain : Storage.Disk usable.val pageCount)
    (recoveredJournal : Option (Storage.Disk usable.val pageCount))
    (outcome : Storage.JournaledCrashOutcome
      (Storage.rollbackCommitState old pages.writes phase)
      recoveredMain recoveredJournal) :
    Storage.recoverWithJournal recoveredMain recoveredJournal = old ∨
      Storage.recoverWithJournal recoveredMain recoveredJournal =
        Storage.applyWrites old pages.writes := by
  exact Storage.rollbackCommit_crash_atomic old pages.writes phase
    recoveredMain recoveredJournal outcome

/-- Decode SQLite's special page-size field: the value one denotes 65536. -/
def HeaderPrefix.pageSize (header : HeaderPrefix) : Nat :=
  if header.pageSizeField.val = 1 then 65536 else header.pageSizeField.val

def ValidSQLitePageSize (pageSize : Nat) : Prop :=
  pageSize ∈ [512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]

instance (pageSize : Nat) : Decidable (ValidSQLitePageSize pageSize) := by
  unfold ValidSQLitePageSize
  infer_instance

/-- Semantic constraints needed to connect the 100-byte database header to a
fixed-size pager configuration. -/
def DatabaseHeader.WellFormedFor (usable : UsablePageSize) (pageCount : Nat)
    (header : DatabaseHeader) : Prop :=
  ValidSQLitePageSize header.headerPrefix.pageSize ∧
  header.headerPrefix.pageSize =
    usable.val + header.headerPrefix.reservedSpace.toNat ∧
  header.databaseSizePages.val = pageCount ∧
  0 < pageCount ∧
  (header.headerPrefix.writeVersion = 1 ∨ header.headerPrefix.writeVersion = 2) ∧
  (header.headerPrefix.readVersion = 1 ∨ header.headerPrefix.readVersion = 2) ∧
  1 ≤ header.schemaFormat.val ∧ header.schemaFormat.val ≤ 4 ∧
  1 ≤ header.textEncoding.val ∧ header.textEncoding.val ≤ 3 ∧
  header.headerPrefix.reservedSpace = 0

instance (usable : UsablePageSize) (pageCount : Nat) (header : DatabaseHeader) :
    Decidable (header.WellFormedFor usable pageCount) := by
  unfold DatabaseHeader.WellFormedFor
  infer_instance

structure ValidDatabaseHeader (usable : UsablePageSize) (pageCount : Nat) where
  header : DatabaseHeader
  wellFormed : header.WellFormedFor usable pageCount
  deriving DecidableEq

def decodeValidDatabaseHeader (usable : UsablePageSize) (pageCount : Nat)
    (input : List UInt8) :
    Option (ValidDatabaseHeader usable pageCount × List UInt8) := do
  let (header, suffix) ← decodeDatabaseHeader input
  if valid : header.WellFormedFor usable pageCount then
    some (⟨header, valid⟩, suffix)
  else
    none

theorem decodeValidDatabaseHeader_encode {usable : UsablePageSize}
    {pageCount : Nat} (header : ValidDatabaseHeader usable pageCount)
    (suffix : List UInt8) :
    decodeValidDatabaseHeader usable pageCount
      (encodeDatabaseHeader header.header ++ suffix) = some (header, suffix) := by
  unfold decodeValidDatabaseHeader
  rw [decodeDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos header.wellFormed]

structure DatabaseFirstPagePrefix (usable : UsablePageSize) (pageCount : Nat) where
  databaseHeader : ValidDatabaseHeader usable pageCount
  btreePrefix : BTreePagePrefix usable.val
  deriving DecidableEq

def DatabaseFirstPagePrefix.encode {usable : UsablePageSize} {pageCount : Nat}
    (pagePrefix : DatabaseFirstPagePrefix usable pageCount) : List UInt8 :=
  encodeDatabaseHeader pagePrefix.databaseHeader.header ++ pagePrefix.btreePrefix.encode

def decodeDatabaseFirstPagePrefix (usable : UsablePageSize) (pageCount : Nat)
    (input : List UInt8) :
    Option (DatabaseFirstPagePrefix usable pageCount × List UInt8) := do
  let (databaseHeader, afterHeader) ←
    decodeValidDatabaseHeader usable pageCount input
  let (btreePrefix, suffix) ← decodeBTreePagePrefix usable.val afterHeader
  some (⟨databaseHeader, btreePrefix⟩, suffix)

theorem decodeDatabaseFirstPagePrefix_encode {usable : UsablePageSize}
    {pageCount : Nat} (pagePrefix : DatabaseFirstPagePrefix usable pageCount)
    (suffix : List UInt8) :
    decodeDatabaseFirstPagePrefix usable pageCount (pagePrefix.encode ++ suffix) =
      some (pagePrefix, suffix) := by
  unfold DatabaseFirstPagePrefix.encode decodeDatabaseFirstPagePrefix
  rw [List.append_assoc, decodeValidDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeBTreePagePrefix_encode]

theorem DatabaseFirstPagePrefix.encode_length {usable : UsablePageSize}
    {pageCount : Nat} (pagePrefix : DatabaseFirstPagePrefix usable pageCount) :
    pagePrefix.encode.length = 100 + pagePrefix.btreePrefix.encode.length := by
  simp [DatabaseFirstPagePrefix.encode, encodeDatabaseHeader_length]

/-- SQLite page one: the database header occupies bytes 0–99 and the B-tree
page prefix begins at byte 100. -/
structure DatabaseFirstPage (usable : UsablePageSize) (pageCount : Nat) where
  databaseHeader : DatabaseHeader
  headerWellFormed : databaseHeader.WellFormedFor usable pageCount
  layout : BoundedTypedBTreePageLayout usable pageCount
  cellsAfterFirstPrefix : ∀ cell ∈ layout.layout.generic.cells,
    100 + layout.layout.generic.pagePrefix.encode.length ≤ cell.offset.val
  deriving DecidableEq

def DatabaseFirstPage.byteAt {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) (byteOffset : Nat) : UInt8 :=
  match (encodeDatabaseHeader page.databaseHeader)[byteOffset]? with
  | some byte => byte
  | none =>
    match page.layout.layout.generic.pagePrefix.encode[byteOffset - 100]? with
    | some byte => byte
    | none => (cellByteAt? page.layout.layout.generic.cells byteOffset).getD 0

def DatabaseFirstPage.encodePage {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) : Storage.Page usable.val := {
  bytes := Array.ofFn (fun offset : Fin usable.val => page.byteAt offset.val)
  sizeInvariant := by simp }

theorem DatabaseFirstPage.encodePage_size
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) :
    page.encodePage.bytes.size = usable.val :=
  page.encodePage.sizeInvariant

theorem DatabaseFirstPage.byteAt_header
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) (byteOffset : Nat)
    (withinHeader : byteOffset < 100) :
    page.byteAt byteOffset = (encodeDatabaseHeader page.databaseHeader).get
      ⟨byteOffset, by simpa [encodeDatabaseHeader_length] using withinHeader⟩ := by
  unfold DatabaseFirstPage.byteAt
  simp [getElem?_def, encodeDatabaseHeader_length, withinHeader]

theorem DatabaseFirstPage.encodePage_take_header
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) :
    page.encodePage.bytes.toList.take 100 =
      encodeDatabaseHeader page.databaseHeader := by
  apply List.ext_getElem
  · simp [encodeDatabaseHeader_length, page.encodePage.sizeInvariant]
    have := usable.atLeastMinimum
    omega
  · intro byteOffset leftBound rightBound
    have withinHeader : byteOffset < 100 := by
      simpa [encodeDatabaseHeader_length] using rightBound
    simpa [DatabaseFirstPage.encodePage] using
      page.byteAt_header byteOffset withinHeader

theorem DatabaseFirstPage.byteAt_btree_prefix
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) (prefixOffset : Nat)
    (withinPrefix : prefixOffset < page.layout.layout.generic.pagePrefix.encode.length) :
    page.byteAt (100 + prefixOffset) =
      page.layout.layout.generic.pagePrefix.encode.get ⟨prefixOffset, withinPrefix⟩ := by
  have afterHeader : ¬100 + prefixOffset < 100 := by omega
  have relativeOffset : 100 + prefixOffset - 100 = prefixOffset := by omega
  unfold DatabaseFirstPage.byteAt
  simp [getElem?_def, encodeDatabaseHeader_length, afterHeader,
    relativeOffset, withinPrefix]

def DatabaseFirstPage.toPageWrite
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) :
    Storage.PageWrite usable.val pageCount := {
  pageId := ⟨0, page.headerWellFormed.2.2.2.1⟩
  page := page.encodePage }

theorem DatabaseFirstPage.toPageWrite_pageId
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) : page.toPageWrite.pageId.val = 0 :=
  rfl

end FileFormat

end SQLeanite
