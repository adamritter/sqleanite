import SQLeanite.CoreSizedPageCodec
import SQLeanite.CoreMultiFreelist
import SQLeanite.CorePageSource

/-! Catalog-preserving images carry separate executable checks for their
catalog, table records, physical indexes and header. The retained declaration
is accepted only when its parsed index identity matches the current index. -/
namespace SQLeanite.CoreCatalogImage

open FileFormat

def retainedSQL (catalog : List CoreDecode.CatalogEntry)
    (table : Core.Table) (index : Core.Index) : String :=
  let retained := catalog.findSome? fun entry => do
    if entry.kind != "index" || entry.name != index.name || entry.table != table.schema.name then none
    else do
      let sql ← entry.sql
      let spec ← (CanonicalIndexSQL.parse sql).orElse fun _ => CoreSchemaSQL.indexSpec sql
      let column ← table.schema.columns[index.column]?
      if spec.name.toLower = index.name.toLower && spec.table.toLower = table.schema.name.toLower &&
          spec.column.toLower = column.name.toLower && spec.unique = index.unique then some sql else none
  retained.getD (CoreFile.indexSQL table index)

def storage (image : CoreFile.Image) : GrowableStorage.Image PhysicalCodec.pageSize :=
  let pages := image.pages.toArray
  { pageCount := pages.size, read := fun page =>
      (pages[page]?).map CoreFile.Page.storage |>.getD (Storage.Page.zero PhysicalCodec.pageSize) }

def page? (bytes : Array UInt8) : Option CoreFile.Page :=
  if size : bytes.toList.length = PhysicalCodec.pageSize then some ⟨bytes.toList,size⟩ else none

def withHeader (image : CoreFile.Image) (header : DatabaseHeader) : Option CoreFile.Image := do
  let first ← image.pages.head?
  let replacement ← page? ((encodeDatabaseHeader header).toArray ++ (first.bytes.drop 100).toArray)
  return { image with pages := replacement :: image.pages.tail }

def encode (oldCount : Nat) (database : Core.Database) (header : DatabaseHeader)
    (metadata : CoreMultiFreelist.HeaderMetadata) (catalog : List CoreDecode.CatalogEntry)
    (declarations : List CoreDecode.CatalogEntry := []) :
    Option CoreFile.Image := do
  let base : DatabaseHeader := { CoreFile.databaseHeader ⟨0, by decide⟩ with
    applicationId := metadata.applicationId, userVersion := metadata.userVersion }
  let pages ← CoreSizedPageCodec.encode? PhysicalCodec.usablePageSize database base (retainedSQL (declarations ++ catalog))
  let pages ← pages.toList.mapM page?
  let image : CoreFile.Image := { database, pages }
  let layout ← CoreMultiFreelist.ofImageTotal? image (max oldCount image.pageCount)
  let layout := { layout with metadata }
  let padded := layout.paddedImage
  let counter : U32Value := ⟨(header.headerPrefix.changeCounter.val + 1) % 2^32, Nat.mod_lt _ (by decide)⟩
  let first ← padded.pages.head?
  let currentCatalog ← CoreDecode.decodeCatalogForOpen first.bytes
  let cookie : U32Value := ⟨(header.schemaCookie.val + if currentCatalog == catalog then 0 else 1) % 2^32,
    Nat.mod_lt _ (by decide)⟩
  let revised := { layout.databaseHeader with
    headerPrefix := { layout.databaseHeader.headerPrefix with
      readVersion := 1, writeVersion := 1, changeCounter := counter }
    versionValidFor := counter
    schemaCookie := cookie }
  withHeader padded revised

structure Checked (old : GrowableStorage.Image PhysicalCodec.pageSize) (database : Core.Database) where
  image : CoreFile.Image
  catalog : List CoreDecode.CatalogEntry
  tables : List Core.Table
  rebuilt : Core.Database
  decoded : Core.Database
  header : DatabaseHeader
  suffix : List UInt8
  catalogRead : (CorePageSource.ofStorageImage (storage image)).readPage 1 >>=
    CoreDecode.decodeCatalogForOpen = some catalog
  tablesRead : (catalog.filter (·.kind == "table")).mapM
    (CoreDecode.decodeTableFrom (CorePageSource.ofStorageImage (storage image))) = some tables
  rebuiltEq : Core.Database.rebuild tables = .ok rebuilt
  indexesRead : CoreDecode.applyIndexesForOpen (CorePageSource.ofStorageImage (storage image))
    rebuilt (catalog.filter (·.kind == "index")) = some decoded
  equivalent : decoded.Equiv database
  headerRead : decodeDatabaseHeader (PhysicalJournalRecovery.imageBytes (storage image)) = some (header,suffix)
  pageCount : header.databaseSizePages.val = (storage image).pageCount
  pageSize : header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize
  reserved : header.headerPrefix.reservedSpace = 0
  utf8 : header.textEncoding.val = 1
  grows : old.pageCount ≤ (storage image).pageCount

def check (old : GrowableStorage.Image PhysicalCodec.pageSize) (database : Core.Database)
    (image : CoreFile.Image) : Option (Checked old database) := do
  let source := CorePageSource.ofStorageImage (storage image)
  match catalogRead : source.readPage 1 >>= CoreDecode.decodeCatalogForOpen with
  | none => none
  | some catalog =>
    match tablesRead : (catalog.filter (·.kind == "table")).mapM (CoreDecode.decodeTableFrom source) with
    | none => none
    | some tables =>
      match rebuiltEq : Core.Database.rebuild tables with
      | .error _ => none
      | .ok rebuilt =>
        match indexesRead : CoreDecode.applyIndexesForOpen source rebuilt (catalog.filter (·.kind == "index")) with
        | none => none
        | some decoded =>
          if equivalent : decoded.Equiv database then
            match headerRead : decodeDatabaseHeader (PhysicalJournalRecovery.imageBytes (storage image)) with
            | none => none
            | some (header,suffix) =>
              if valid : header.databaseSizePages.val = (storage image).pageCount ∧
                  header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize ∧
                  header.headerPrefix.reservedSpace = 0 ∧ header.textEncoding.val = 1 ∧
                  old.pageCount ≤ (storage image).pageCount then
                some {
                  image := image
                  catalog := catalog
                  tables := tables
                  rebuilt := rebuilt
                  decoded := decoded
                  header := header
                  suffix := suffix
                  catalogRead := catalogRead
                  tablesRead := tablesRead
                  rebuiltEq := rebuiltEq
                  indexesRead := indexesRead
                  equivalent := equivalent
                  headerRead := headerRead
                  pageCount := valid.1
                  pageSize := valid.2.1
                  reserved := valid.2.2.1
                  utf8 := valid.2.2.2.1
                  grows := valid.2.2.2.2 }
              else none
          else none

def Checked.writes {old database} (checked : Checked old database) :=
  GrowableStorage.deltaWrites old (storage checked.image)

theorem Checked.applied {old database} (checked : Checked old database) :
    (GrowableStorage.applyWrites old checked.writes).Equiv (storage checked.image) :=
  GrowableStorage.apply_deltaWrites_equiv _ _ checked.grows

theorem Checked.components_decode {old database} (checked : Checked old database) :
    CoreDecode.decodeFromPageSource (CorePageSource.ofStorageImage (storage checked.image)) =
      some checked.decoded := by
  unfold CoreDecode.decodeFromPageSource
  rw [← bind_assoc, checked.catalogRead]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [checked.tablesRead]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [checked.rebuiltEq]
  exact checked.indexesRead

theorem Checked.bytes_decode {old database} (checked : Checked old database) :
    CoreDecode.decode (PhysicalJournalRecovery.imageBytes (storage checked.image)) =
      some checked.decoded := by
  unfold CoreDecode.decode
  rw [checked.headerRead]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos checked.pageSize, dif_pos checked.reserved, dif_pos checked.utf8]
  rw [checked.pageCount]
  have fileLength : (PhysicalJournalRecovery.imageBytes (storage checked.image)).length =
      (storage checked.image).pageCount * PhysicalCodec.pageSize := by
    rw [PhysicalJournalRecovery.imageBytes, DiskFormat.encodePages_length]
    rw [PhysicalJournalRecovery.imagePages_length]
    exact Nat.mul_comm _ _
  rw [dif_pos fileLength]
  rw [CorePageSource.pages_imageBytes]
  exact checked.components_decode

theorem Checked.applied_decode {old database} (checked : Checked old database) :
    CoreDecode.decode (PhysicalJournalRecovery.imageBytes
      (GrowableStorage.applyWrites old checked.writes)) = some checked.decoded := by
  rw [PhysicalJournalRecovery.imageBytes_eq_of_equiv checked.applied]
  exact checked.bytes_decode

/-- Recovery retains the original bytes or reaches the independently checked
post-image. The unchanged branch does not assume the old file was generated. -/
theorem Checked.recovery {old database} (checked : Checked old database)
    (phase : GrowableStorage.CommitPhase)
    (main : GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : Option (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState old checked.writes phase) main journal) :
    PhysicalJournalRecovery.recoverBytes main journal = PhysicalJournalRecovery.imageBytes old ∨
    CoreDecode.decode (PhysicalJournalRecovery.recoverBytes main journal) = some checked.decoded := by
  rcases PhysicalJournalRecovery.rollbackCommit_recovery_bytes_atomic old checked.writes
    phase main journal outcome with restored | committed
  · exact .inl restored
  · exact .inr (committed ▸ checked.applied_decode)

end SQLeanite.CoreCatalogImage
