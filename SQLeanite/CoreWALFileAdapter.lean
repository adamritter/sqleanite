import SQLeanite.CoreCatalogImage
import SQLeanite.CoreFileAdapter.PreadPageSource
import SQLeanite.CorePageCodec.PageSourceRepresentsEncodeBulkIn
import SQLeanite.CoreWAL
import SQLeanite.GroupCommit
import SQLeanite.SQLite.WALShared

/-!
# WAL file adapter for arbitrary Core schemas

Mirrors `LegacyWALFileAdapter` over `Core.Database` instead of the fixed
three-column table, using the schema-agnostic recovery in `CoreWAL`.

Shared byte-range locks, coherent positional writes and filesystem sync are
explicit executable obligations. Pure codec theorems do not prove this IO
adapter or its live shared-index publication protocol.
-/

namespace SQLeanite
namespace CoreWALFileAdapter

abbrev Paths := SQLite.WALShared.Paths
abbrev Session := SQLite.WALShared.Session

abbrev SyncOps := PhysicalFileAdapter.SyncOps

def Paths.temporaryWAL (paths : Paths) : System.FilePath :=
  paths.wal.toString ++ ".tmp"

private def bytes (values : List UInt8) : ByteArray :=
  ByteArray.mk values.toArray

private def encodeImage (database : Core.Database)
    (metadata : CoreMultiFreelist.HeaderMetadata := {}) : IO CoreFile.Image := do
  let image ← match CorePageCodec.encodeChecked database with
    | some image => pure image
    | none => throw (IO.userError "general MVP database exceeds the physical subset")
  let some layout := CoreMultiFreelist.ofImageTotal? image image.pageCount |
    throw (IO.userError "WAL image has no bounded metadata layout")
  return ({ layout with metadata } : CoreMultiFreelist.Layout).paddedImage

/-- Application metadata comes from the committed WAL snapshot when page one
has an overlay, and otherwise from the main database header. -/
private def committedHeader (session : Session) : IO FileFormat.DatabaseHeader := do
  let paths := session.paths
  let main ← IO.FS.readBinFile paths.main
  let visible ← session.visibleWAL
  let first ← if !visible.isEmpty then do
      let bytes := ByteArray.mk visible
      let recovered ← match SQLite.WALRead.recover bytes.toList with
        | .ok snapshot => pure snapshot
        | .error message => throw (IO.userError message)
      match recovered with
      | none => pure (main.extract 0 100).toList
      | some snapshot =>
          let base := fun page => if page == 1 then
              some (main.extract 0 snapshot.pageSize).toList else none
          match snapshot.readPage base 1 with
          | some bytes => pure bytes
          | none => throw (IO.userError "WAL snapshot has no metadata page")
    else pure (main.extract 0 100).toList
  let some header := CoreFileAdapter.headerOrEmpty first main.size |
    throw (IO.userError "invalid database application metadata")
  if let some message := SQLite.HeaderVersion.readError? header then
    throw (IO.userError message)
  return header

/-- Admission uses the committed snapshot header. The pager may already have
opened an existing WAL before B-tree header validation, so a superseded main
header cannot overrule the latest committed page one. -/
def requireWritableFormat (session : Session) : IO Unit := do
  let header ← committedHeader session
  if let some message := SQLite.HeaderVersion.writeError? header then
    throw (IO.userError message)
  unless CoreFileAdapter.utf8TextEncoding header.textEncoding.val do
    throw (IO.userError "unsupported UTF-16 database writes")

private def writeMetadata (session : Session) : IO CoreMultiFreelist.HeaderMetadata := do
  requireWritableFormat session
  let header ← committedHeader session
  unless CoreFileAdapter.utf8TextEncoding header.textEncoding.val do
    throw (IO.userError "unsupported UTF-16 database writes")
  unless header.headerPrefix.reservedSpace = 0 do
    throw (IO.userError "unsupported reserved-byte database writes")
  return CoreMultiFreelist.HeaderMetadata.fromHeader header

def header : PhysicalWAL.Header := {
  checkpointSequence := ⟨0, by decide⟩
  saltFirst := ⟨0x4c53514c, by decide⟩
  saltSecond := ⟨0x57414c31, by decide⟩ }

def emptyImage : PhysicalWALRecovery.Image := {
  pageCount := 0
  read := fun _ => Storage.Page.zero PhysicalCodec.pageSize }

private def readMain (paths : Paths) (origins : Option (IO.Ref (List SQLite.StoredText)) := none) :
    IO (Core.Database × CoreMultiFreelist.HeaderMetadata) :=
  CoreFileAdapter.reopenWithMetadata { main := paths.main, journal := paths.main.toString ++ "-journal" } origins

private def readWAL (session : Session) (origins : Option (IO.Ref (List SQLite.StoredText)) := none) :
    IO (Core.Database × CoreMultiFreelist.HeaderMetadata) := do
  let paths := session.paths
  let contents := ByteArray.mk (← session.visibleWAL)
  let recovered ← match SQLite.WALRead.recover contents.data.toList with
    | .ok snapshot => pure snapshot
    | .error message => throw (IO.userError message)
  let some snapshot := recovered | readMain paths origins
  let main ← IO.FS.readBinFile paths.main
  let base := SQLite.DatabaseSize.pageBytes main snapshot.pageSize
  let read := snapshot.readPage base
  let some firstPage := read 1 |
    throw (IO.userError "SQLite WAL snapshot has no database header")
  let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
    throw (IO.userError "invalid database header in SQLite WAL snapshot")
  if let some message := SQLite.HeaderVersion.readError? header then
    throw (IO.userError message)
  let some usable := CoreFileAdapter.headerUsablePageSize? header |
    throw (IO.userError "unsupported page geometry in SQLite WAL snapshot")
  unless header.headerPrefix.pageSize = snapshot.pageSize && SQLite.TextEncoding.supported header.textEncoding.val do
    throw (IO.userError "SQLite WAL/header geometry or text encoding mismatch")
  let source : CoreDecode.IOPageSource := {
    usable
    textEncoding := header.textEncoding.val
    observeRow := if header.textEncoding.val == 2 || header.textEncoding.val == 3 then
      origins.map fun reference => fun schema row fields =>
        reference.modify (fun previous => CoreTextEncoding.origins header.textEncoding.val schema row fields ++ previous)
      else none
    pageCount := snapshot.pageCount
    readPage := fun pageNumber => pure ((read pageNumber).map (List.take usable.val)) }
  match ← CoreDecode.decodeFromIOPageSource source with
  | some database => return (database, CoreMultiFreelist.HeaderMetadata.fromHeader header)
  | none => throw (IO.userError "invalid recovered SQLite WAL database")

/-- The session owns a stable committed prefix while its pages are decoded. -/
def reopenInSession (session : Session) (origins : Option (IO.Ref (List SQLite.StoredText)) := none) :
    IO (Core.Database × CoreMultiFreelist.HeaderMetadata) :=
  readWAL session origins

def reopenWithMetadata (paths : Paths) (origins : Option (IO.Ref (List SQLite.StoredText)) := none) :
    IO (Core.Database × CoreMultiFreelist.HeaderMetadata) :=
  SQLite.WALShared.withSession paths false (fun session => reopenInSession session origins)

def reopen (paths : Paths) : IO Core.Database := do
  return (← reopenWithMetadata paths).1

private def walBytes (image : CoreFile.Image) : Array UInt8 :=
  image.fileBytes.toArray |>.set! 18 2 |>.set! 19 2

def create (syncOps : SyncOps) (paths : Paths)
    (database : Core.Database) : IO Unit := do
  let image ← encodeImage database
  WALVFS.withRange paths.main 1073741824 512 true true do
    if ← paths.wal.pathExists then IO.FS.removeFile paths.wal
    if ← paths.temporaryWAL.pathExists then IO.FS.removeFile paths.temporaryWAL
    let data := if database.tables.isEmpty then
        let prepared : SQLite.WALIndex.Prepared := ⟨walBytes image, #[]⟩
        (prepared.write 40 #[0, 0, 0, 0]).bytes
      else walBytes image
    IO.FS.writeBinFile paths.main (ByteArray.mk data)
    syncOps.syncFile paths.main
    syncOps.syncDeletion paths.main

/-- Compare the physical catalog, including root-page locations. Rebuilding
an image can relocate a root even when the SQL schema has not changed; an idle
SQLite connection must reload its cached root numbers in that case too. -/
private def schemaSource (session : Session) : IO CoreDecode.IOPageSource := do
  let header ← committedHeader session
  let main ← IO.FS.readBinFile session.paths.main
  let snapshot ← match SQLite.WALRead.recover (← session.visibleWAL).toList with
    | .ok snapshot => pure snapshot
    | .error message => throw (IO.userError message)
  let pageSize := header.headerPrefix.pageSize
  let base := SQLite.DatabaseSize.pageBytes main pageSize
  let read := match snapshot with
    | some snapshot => snapshot.readPage base
    | none => base
  let some usable := CoreFileAdapter.headerUsablePageSize? header |
    throw (IO.userError "unsupported WAL catalog geometry")
  let source : CoreDecode.IOPageSource := {
    usable
    textEncoding := header.textEncoding.val
    pageCount := snapshot.map (·.pageCount) |>.getD (main.size / pageSize)
    readPage := fun page => pure ((read page).map (List.take usable.val)) }
  return source

private def storedCatalog (session : Session) : IO (List CoreDecode.CatalogEntry) := do
  let source ← schemaSource session
  if source.pageCount == 0 then return []
  let some catalog ← CoreDecode.catalogIOFrom source |
    throw (IO.userError "invalid WAL catalog")
  return catalog

def schemaRows (session : Session) : IO (List Core.Row) := do
  let source ← schemaSource session
  if source.pageCount == 0 then return []
  let some rows ← CoreSchemaRead.rows source |
    throw (IO.userError "invalid WAL schema records")
  return rows

/-- Retain existing index SQL only after parsing and checking its current
name, owner, indexed column and uniqueness. Physical root relocation does
not rewrite schema spelling or attach value-dependent private certificates. -/
private def retainedIndexSQL (catalog : List CoreDecode.CatalogEntry)
    (table : Core.Table) (index : Core.Index) : String :=
  CoreCatalogImage.retainedSQL catalog table index

def textEncoding (session : Session) : IO Nat :=
  return (← committedHeader session).textEncoding.val

def schemaVersion (session : Session) : IO Nat :=
  return (← committedHeader session).schemaCookie.val

private def publicationPages (session : Session) (usable : FileFormat.UsablePageSize)
    (pages : Array (Array UInt8)) (schemaVersion : Option Nat := none) : IO (Array (Array UInt8)) := do
  let oldHeader ← committedHeader session
  let oldCatalog ← storedCatalog session
  let source : CoreDecode.IOPageSource := {
    usable
    pageCount := pages.size
    readPage := fun page => pure ((pages[page - 1]?).map Array.toList) }
  let some newCatalog ← CoreDecode.catalogIOFrom source |
    throw (IO.userError "invalid encoded WAL catalog")
  let schemaCookie := (schemaVersion.getD (oldHeader.schemaCookie.val +
    if oldCatalog = newCatalog then 0 else 1)) % 2^32
  let counter := (oldHeader.headerPrefix.changeCounter.val + 1) % 2^32
  let some first := pages[0]? | throw (IO.userError "empty encoded WAL image")
  let prepared : SQLite.WALIndex.Prepared := ⟨first, #[]⟩
  let number := SQLite.WALIndex.numberBytes true 4
  return pages.set! 0 (prepared.write 24 (number counter) |>.write 40 (number schemaCookie)
    |>.write 92 (number counter)).bytes

/-- The writer lock spans read, SQL execution and publication, preventing a
concurrent SQLite commit from being overwritten by a stale Lean snapshot. -/
def commitInSession (syncOps : SyncOps) (session : Session) (database : Core.Database)
    (updatedMetadata : Option CoreMultiFreelist.HeaderMetadata := none)
    (indexDeclarations : List CoreDecode.CatalogEntry := [])
    (objects : Option CoreCatalogData.Objects := none) :
    IO Core.Database := do
  let metadata ← writeMetadata session
  let oldHeader ← committedHeader session
  let some usable := CoreFileAdapter.headerUsablePageSize? oldHeader |
    throw (IO.userError "unsupported WAL write geometry")
  let metadata := updatedMetadata.getD metadata
  let catalog := indexDeclarations ++ (← storedCatalog session)
  let baseHeader : FileFormat.DatabaseHeader := {
    CoreFile.databaseHeader ⟨0, by decide⟩ with
    applicationId := metadata.applicationId
    userVersion := metadata.userVersion }
  let some pages := CoreSizedPageCodec.encode? usable database baseHeader
      (retainedIndexSQL catalog) ((objects.map CoreCatalogImage.viewEntries).getD [])
      ((objects.map (·.identities)).getD []) |
    throw (IO.userError "cannot encode database at its existing page size")
  if let some objects := objects then
    let source : CoreDecode.IOPageSource := {
      usable
      pageCount := pages.size
      readPage := fun page => pure ((pages[page - 1]?).map Array.toList) }
    let some records ← CoreSchemaRead.rows source | throw (IO.userError "invalid encoded object catalog")
    unless CoreCatalogImage.objectRecordsMatch objects records do
      throw (IO.userError "WAL schema object identity validation failed")
  let pages ← publicationPages session usable pages (objects.map (·.schemaVersion))
  -- SQLite needs a main-file page before it will discover the WAL. The first
  -- commit holds the exclusive database lock and publishes an empty base first;
  -- reads and rolled-back transactions never reach this initialization.
  if (← session.paths.main.metadata).byteSize.toNat ≤ 1 && (← session.visibleWAL).isEmpty then
    unless session.exclusiveDatabase do throw (IO.userError "empty WAL database requires exclusive initialization")
    let empty ← encodeImage Core.Database.empty
    let prepared : SQLite.WALIndex.Prepared := ⟨walBytes empty, #[]⟩
    IO.FS.writeBinFile session.paths.main (ByteArray.mk (prepared.write 40 #[0,0,0,0]).bytes)
    syncOps.syncFile session.paths.main
  session.append syncOps.syncFile header pages
  syncOps.syncDeletion session.paths.main
  return (← reopenInSession session).1

def commit (syncOps : SyncOps) (paths : Paths) (database : Core.Database)
    (updatedMetadata : Option CoreMultiFreelist.HeaderMetadata := none) :
    IO Core.Database :=
  SQLite.WALShared.withSession paths true fun session =>
    commitInSession syncOps session database updatedMetadata

/-- One physical WAL sync publishes the newest full-image state. -/
def commitBatch (syncOps : SyncOps) (paths : Paths)
    (databases : List Core.Database) : IO Core.Database := do
  match GroupCommit.newest? databases with
  | none => reopen paths
  | some newest => commit syncOps paths newest

/-- Backfill exact committed bytes under all reader locks. Keep the WAL and
shared index in place for idle connections; SQLite may subsequently reset it.
A busy reader causes an error before any main-file mutation. -/
def checkpoint (syncOps : SyncOps) (paths : Paths) : IO Core.Database :=
  SQLite.WALShared.withSession paths true fun session =>
    WALVFS.withRange paths.shm 121 2 true false do
     WALVFS.withRange paths.shm 123 5 true false do
      requireWritableFormat session
      let main ← IO.FS.readBinFile paths.main
      let recovered ← match SQLite.WALRead.recover (← session.visibleWAL).toList with
        | .ok snapshot => pure snapshot
        | .error message => throw (IO.userError message)
      if let some snapshot := recovered then
        let base := SQLite.DatabaseSize.pageBytes main snapshot.pageSize
        let mut transfers : Array SyscallVFS.PageTransfer := #[]
        for i in [:snapshot.pageCount] do
          let some page := snapshot.readPage base (i + 1) |
            throw (IO.userError "WAL checkpoint is missing a database page")
          transfers := transfers.push {
            bytes := bytes page
            offset := (i * snapshot.pageSize).toUInt64 }
        -- Never truncate the main file: a crash must retain untouched pages
        -- that a partial-page SQLite WAL does not contain. The committed
        -- database-size header hides any old tail after a shrinking commit.
        SyscallVFS.pwritePages paths.main.toString transfers
        syncOps.syncFile paths.main
        session.markBackfilled
      return (← readMain paths).1

end CoreWALFileAdapter
end SQLeanite
