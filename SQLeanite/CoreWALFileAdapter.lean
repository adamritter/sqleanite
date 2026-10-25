import SQLeanite.CoreWAL
import SQLeanite.CorePageCodec
import SQLeanite.GroupCommit
import SQLeanite.SQLite.WALRead

/-!
# WAL file adapter for arbitrary Core schemas

Mirrors `LegacyWALFileAdapter` over `Core.Database` instead of the fixed
three-column table, using the schema-agnostic recovery in `CoreWAL`.

Atomic rename and filesystem sync remain explicit obligations of this IO
adapter and are part of the executable trusted computing base; nothing here is
verified beyond the pure WAL protocol it drives.
-/

namespace SQLeanite
namespace CoreWALFileAdapter

structure Paths where
  main : System.FilePath
  wal : System.FilePath

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
private def committedHeader (paths : Paths) : IO FileFormat.DatabaseHeader := do
  let main ← IO.FS.readBinFile paths.main
  let first ← if ← paths.wal.pathExists then do
      let bytes ← IO.FS.readBinFile paths.wal
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
  let some (header, _) := FileFormat.decodeDatabaseHeader first |
    throw (IO.userError "invalid database application metadata")
  if let some message := SQLite.HeaderVersion.readError? header then
    throw (IO.userError message)
  return header

/-- Admission uses the committed snapshot header. The pager may already have
opened an existing WAL before B-tree header validation, so a superseded main
header cannot overrule the latest committed page one. -/
def requireWritableFormat (paths : Paths) : IO Unit := do
  if let some message := SQLite.HeaderVersion.writeError? (← committedHeader paths) then
    throw (IO.userError message)

private def writeMetadata (paths : Paths) : IO CoreMultiFreelist.HeaderMetadata := do
  requireWritableFormat paths
  let header ← committedHeader paths
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

private def readMain (paths : Paths) : IO Core.Database :=
  CoreFileAdapter.reopen { main := paths.main, journal := paths.main.toString ++ "-journal" }

private def readWAL (paths : Paths) : IO Core.Database := do
  let contents ← IO.FS.readBinFile paths.wal
  let recovered ← match SQLite.WALRead.recover contents.data.toList with
    | .ok snapshot => pure snapshot
    | .error message => throw (IO.userError message)
  let some snapshot := recovered | readMain paths
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
  unless header.headerPrefix.pageSize = snapshot.pageSize && header.textEncoding.val = 1 do
    throw (IO.userError "SQLite WAL/header geometry or text encoding mismatch")
  let source : CoreDecode.IOPageSource := {
    usable
    pageCount := snapshot.pageCount
    readPage := fun pageNumber => pure ((read pageNumber).map (List.take usable.val)) }
  match ← CoreDecode.decodeFromIOPageSource source with
  | some database => return database
  | none => throw (IO.userError "invalid recovered SQLite WAL database")

/-- A WAL rename or checkpoint deletion can occur between `pathExists` and
`readBinFile`. Bounded retry keeps the live reader total while allowing that
expected race. -/
private def reopenRetry (paths : Paths) : Nat → IO Core.Database
  | 0 => readMain paths
  | attempts + 1 => do
      if ← paths.wal.pathExists then
        try readWAL paths
        catch error =>
          if ← paths.wal.pathExists then throw error
          else reopenRetry paths attempts
      else readMain paths

def reopen (paths : Paths) : IO Core.Database :=
  reopenRetry paths 4

def create (syncOps : SyncOps) (paths : Paths)
    (database : Core.Database) : IO Unit := do
  let image ← encodeImage database
  if ← paths.wal.pathExists then IO.FS.removeFile paths.wal
  if ← paths.temporaryWAL.pathExists then IO.FS.removeFile paths.temporaryWAL
  IO.FS.writeBinFile paths.main (bytes image.fileBytes)
  syncOps.syncFile paths.main
  syncOps.syncDeletion paths.main

/-- Publish a complete, self-contained WAL through a temporary file. The pure
WAL writes every target page, so reopening never depends on uncheckpointed
main-file contents. -/
def commit (syncOps : SyncOps) (paths : Paths) (database : Core.Database) :
    IO Core.Database := do
  let metadata ← writeMetadata paths
  let image ← encodeImage database metadata
  if fits : CoreWAL.imagePageCount image < 2 ^ 32 then
    let wal := CoreWAL.forCoreImage header image fits
    if ← paths.temporaryWAL.pathExists then IO.FS.removeFile paths.temporaryWAL
    IO.FS.writeBinFile paths.temporaryWAL (bytes wal.encode)
    syncOps.syncFile paths.temporaryWAL
    IO.FS.rename paths.temporaryWAL paths.wal
    syncOps.syncDeletion paths.main
    reopen paths
  else throw (IO.userError "general MVP database exceeds the WAL page count")

/-- Publish a chronological batch of already-computed transaction states with
one physical WAL sync. The proved group-commit model shows that the newest
full-image state is exactly the visible result of sequentially committing the
whole batch. An empty batch is a read-only reopen. -/
def commitBatch (syncOps : SyncOps) (paths : Paths)
    (databases : List Core.Database) : IO Core.Database := do
  match GroupCommit.newest? databases with
  | none => reopen paths
  | some newest => commit syncOps paths newest

/-- Copy the latest committed WAL image to the main database, sync it, and only
then delete the WAL. A crash before deletion still has the complete WAL; a
reader after deletion sees the synced main file. -/
def checkpoint (syncOps : SyncOps) (paths : Paths) : IO Core.Database := do
  let database ← reopen paths
  let metadata ← writeMetadata paths
  let image ← encodeImage database metadata
  IO.FS.writeBinFile paths.main (bytes image.fileBytes)
  syncOps.syncFile paths.main
  if ← paths.wal.pathExists then IO.FS.removeFile paths.wal
  syncOps.syncDeletion paths.main
  readMain paths

end CoreWALFileAdapter
end SQLeanite
