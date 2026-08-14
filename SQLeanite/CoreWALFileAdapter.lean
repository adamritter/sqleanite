import SQLeanite.CoreWAL
import SQLeanite.CorePageCodec
import SQLeanite.GroupCommit

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

private def encodeImage (database : Core.Database) : IO CoreFile.Image :=
  match CorePageCodec.encodeChecked database with
  | some image => return image
  | none => throw (IO.userError "general MVP database exceeds the physical subset")

def header : PhysicalWAL.Header := {
  checkpointSequence := ⟨0, by decide⟩
  saltFirst := ⟨0x4c53514c, by decide⟩
  saltSecond := ⟨0x57414c31, by decide⟩ }

def emptyImage : PhysicalWALRecovery.Image := {
  pageCount := 0
  read := fun _ => Storage.Page.zero PhysicalCodec.pageSize }

private def decodeImageBytes (contents : List UInt8) (label : String) :
    IO Core.Database :=
  match CoreDecode.decode contents with
  | some database => return database
  | none => throw (IO.userError s!"invalid general MVP SQLite image: {label}")

private def readMain (paths : Paths) : IO Core.Database := do
  let contents ← IO.FS.readBinFile paths.main
  decodeImageBytes contents.data.toList paths.main.toString

private def readWAL (paths : Paths) : IO Core.Database := do
  let contents ← IO.FS.readBinFile paths.wal
  let wal ← match PhysicalWAL.decode contents.data.toList with
    | some wal => pure wal
    | none => throw (IO.userError s!"invalid physical SQLite WAL: {paths.wal}")
  let recovered ← match PhysicalWALRecovery.recover emptyImage wal with
    | some recovered => pure recovered
    | none => throw (IO.userError "physical SQLite WAL contains no commit frame")
  let pageBytes := (List.range recovered.pageCount).flatMap fun pageId =>
    (recovered.read pageId).bytes.toList
  decodeImageBytes pageBytes "physical SQLite WAL"

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
  let image ← encodeImage database
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
  let image ← encodeImage database
  IO.FS.writeBinFile paths.main (bytes image.fileBytes)
  syncOps.syncFile paths.main
  if ← paths.wal.pathExists then IO.FS.removeFile paths.wal
  syncOps.syncDeletion paths.main
  readMain paths

end CoreWALFileAdapter
end SQLeanite
