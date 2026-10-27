import SQLeanite.WALVFS
import SQLeanite.SQLite.WALAppend
import SQLeanite.SQLite.HeaderVersion

/-! Linux/SQLite shared-WAL IO boundary. The byte codecs are pure Lean.
The lock lifetime, filesystem coherence and publication ordering below are
explicit executable obligations, not consequences of the pure WAL theorems. -/
namespace SQLeanite.SQLite.WALShared

structure Paths where
  main : System.FilePath
  wal : System.FilePath

def Paths.shm (paths : Paths) : System.FilePath := paths.main.toString ++ "-shm"

structure Session where
  paths : Paths
  nativeBigEndian : Bool
  /-- No other process has this wal-index open. Ignore its stale contents. -/
  firstConnection : Bool
  writable : Bool
  exclusiveDatabase : Bool := false

private def lift (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def writeAt (path : System.FilePath) (offset : Nat) (data : Array UInt8) : IO Unit :=
  SyscallVFS.pwriteBytes path.toString offset.toUInt64 (ByteArray.mk data)

private def indexBytes (paths : Paths) : IO (Array UInt8) := do
  return (← IO.FS.readBinFile paths.shm).data

private def indexHeader (session : Session) : Nat → IO WALIndex.Header
  | 0 => throw (IO.userError "database is locked")
  | attempts + 1 => do
      let input ← SyscallVFS.preadBytes session.paths.shm.toString 0 96
      if let some header := WALIndex.decodeCopies session.nativeBigEndian input.data then
        return header
      IO.sleep 1
      indexHeader session attempts

/-- Two ordered system calls publish the secondary copy before the primary.
Linux coherent page-cache writes and syscall ordering are part of the TCB. -/
def publishHeader (session : Session) (header : WALIndex.Header) : IO Unit := do
  let bytes := header.encode session.nativeBigEndian
  writeAt session.paths.shm 48 bytes
  writeAt session.paths.shm 0 bytes

private def headerOfLog (log : WALAppend.Log) (change : Nat := 0) : WALIndex.Header := {
  change := ⟨change % 2^32, Nat.mod_lt _ (by decide)⟩
  bigEndianChecksum := log.header.bigEndian
  pageSize := log.header.pageSize
  maxFrame := ⟨log.committedFrames % 2^32, Nat.mod_lt _ (by decide)⟩
  databaseSize := ⟨log.pageCount % 2^32, Nat.mod_lt _ (by decide)⟩
  frameChecksum := log.checksum
  saltFirst := log.header.saltFirst
  saltSecond := log.header.saltSecond }

private def rawWAL (paths : Paths) : IO (Array UInt8) := do
  if ← paths.wal.pathExists then return (← IO.FS.readBinFile paths.wal).data
  return #[]

private def emptyHeader : WALIndex.Header := {
  change := ⟨0, by decide⟩, bigEndianChecksum := false, pageSize := 0
  maxFrame := ⟨0, by decide⟩, databaseSize := ⟨0, by decide⟩
  frameChecksum := .zero, saltFirst := ⟨0, by decide⟩, saltSecond := ⟨0, by decide⟩ }

/-- Caller excludes writers, checkpoints, recovery and all active readers.
Never replace or truncate an index that a different connection may have mapped. -/
private def recoverIndex (session : Session) : IO Unit := do
  let log ← lift (WALAppend.read (← rawWAL session.paths))
  let pages := log.map (·.pages) |>.getD #[]
  let prepared ← lift (WALIndex.append session.nativeBigEndian 0 pages #[])
  let prepared := prepared.ensureRegion 0
  for transfer in prepared.writes do
    -- The initial extension is zero-filled by the filesystem. Do not write
    -- SQLite's eight reserved locking bytes at offsets 120 through 127.
    if transfer.offset = 0 then
      writeAt session.paths.shm (prepared.bytes.size - 1) #[0]
    else writeAt session.paths.shm transfer.offset transfer.bytes
  let header := log.map headerOfLog |>.getD emptyHeader
  let number := WALIndex.numberBytes session.nativeBigEndian 4
  writeAt session.paths.shm 96 (number 0 ++ number 0 ++
    number (if header.maxFrame.val = 0 then 4294967295 else header.maxFrame.val) ++
    number 4294967295 ++ number 4294967295 ++ number 4294967295)
  writeAt session.paths.shm 128 (number header.maxFrame.val ++ number 0)
  publishHeader session header

private def initializeWriter (session : Session) : IO Unit := do
  let input ← indexBytes session.paths
  if !session.firstConnection && (WALIndex.decodeCopies session.nativeBigEndian input).isSome then
    return
  WALVFS.withRange session.paths.shm 121 2 true false do
    WALVFS.withRange session.paths.shm 123 5 true false (recoverIndex session)

/-- Entering WAL mode from a rollback-mode main file requires exclusive
database ownership. Page geometry itself never requires a mode conversion.
This only selects locks; SQL admission inspects the committed page one. -/
private def needsExclusiveDatabase (paths : Paths) (writable : Bool) : IO Bool := do
  unless writable do return false
  let canWrite ← try
      IO.FS.withFile paths.main .readWrite (fun _ => pure true)
    catch _ => pure false
  unless canWrite do return false
  let wal ← if ← paths.wal.pathExists then
      try pure (← SyscallVFS.preadBytes paths.wal.toString 0 32).data
      catch _ => pure #[]
    else pure #[]
  if let .ok (some _) := WALRead.decodeHeader wal.toList then
    return false
  let first ← SyscallVFS.preadBytes paths.main.toString 0 100
  let some (header, _) := FileFormat.decodeDatabaseHeader first.toList | return false
  return header.headerPrefix.readVersion != 2 || header.headerPrefix.writeVersion != 2

/-- Short races while another process initializes SHM do not run the user
action twice. Only the lock acquisition is retried, with a finite bound. -/
private def withSharedRetry (path : System.FilePath) (offset length : Nat)
    (action : IO α) : Nat → IO α
  | 0 => throw (IO.userError "database is locked")
  | attempts + 1 => do
      match ← WALVFS.tryRangeLock path.toString offset.toUInt64 length.toUInt64 false false with
      | some descriptor => try action finally WALVFS.releaseRangeLock descriptor
      | none =>
          IO.sleep 1
          withSharedRetry path offset length action attempts

/-- Initialize a stale index under exclusive DMS, release that initialization
session, then open a fresh shared-DMS session. No snapshot crosses this gap.
Another opener may initialize in between; the acquired writer/read locks and
the current validated header determine the subsequent snapshot. The main-file
shared lock prevents any closer from unlinking WAL/SHM during the handoff. -/
def withSession (paths : Paths) (writable : Bool) (action : Session → IO α) : IO α := do
  let exclusiveDatabase ← needsExclusiveDatabase paths writable
  let run := do
    let nativeEndian ← WALVFS.nativeBigEndian
    let session : Session := {
      paths := paths
      nativeBigEndian := nativeEndian
      firstConnection := false
      writable := writable
      exclusiveDatabase := exclusiveDatabase }
    let first ← WALVFS.tryRangeLock paths.shm.toString 128 1 true true
    if let some descriptor := first then
      try
        WALVFS.withRange paths.shm 120 1 true false do
          initializeWriter { session with firstConnection := true }
      finally WALVFS.releaseRangeLock descriptor
    withSharedRetry paths.shm 128 1 (do
      if writable then
        WALVFS.withRange paths.shm 120 1 true false do
          initializeWriter session
          action session
      else
        withSharedRetry paths.shm 121 7 (action session) 100) 100
  if exclusiveDatabase then WALVFS.withRange paths.main 1073741824 512 true false run
  else
    WALVFS.withRange paths.main 1073741824 1 false false do
      WALVFS.withRange paths.main 1073741826 510 false false run

/-- Only bytes admitted by the published wal-index are visible while another
connection is open. A durable but unpublished suffix is not a transaction. -/
def Session.visibleWAL (session : Session) : IO (Array UInt8) := do
  let header ← indexHeader session 20
  if header.maxFrame.val = 0 then return #[]
  let length := 32 + header.maxFrame.val * (header.pageSize + 24)
  let bytes ← SyscallVFS.preadBytes session.paths.wal.toString 0 length.toUSize
  unless bytes.size = length do throw (IO.userError "WAL committed prefix is truncated")
  let some log ← lift (WALAppend.read bytes.data) |
    throw (IO.userError "WAL committed header is invalid")
  unless log.committedFrames = header.maxFrame.val && log.pageCount = header.databaseSize.val &&
      log.header.saltFirst = header.saltFirst && log.header.saltSecond = header.saltSecond &&
      log.checksum = header.frameChecksum do
    throw (IO.userError "WAL and shared index disagree")
  return bytes.data

/-- Append a full Lean-encoded image without changing any committed WAL byte.
Hash mappings become visible only after WAL durability and before the header. -/
def Session.append (session : Session) (syncFile : System.FilePath → IO Unit)
    (initialHeader : PhysicalWAL.Header) (pages : Array (Array UInt8)) : IO Unit := do
  unless session.writable do throw (IO.userError "WAL writer session required")
  let old ← indexHeader session 20
  let visible ← session.visibleWAL
  let log ← match ← lift (WALAppend.read visible) with
    | some log => pure log
    | none => do
        let some first := pages[0]? | throw (IO.userError "cannot publish an empty WAL database image")
        let bytes ← lift (WALAppend.initialBytes initialHeader first.size)
        let some log ← lift (WALAppend.read bytes) |
          throw (IO.userError "invalid initial WAL header")
        IO.FS.writeBinFile session.paths.wal (ByteArray.mk bytes)
        pure log
  let prepared ← lift (WALAppend.prepare log pages)
  let index ← lift (WALIndex.append session.nativeBigEndian log.committedFrames
    prepared.pages (← indexBytes session.paths))
  let transfers := prepared.writes.map fun write =>
    ({ bytes := ByteArray.mk write.bytes, offset := write.offset.toUInt64 } : SyscallVFS.PageTransfer)
  -- Invalidate any old uncommitted suffix without truncating a mapped inode.
  -- Zero page-number is an invalid frame under either checksum byte order.
  writeAt session.paths.wal prepared.endOffset #[0, 0, 0, 0]
  SyscallVFS.pwritePages session.paths.wal.toString transfers
  syncFile session.paths.wal
  for transfer in index.writes do writeAt session.paths.shm transfer.offset transfer.bytes
  publishHeader session {
    change := ⟨(old.change.val + 1) % 2^32, Nat.mod_lt _ (by decide)⟩
    bigEndianChecksum := log.header.bigEndian, pageSize := log.header.pageSize
    maxFrame := prepared.committedFrames, databaseSize := prepared.databaseSize
    frameChecksum := prepared.checksum
    saltFirst := log.header.saltFirst, saltSecond := log.header.saltSecond }

def Session.markBackfilled (session : Session) : IO Unit := do
  let header ← indexHeader session 20
  let number := WALIndex.numberBytes session.nativeBigEndian 4
  writeAt session.paths.shm 128 (number header.maxFrame.val)
  writeAt session.paths.shm 96 (number header.maxFrame.val)

end SQLeanite.SQLite.WALShared
