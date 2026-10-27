import SQLeanite.SQLite.WALIndex

/-! Prefix-preserving WAL construction. The existing committed frames retain
both bytes and salts. Only new frames are constructed, chained from the last
committed checksum. Shared-index publication is a separate ordered IO step. -/
namespace SQLeanite.SQLite.WALAppend

open FileFormat PhysicalWAL

/-- New logs use the database's geometry; existing logs retain their original
header and checksum byte order. -/
def initialBytes (header : PhysicalWAL.Header) (pageSize : Nat) : Except String (Array UInt8) := do
  unless ValidSQLitePageSize pageSize do throw "invalid WAL page size"
  let some size := WALIndex.u32? pageSize | throw "invalid WAL page size"
  let fields := encodeWords [walMagicValue, walVersionValue, size,
    header.checkpointSequence, header.saltFirst, header.saltSecond]
  let crc := checksumBytes .zero fields
  return (fields ++ encodeWords [crc.first, crc.second]).toArray

structure Log where
  header : WALRead.Header
  committedFrames : Nat := 0
  pageCount : Nat := 0
  checksum : Checksum
  pages : Array Nat := #[]

def Log.endOffset (log : Log) : Nat :=
  32 + log.committedFrames * (log.header.pageSize + 24)

/-- Read a frame-sized slice each time. The traversal is linear in WAL bytes;
no frame parser scans the entire remaining log merely to check its length. -/
def scan (header : WALRead.Header) (input : Array UInt8) :
    Nat → Nat → Checksum → Array Nat → Log → Log
  | 0, _, _, _, committed => committed
  | fuel + 1, offset, crc, pages, committed =>
      let stop := offset + header.pageSize + 24
      match WALRead.decodeFrame header crc (input.extract offset stop).toList with
      | none => committed
      | some (frame, next, _) =>
          let pages := pages.push frame.pageNumber
          let committed := if frame.databaseSize = 0 then committed else
            { header, committedFrames := pages.size, pageCount := frame.databaseSize,
              checksum := next, pages }
          scan header input fuel stop next pages committed

def read (input : Array UInt8) : Except String (Option Log) := do
  let some (header, _) ← WALRead.decodeHeader (input.extract 0 32).toList | return none
  let initial : Log := { header, checksum := header.seed }
  return some (scan header input ((input.size - 32) / (header.pageSize + 24))
    32 header.seed #[] initial)

structure Frame where
  pageNumber : U32Value
  databaseSize : U32Value
  page : Array UInt8

def Frame.prefix (frame : Frame) : List UInt8 :=
  encodeU32Bytes frame.pageNumber ++ encodeU32Bytes frame.databaseSize

def Frame.checksum (header : WALRead.Header) (seed : Checksum) (frame : Frame) : Checksum :=
  WALRead.checksum header.bigEndian seed (frame.prefix ++ frame.page.toList)

def Frame.encode (header : WALRead.Header) (seed : Checksum) (frame : Frame) : Array UInt8 :=
  let crc := frame.checksum header seed
  (frame.prefix ++ encodeWords [header.saltFirst, header.saltSecond,
    crc.first, crc.second]).toArray ++ frame.page

theorem Frame.encode_size (header : WALRead.Header) (seed : Checksum) (frame : Frame) :
    (frame.encode header seed).size = 24 + frame.page.size := by
  simp [Frame.encode, Frame.prefix, encodeWords_length, encodeU32Bytes,
    encodeUnsignedFixed_length]

structure Prepared where
  /-- Every transfer starts after the previously committed prefix. -/
  writes : Array WALIndex.Write
  pages : Array Nat
  committedFrames : U32Value
  databaseSize : U32Value
  checksum : Checksum
  endOffset : Nat

def prepare (log : Log) (image : Array (Array UInt8)) : Except String Prepared := do
  unless !image.isEmpty do throw "cannot publish an empty WAL database image"
  let some size := WALIndex.u32? image.size | throw "WAL database page count is out of range"
  let some frameCount := WALIndex.u32? (log.committedFrames + image.size) |
    throw "WAL frame count is out of range"
  let mut offset := log.endOffset
  let mut crc := log.checksum
  let mut writes := #[]
  let mut pages := #[]
  for i in [:image.size] do
    let page := image[i]!
    unless page.size = log.header.pageSize do throw "WAL page size cannot change while appending"
    let some pageNumber := WALIndex.u32? (i + 1) | throw "WAL page number is out of range"
    let frame : Frame := {
      pageNumber
      databaseSize := if i + 1 = image.size then size else ⟨0, by decide⟩
      page }
    let bytes := frame.encode log.header crc
    crc := frame.checksum log.header crc
    writes := writes.push ⟨offset, bytes⟩
    pages := pages.push (i + 1)
    offset := offset + bytes.size
  return {
    writes := writes
    pages := pages
    committedFrames := frameCount
    databaseSize := size
    checksum := crc
    endOffset := offset }

theorem prepare_empty (log : Log) :
    prepare log #[] = .error "cannot publish an empty WAL database image" := rfl

end SQLeanite.SQLite.WALAppend
