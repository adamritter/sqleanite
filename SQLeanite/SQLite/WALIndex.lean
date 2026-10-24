import SQLeanite.SQLite.WALRead

/-!
SQLite 3.53.4 wal.c: native-endian wal-index headers and append-only hash
mappings. This module only constructs byte transfers; locking and publication
order belong to the IO adapter. Host byte order is an explicit input.
-/
namespace SQLeanite.SQLite.WALIndex

open FileFormat PhysicalWAL

def regionSize : Nat := 32768
def headerSize : Nat := 136
def firstCapacity : Nat := 4062
def regionCapacity : Nat := 4096
def slotCount : Nat := 8192

def numberBytes (bigEndian : Bool) (width value : Nat) : Array UInt8 :=
  let bytes := encodeUnsignedFixed width value
  (if bigEndian then bytes else bytes.reverse).toArray

def number? (bigEndian : Bool) (bytes : Array UInt8) (offset width : Nat) : Option Nat :=
  if offset + width ≤ bytes.size then
    let part := (bytes.extract offset (offset + width)).toList
    some ((if bigEndian then part else part.reverse).foldl (fun n byte => n * 256 + byte.toNat) 0)
  else none

structure Header where
  change : U32Value
  bigEndianChecksum : Bool
  pageSize : Nat
  maxFrame : U32Value
  databaseSize : U32Value
  frameChecksum : Checksum
  saltFirst : U32Value
  saltSecond : U32Value
  deriving Repr

def Header.prefix (nativeBigEndian : Bool) (header : Header) : Array UInt8 :=
  numberBytes nativeBigEndian 4 walVersion ++ numberBytes nativeBigEndian 4 0 ++
  numberBytes nativeBigEndian 4 header.change.val ++
  #[1, if header.bigEndianChecksum then 1 else 0] ++
  numberBytes nativeBigEndian 2 (if header.pageSize == 65536 then 1 else header.pageSize) ++
  numberBytes nativeBigEndian 4 header.maxFrame.val ++
  numberBytes nativeBigEndian 4 header.databaseSize.val ++
  numberBytes nativeBigEndian 4 header.frameChecksum.first.val ++
  numberBytes nativeBigEndian 4 header.frameChecksum.second.val ++
  numberBytes true 4 header.saltFirst.val ++ numberBytes true 4 header.saltSecond.val

def Header.encode (nativeBigEndian : Bool) (header : Header) : Array UInt8 :=
  let first := header.prefix nativeBigEndian
  let crc := WALRead.checksum nativeBigEndian .zero first.toList
  first ++ numberBytes nativeBigEndian 4 crc.first.val ++
    numberBytes nativeBigEndian 4 crc.second.val

theorem numberBytes_size (bigEndian : Bool) (width value : Nat) :
    (numberBytes bigEndian width value).size = width := by
  unfold numberBytes
  split <;> simp [encodeUnsignedFixed_length]

theorem Header.prefix_size (nativeBigEndian : Bool) (header : Header) :
    (header.prefix nativeBigEndian).size = 40 := by
  simp [Header.prefix, numberBytes_size]

theorem Header.encode_size (nativeBigEndian : Bool) (header : Header) :
    (header.encode nativeBigEndian).size = 48 := by
  simp [Header.encode, Header.prefix_size, numberBytes_size]

def u32? (value : Nat) : Option U32Value :=
  if bound : value < 2 ^ 32 then some ⟨value, by simpa using bound⟩ else none

def decodeHeader (nativeBigEndian : Bool) (bytes : Array UInt8) : Option Header := do
  unless bytes.size = 48 do none
  let get := number? nativeBigEndian bytes
  unless (← get 0 4) = walVersion && bytes[12]? == some 1 do none
  let flag ← (bytes[13]? : Option UInt8)
  unless flag == 0 || flag == 1 do none
  let encodedPageSize ← get 14 2
  let pageSize := if encodedPageSize == 1 then 65536 else encodedPageSize
  let maxFrame ← get 16 4
  unless decide (ValidSQLitePageSize pageSize) || (pageSize == 0 && maxFrame == 0) do none
  let crc := WALRead.checksum nativeBigEndian .zero (bytes.toList.take 40)
  unless (← get 40 4) = crc.first.val && (← get 44 4) = crc.second.val do none
  return {
    change := ← u32? (← get 8 4)
    bigEndianChecksum := flag == 1
    pageSize
    maxFrame := ← u32? maxFrame
    databaseSize := ← u32? (← get 20 4)
    frameChecksum := ⟨← u32? (← get 24 4), ← u32? (← get 28 4)⟩
    saltFirst := ← u32? (← number? true bytes 32 4)
    saltSecond := ← u32? (← number? true bytes 36 4) }

/-- Readers require identical copies with a valid checksum. A torn publication
is retried by the adapter, never treated as a new committed snapshot. -/
def decodeCopies (nativeBigEndian : Bool) (bytes : Array UInt8) : Option Header := do
  unless 96 ≤ bytes.size do none
  let first := bytes.extract 0 48
  unless first == bytes.extract 48 96 do none
  decodeHeader nativeBigEndian first

/-- One positional write into the shared mapping. Offsets are absolute bytes. -/
structure Write where
  offset : Nat
  bytes : Array UInt8

structure Prepared where
  bytes : Array UInt8
  writes : Array Write := #[]

/-- This is the wal.c block calculation, including the shorter first block. -/
def frameRegion (frame : Nat) : Nat := (frame + 33) / regionCapacity

def frameBase (region : Nat) : Nat :=
  if region = 0 then 0 else firstCapacity + (region - 1) * regionCapacity

def mappingOffset (region relative : Nat) : Nat :=
  region * regionSize + (if region = 0 then headerSize else 0) + (relative - 1) * 4

def hashOffset (region slot : Nat) : Nat := region * regionSize + 16384 + slot * 2

def hashSlot (page : Nat) : Nat := (page * 383) % slotCount

def Prepared.write (prepared : Prepared) (offset : Nat) (data : Array UInt8) : Prepared := Id.run do
  let mut bytes := prepared.bytes
  if bytes.size < offset + data.size then
    bytes := bytes ++ Array.replicate (offset + data.size - bytes.size) 0
  for i in [:data.size] do
    bytes := bytes.set! (offset + i) data[i]!
  return { bytes, writes := prepared.writes.push ⟨offset, data⟩ }

def Prepared.ensureRegion (prepared : Prepared) (region : Nat) : Prepared :=
  let needed := (region + 1) * regionSize
  if prepared.bytes.size < needed then
    prepared.write prepared.bytes.size (Array.replicate (needed - prepared.bytes.size) 0)
  else prepared

def clearRegion (prepared : Prepared) (region : Nat) : Prepared :=
  let start := region * regionSize + if region = 0 then headerSize else 0
  prepared.write start (Array.replicate ((region + 1) * regionSize - start) 0)

/-- walCleanupHash removes only unpublished entries in the last visible block.
All slots that may still be used by a reader of the committed prefix survive. -/
def cleanup (nativeBigEndian : Bool) (maxFrame : Nat) (prepared : Prepared) :
    Except String Prepared := do
  if maxFrame = 0 then return prepared
  let region := frameRegion maxFrame
  let limit := maxFrame - frameBase region
  unless (region + 1) * regionSize ≤ prepared.bytes.size do
    throw "WAL index has an incomplete committed mapping"
  let mut result := prepared
  for slot in [:slotCount] do
    let offset := hashOffset region slot
    let some value := number? nativeBigEndian result.bytes offset 2 |
      throw "WAL index slot is truncated"
    if limit < value then
      result := result.write offset (numberBytes nativeBigEndian 2 0)
  let start := mappingOffset region (limit + 1)
  return result.write start (Array.replicate (hashOffset region 0 - start) 0)

def findSlot (nativeBigEndian : Bool) (bytes : Array UInt8) (region : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, slot => do
      let value ← number? nativeBigEndian bytes (hashOffset region slot) 2
      if value = 0 then some slot
      else findSlot nativeBigEndian bytes region fuel ((slot + 1) % slotCount)

/-- Append mappings in frame order. Existing committed mappings are immutable;
only newly reached blocks and slots are written. -/
def append (nativeBigEndian : Bool) (maxFrame : Nat) (pages : Array Nat)
    (bytes : Array UInt8) : Except String Prepared := do
  let mut result ← cleanup nativeBigEndian maxFrame ⟨bytes, #[]⟩
  for i in [:pages.size] do
    let page := pages[i]!
    unless 0 < page && page < 2 ^ 32 do throw "WAL page number is out of range"
    let frame := maxFrame + i + 1
    unless frame < 2 ^ 32 do throw "WAL frame number is out of range"
    let region := frameRegion frame
    let relative := frame - frameBase region
    result := result.ensureRegion region
    if relative = 1 then result := clearRegion result region
    let some slot := findSlot nativeBigEndian result.bytes region slotCount (hashSlot page) |
      throw "WAL index hash table is full"
    result := result.write (mappingOffset region relative) (numberBytes nativeBigEndian 4 page)
    result := result.write (hashOffset region slot) (numberBytes nativeBigEndian 2 relative)
  return result

/-- Appending no frames cannot change any previously committed mapping. The
cleanup step may remove an interrupted writer's unpublished suffix. -/
theorem append_empty (nativeBigEndian : Bool) (maxFrame : Nat) (bytes : Array UInt8) :
    append nativeBigEndian maxFrame #[] bytes = cleanup nativeBigEndian maxFrame ⟨bytes, #[]⟩ := by
  simp [append]

end SQLeanite.SQLite.WALIndex
