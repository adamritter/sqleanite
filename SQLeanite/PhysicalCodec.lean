import SQLeanite.SQLite.Limits
import SQLeanite.Durability
import SQLeanite.GrowableStorage

namespace SQLeanite
namespace PhysicalCodec

open FileFormat

def pageSize : Nat := 4096
def textByteLimit : Nat := SQLite.Limits.maxLength + 1

/-- TEXT preserves its exact UTF-8 file bytes, including malformed sequences.
The strict bound admits SQLite's inclusive default byte limit. -/
structure Text where
  bytes : List UInt8
  lengthBound : bytes.length < textByteLimit
  deriving DecidableEq

/-- Blobs retain their exact bytes. The shared bound is well above a page;
large values are split across SQLite overflow pages by the physical encoder. -/
structure Blob where
  bytes : List UInt8
  lengthBound : bytes.length < textByteLimit
  deriving DecidableEq

def Text.serialType (text : Text) : TextSerialType := {
  code := ⟨13 + 2 * text.bytes.length, by
    have bound := text.lengthBound
    simp only [textByteLimit, SQLite.Limits.maxLength] at bound
    omega⟩
  atLeastThirteen := by
    change 13 ≤ 13 + 2 * text.bytes.length
    omega
  oddCode := by
    change (13 + 2 * text.bytes.length) % 2 = 1
    omega }

def Text.recordField (text : Text) : RecordField :=
  .text text.serialType {
    bytes := text.bytes
    length_eq := by
      change text.bytes.length = (13 + 2 * text.bytes.length - 13) / 2
      omega }

def Blob.serialType (blob : Blob) : BlobSerialType := {
  code := ⟨12 + 2 * blob.bytes.length, by
    have bound := blob.lengthBound
    simp only [textByteLimit, SQLite.Limits.maxLength] at bound
    omega⟩
  atLeastTwelve := by
    change 12 ≤ 12 + 2 * blob.bytes.length
    omega
  evenCode := by
    change (12 + 2 * blob.bytes.length) % 2 = 0
    omega }

def Blob.recordField (blob : Blob) : RecordField :=
  .blob blob.serialType {
    bytes := blob.bytes
    length_eq := by
      change blob.bytes.length = (12 + 2 * blob.bytes.length - 12) / 2
      omega }

/-- The five SQLite storage classes; REAL retains its binary64 bits. -/
inductive Value where
  | null
  | integer (value : SignedInteger .eight)
  | realBits (bits : U64Value)
  | text (value : Text)
  | blob (value : Blob)
  deriving DecidableEq

def Value.recordField : Value → RecordField
  | .null => .null
  | .integer value => .integer .eight value
  | .realBits bits => .floatBits bits
  | .text value => value.recordField
  | .blob value => value.recordField

def widenSignedInteger {width : IntegerWidth} (value : SignedInteger width) :
    SignedInteger .eight := {
  value := value.value
  lowerBound := by
    have lower := value.lowerBound
    cases width <;> simp [IntegerWidth.midpoint] at lower ⊢ <;> omega
  upperBound := by
    have upper := value.upperBound
    cases width <;> simp [IntegerWidth.midpoint] at upper ⊢ <;> omega }

theorem widenSignedInteger_value {width : IntegerWidth}
    (value : SignedInteger width) :
    (widenSignedInteger value).value = value.value := rfl

theorem widenSignedInteger_eight (value : SignedInteger .eight) :
    widenSignedInteger value = value := by
  exact SignedInteger.ext rfl

def decodeValueField : RecordField → Option Value
  | .null => some .null
  | .integer _ value => some (.integer (widenSignedInteger value))
  | .floatBits bits => some (.realBits bits)
  | .constantZero => some (.integer ⟨0, by decide, by decide⟩)
  | .constantOne => some (.integer ⟨1, by decide, by decide⟩)
  | .text _ payload =>
      if bound : payload.bytes.length < textByteLimit then
        some (.text ⟨payload.bytes, bound⟩)
      else none
  | .blob _ payload =>
      if bound : payload.bytes.length < textByteLimit then
        some (.blob ⟨payload.bytes, bound⟩)
      else none

set_option maxRecDepth 2000 in
theorem decodeValueField_recordField (value : Value) :
    decodeValueField value.recordField = some value := by
  cases value with
  | null => rfl
  | integer value => rfl
  | realBits bits => rfl
  | text value =>
      simp [Value.recordField, Text.recordField, decodeValueField,
        value.lengthBound]
  | blob value =>
      simp [Value.recordField, Blob.recordField, decodeValueField,
        value.lengthBound]

theorem Value.recordField_payload_length_le (value : Value) :
    value.recordField.encodePayload.length ≤ textByteLimit := by
  cases value with
  | null => simp [Value.recordField, RecordField.encodePayload, textByteLimit]
  | integer value =>
      simp [Value.recordField, RecordField.encodePayload,
        encodeSignedInteger_length, IntegerWidth.bytes, textByteLimit]
  | realBits bits =>
      simp [Value.recordField, RecordField.encodePayload,
        encodeUnsignedFixed_length, textByteLimit]
  | text value =>
      simp [Value.recordField, Text.recordField, RecordField.encodePayload]
      exact Nat.le_of_lt value.lengthBound
  | blob value =>
      simp [Value.recordField, Blob.recordField, RecordField.encodePayload]
      exact Nat.le_of_lt value.lengthBound

/-- A row in the fixed three-column MVP table. `rowid` is the value of the
`INTEGER PRIMARY KEY`; SQLite stores a NULL placeholder for that column in the
record payload and the actual key in the table-leaf cell header. -/
structure Row where
  rowid : SignedInteger .eight
  first : Value
  second : Value
  deriving DecidableEq

def Row.recordFields (row : Row) : List RecordField :=
  [.null, row.first.recordField, row.second.recordField]

def Row.record (row : Row) : PhysicalRecord := {
  fields := row.recordFields
  headerSizeBound := by
    have serialBound := encodeRecordSerialTypes_length_le row.recordFields
    have headerBound := recordHeaderSize_le
      (encodeRecordSerialTypes row.recordFields).length
    have serialSmall : (encodeRecordSerialTypes row.recordFields).length ≤ 27 := by
      simpa [Row.recordFields] using serialBound
    change recordHeaderSize (encodeRecordSerialTypes row.recordFields).length <
      18446744073709551616
    omega }

theorem Row.record_encode_length_lt_u64 (row : Row) :
    row.record.encode.length < 2 ^ 64 := by
  rw [PhysicalRecord.encode_length]
  have serialBound := encodeRecordSerialTypes_length_le row.recordFields
  have headerBound := recordHeaderSize_le
    (encodeRecordSerialTypes row.recordFields).length
  have serialSmall : (encodeRecordSerialTypes row.recordFields).length ≤ 27 := by
    simpa [Row.recordFields] using serialBound
  have headerSmall : row.record.headerSize.val ≤ 36 := by
    change recordHeaderSize (encodeRecordSerialTypes row.recordFields).length ≤ 36
    omega
  have firstBound := row.first.recordField_payload_length_le
  have secondBound := row.second.recordField_payload_length_le
  have payloadLength : row.record.encodePayload.length =
      row.first.recordField.encodePayload.length +
        row.second.recordField.encodePayload.length := by
    change (RecordField.null.encodePayload ++
      (row.first.recordField.encodePayload ++
        (row.second.recordField.encodePayload ++ []))).length = _
    simp [RecordField.encodePayload]
  rw [payloadLength]
  change row.record.headerSize.val +
    (row.first.recordField.encodePayload.length +
      row.second.recordField.encodePayload.length) < 2 ^ 64
  simp only [textByteLimit, SQLite.Limits.maxLength] at firstBound secondBound
  omega

def decodeRowFields (rowid : SignedInteger .eight) :
    List RecordField → Option Row
  | [.null, first, second] => do
      let first ← decodeValueField first
      let second ← decodeValueField second
      some ⟨rowid, first, second⟩
  | _ => none

theorem decodeRowFields_recordFields (row : Row) :
    decodeRowFields row.rowid row.recordFields = some row := by
  simp [Row.recordFields, decodeRowFields, decodeValueField_recordField]

def Row.payloadSize (row : Row) : U64Value :=
⟨row.record.encode.length, by
    exact row.record_encode_length_lt_u64⟩

def Row.encodeCell (row : Row) : List UInt8 :=
  encodeVarint row.payloadSize ++ encodeVarint (signedInteger64Bits row.rowid) ++
    row.record.encode

def decodeRowCell (input : List UInt8) : Option (Row × List UInt8) := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (rowidBits, afterRowid) ← decodeVarint afterSize
  let (record, suffix) ← decodePhysicalRecord afterRowid
  if _sizeMatches : record.encode.length = payloadSize.val then
    let rowid := signedIntegerFromUnsigned .eight rowidBits
    let row ← decodeRowFields rowid record.fields
    some (row, suffix)
  else none

theorem decodeRowCell_encode (row : Row) (suffix : List UInt8) :
    decodeRowCell (row.encodeCell ++ suffix) = some (row, suffix) := by
  have encodedLayout : row.encodeCell ++ suffix =
      encodeVarint row.payloadSize ++
        (encodeVarint (signedInteger64Bits row.rowid) ++
          (row.record.encode ++ suffix)) := by
    simp [Row.encodeCell, List.append_assoc]
  rw [encodedLayout]
  unfold decodeRowCell
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodePhysicalRecord_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  have sizeMatches : row.record.encode.length = row.payloadSize.val := rfl
  simp only [dif_pos sizeMatches]
  rw [signedIntegerFromBits_toBits]
  change (decodeRowFields row.rowid row.recordFields).bind
    (fun decoded => some (decoded, suffix)) = some (row, suffix)
  rw [decodeRowFields_recordFields]
  rfl

def encodeCells (rows : List Row) : List UInt8 :=
  rows.flatMap Row.encodeCell

@[simp] theorem encodeCells_cons (row : Row) (rows : List Row) :
    encodeCells (row :: rows) = row.encodeCell ++ encodeCells rows := rfl

def decodeCells : Nat → List UInt8 → Option (List Row × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (row, afterRow) ← decodeRowCell input
      let (rows, suffix) ← decodeCells count afterRow
      some (row :: rows, suffix)

theorem decodeCells_encode (rows : List Row) (suffix : List UInt8) :
    decodeCells rows.length (encodeCells rows ++ suffix) = some (rows, suffix) := by
  induction rows generalizing suffix with
  | nil => rfl
  | cons row rows induction =>
      rw [encodeCells_cons, List.append_assoc]
      simp only [List.length_cons, decodeCells]
      rw [decodeRowCell_encode row (encodeCells rows ++ suffix)]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [induction]

def encodeU16Nat (value : Nat) : List UInt8 :=
  encodeUnsignedFixed 2 value

theorem encodeU16Nat_length (value : Nat) :
    (encodeU16Nat value).length = 2 :=
  encodeUnsignedFixed_length 2 value

def cellOffsetsFrom (start : Nat) : List (List UInt8) → List Nat
  | [] => []
  | cell :: cells => start :: cellOffsetsFrom (start + cell.length) cells

def leafHeader (cellCount contentStart : Nat) : List UInt8 :=
  [13, 0, 0] ++ encodeU16Nat cellCount ++ encodeU16Nat contentStart ++ [0]

theorem leafHeader_length (cellCount contentStart : Nat) :
    (leafHeader cellCount contentStart).length = 8 := by
  simp [leafHeader, encodeU16Nat_length]

def leafPointers (contentStart : Nat) (cells : List (List UInt8)) : List UInt8 :=
  (cellOffsetsFrom contentStart cells).flatMap encodeU16Nat

theorem cellOffsetsFrom_length (start : Nat) (cells : List (List UInt8)) :
    (cellOffsetsFrom start cells).length = cells.length := by
  induction cells generalizing start with
  | nil => rfl
  | cons cell cells induction => simp [cellOffsetsFrom, induction]

private theorem encodeU16Nats_length (values : List Nat) :
    (values.flatMap encodeU16Nat).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [encodeU16Nat_length, induction]
      omega

theorem leafPointers_length (contentStart : Nat) (cells : List (List UInt8)) :
    (leafPointers contentStart cells).length = 2 * cells.length := by
  unfold leafPointers
  rw [encodeU16Nats_length, cellOffsetsFrom_length]

def cellBytes (cells : List (List UInt8)) : List UInt8 := cells.flatten

def PageFit (headerOffset : Nat) (cells : List (List UInt8)) : Prop :=
  headerOffset + 8 + 2 * cells.length + (cellBytes cells).length ≤ pageSize

def leafPageBody (headerOffset : Nat) (cells : List (List UInt8)) : List UInt8 :=
  let content := cellBytes cells
  let contentStart := pageSize - content.length
  let headerAndPointers :=
    leafHeader cells.length contentStart ++ leafPointers contentStart cells
  headerAndPointers ++
    List.replicate (contentStart - headerOffset - headerAndPointers.length) 0 ++ content

theorem leafPageBody_length (headerOffset : Nat) (cells : List (List UInt8))
    (fits : PageFit headerOffset cells) :
    (leafPageBody headerOffset cells).length = pageSize - headerOffset := by
  have prefixLength :
      (leafHeader cells.length (pageSize - (cellBytes cells).length) ++
        leafPointers (pageSize - (cellBytes cells).length) cells).length =
          8 + 2 * cells.length := by
    simp [leafHeader_length, leafPointers_length]
  unfold leafPageBody
  dsimp only
  rw [List.length_append, List.length_append, List.length_replicate, prefixLength]
  unfold PageFit at fits
  simp only [pageSize] at fits ⊢
  omega

theorem PageFit.cellCount_lt (fits : PageFit headerOffset cells) :
    cells.length < 65536 := by
  unfold PageFit at fits
  simp only [pageSize] at fits
  omega

theorem contentStart_lt (cells : List (List UInt8)) :
    pageSize - (cellBytes cells).length < 65536 := by
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)

theorem leafPageBody_drop_content (cells : List (List UInt8))
    (fits : PageFit 0 cells) :
    (leafPageBody 0 cells).drop (pageSize - (cellBytes cells).length) =
      cellBytes cells := by
  let contentStart := pageSize - (cellBytes cells).length
  let headerAndPointers :=
    leafHeader cells.length contentStart ++ leafPointers contentStart cells
  have headerAndPointersLength : headerAndPointers.length = 8 + 2 * cells.length := by
    simp [headerAndPointers, leafHeader_length, leafPointers_length]
  have contentLe : (cellBytes cells).length ≤ pageSize := by
    unfold PageFit at fits
    omega
  have contentStartIdentity : contentStart + (cellBytes cells).length = pageSize := by
    unfold contentStart
    exact Nat.sub_add_cancel contentLe
  have headerLeStart : headerAndPointers.length ≤ contentStart := by
    rw [headerAndPointersLength]
    unfold PageFit at fits
    omega
  have prefixLength :
      (headerAndPointers ++ List.replicate
        (contentStart - headerAndPointers.length) 0).length = contentStart := by
    rw [List.length_append, List.length_replicate]
    omega
  unfold leafPageBody
  let prefixPad := headerAndPointers ++
    List.replicate (contentStart - headerAndPointers.length) 0
  have prefixPadLength : prefixPad.length = contentStart := prefixLength
  change List.drop contentStart (prefixPad ++ cellBytes cells) = cellBytes cells
  calc
    List.drop contentStart (prefixPad ++ cellBytes cells) =
        List.drop prefixPad.length (prefixPad ++ cellBytes cells) := by
          rw [prefixPadLength]
    _ = cellBytes cells := by simp

/-- The content-region theorem for page one, whose B-tree body follows an
arbitrary database header. Cell offsets are absolute page offsets, so the
prefix length must agree with `headerOffset`. -/
theorem prefix_leafPageBody_drop_content (headerBytes : List UInt8)
    (headerOffset : Nat) (cells : List (List UInt8))
    (prefixLength : headerBytes.length = headerOffset)
    (fits : PageFit headerOffset cells) :
    (headerBytes ++ leafPageBody headerOffset cells).drop
        (pageSize - (cellBytes cells).length) = cellBytes cells := by
  let contentStart := pageSize - (cellBytes cells).length
  let headerAndPointers :=
    leafHeader cells.length contentStart ++ leafPointers contentStart cells
  have headerAndPointersLength : headerAndPointers.length = 8 + 2 * cells.length := by
    simp [headerAndPointers, leafHeader_length, leafPointers_length]
  have contentLe : (cellBytes cells).length ≤ pageSize := by
    unfold PageFit at fits
    omega
  have headerLeStart : headerOffset + headerAndPointers.length ≤ contentStart := by
    rw [headerAndPointersLength]
    unfold PageFit at fits contentStart
    omega
  let bodyPrefix := headerAndPointers ++ List.replicate
    (contentStart - headerOffset - headerAndPointers.length) 0
  have bodyPrefixLength : bodyPrefix.length = contentStart - headerOffset := by
    unfold bodyPrefix
    rw [List.length_append, List.length_replicate]
    omega
  have fullPrefixLength : (headerBytes ++ bodyPrefix).length = contentStart := by
    rw [List.length_append, prefixLength, bodyPrefixLength]
    omega
  unfold leafPageBody
  change List.drop contentStart
    (headerBytes ++ (bodyPrefix ++ cellBytes cells)) = cellBytes cells
  rw [← List.append_assoc]
  calc
    List.drop contentStart ((headerBytes ++ bodyPrefix) ++ cellBytes cells) =
        List.drop (headerBytes ++ bodyPrefix).length
          ((headerBytes ++ bodyPrefix) ++ cellBytes cells) := by
            rw [fullPrefixLength]
    _ = cellBytes cells := by simp

def Row.keyLess (left right : Row) : Prop := left.rowid.value < right.rowid.value

/-- The first concrete codec intentionally fixes one table and two payload
columns. Rows must be ordered by their INTEGER PRIMARY KEY, and the no-overflow
MVP is enforced by a proof that all encoded cells fit one 4096-byte leaf page. -/
structure Database where
  rows : List Row
  rowidsSorted : rows.Pairwise Row.keyLess
  pageFits : PageFit 0 (rows.map Row.encodeCell)

theorem Database.ext {left right : Database} (rows : left.rows = right.rows) :
    left = right := by
  cases left
  cases right
  cases rows
  rfl

def Database.dataPageBytes (database : Database) : List UInt8 :=
  leafPageBody 0 (database.rows.map Row.encodeCell)

theorem Database.dataPageBytes_length (database : Database) :
    database.dataPageBytes.length = pageSize := by
  simpa [Database.dataPageBytes] using
    leafPageBody_length 0 (database.rows.map Row.encodeCell) database.pageFits

def Database.dataPage (database : Database) : Storage.Page pageSize := {
  bytes := database.dataPageBytes.toArray
  sizeInvariant := by simp [database.dataPageBytes_length] }

private def schemaType : Text :=
  ⟨[116, 97, 98, 108, 101], by decide⟩

private def schemaName : Text :=
  ⟨[105, 116, 101, 109, 115], by decide⟩

private def schemaSQL : Text :=
  ⟨[67, 82, 69, 65, 84, 69, 32, 84, 65, 66, 76, 69, 32, 105, 116, 101,
    109, 115, 40, 105, 100, 32, 73, 78, 84, 69, 71, 69, 82, 32, 80, 82,
    73, 77, 65, 82, 89, 32, 75, 69, 89, 44, 102, 105, 114, 115, 116, 44,
    115, 101, 99, 111, 110, 100, 41], by decide⟩

private def rootPageInteger : SignedInteger .eight :=
  ⟨2, by decide, by decide⟩

private def schemaRecord : PhysicalRecord := {
  fields := [schemaType.recordField, schemaName.recordField,
    schemaName.recordField, .integer .eight rootPageInteger,
    schemaSQL.recordField]
  headerSizeBound := by
    have serialBound := encodeRecordSerialTypes_length_le
      [schemaType.recordField, schemaName.recordField,
        schemaName.recordField, .integer .eight rootPageInteger,
        schemaSQL.recordField]
    have headerBound := recordHeaderSize_le
      (encodeRecordSerialTypes [schemaType.recordField, schemaName.recordField,
        schemaName.recordField, .integer .eight rootPageInteger,
        schemaSQL.recordField]).length
    simp only [List.length_cons, List.length_nil] at serialBound
    omega }

private def schemaRowid : SignedInteger .eight :=
  ⟨1, by decide, by decide⟩

private theorem schemaRecord_encode_length_lt :
    schemaRecord.encode.length < pageSize := by
  rw [PhysicalRecord.encode_length]
  have headerValue : schemaRecord.headerSize.val = 6 := by decide
  have payloadValue : schemaRecord.encodePayload.length = 78 := by decide
  rw [headerValue, payloadValue]
  decide

def schemaCell : List UInt8 :=
  encodeVarint ⟨schemaRecord.encode.length, by
    have encodedLength := schemaRecord_encode_length_lt
    simp only [pageSize] at encodedLength
    omega⟩ ++
    encodeVarint (signedInteger64Bits schemaRowid) ++ schemaRecord.encode

theorem schemaPageFits : PageFit 100 [schemaCell] := by
  unfold PageFit schemaCell schemaRecord schemaType schemaName schemaSQL
  decide

def databaseHeader : DatabaseHeader := {
  headerPrefix := {
    pageSizeField := ⟨4096, by omega⟩
    writeVersion := 1
    readVersion := 1
    reservedSpace := 0
    changeCounter := ⟨1, by omega⟩ }
  databaseSizePages := ⟨2, by omega⟩
  firstFreelistTrunk := ⟨0, by omega⟩
  freelistPageCount := ⟨0, by omega⟩
  schemaCookie := ⟨1, by omega⟩
  schemaFormat := ⟨4, by omega⟩
  defaultPageCacheSize := ⟨0, by omega⟩
  largestRootBTreePage := ⟨0, by omega⟩
  textEncoding := ⟨1, by omega⟩
  userVersion := ⟨0, by omega⟩
  incrementalVacuum := ⟨0, by omega⟩
  applicationId := ⟨0, by omega⟩
  versionValidFor := ⟨1, by omega⟩
  sqliteVersion := ⟨3050004, by omega⟩ }

def usablePageSize : UsablePageSize :=
  ⟨pageSize, by decide, by decide⟩

theorem databaseHeader_wellFormed :
    databaseHeader.WellFormedFor usablePageSize 2 := by decide

def geometry : DiskFormat.DatabaseGeometry := {
  usable := usablePageSize
  pageCount := 2
  header := ⟨databaseHeader, databaseHeader_wellFormed⟩ }

def schemaPageBytes : List UInt8 :=
  encodeDatabaseHeader databaseHeader ++ leafPageBody 100 [schemaCell]

theorem schemaPageBytes_length : schemaPageBytes.length = pageSize := by
  unfold schemaPageBytes
  rw [List.length_append, encodeDatabaseHeader_length,
    leafPageBody_length 100 [schemaCell] schemaPageFits]
  simp [pageSize]

def schemaPage : Storage.Page pageSize := {
  bytes := schemaPageBytes.toArray
  sizeInvariant := by simp [schemaPageBytes_length] }

def Database.image (database : Database) : DiskFormat.DatabaseImage := {
  geometry
  disk := {
    read := fun pageId =>
      if pageId.val = 0 then schemaPage
      else database.dataPage } }

theorem Database.image_read_schema (database : Database) :
    (database.image.disk.read ⟨0, by
      simp [Database.image, geometry]⟩).bytes.toList = schemaPageBytes := by
  change schemaPageBytes.toArray.toList = schemaPageBytes
  exact List.toList_toArray

theorem Database.image_read_data (database : Database) :
    (database.image.disk.read ⟨1, by
      simp [Database.image, geometry]⟩).bytes.toList =
      database.dataPageBytes := by
  change database.dataPageBytes.toArray.toList = database.dataPageBytes
  exact List.toList_toArray

def Database.fileBytes (database : Database) : List UInt8 :=
  database.image.encode

theorem Database.fileBytes_length (database : Database) :
    database.fileBytes.length = 2 * pageSize := by
  unfold Database.fileBytes DiskFormat.DatabaseImage.encode
  rw [DiskFormat.encodeDisk_length]
  simp [Database.image, geometry, usablePageSize]
  omega

theorem Database.fileBytes_layout (database : Database) :
    database.fileBytes = schemaPageBytes ++ database.dataPageBytes := by
  unfold Database.fileBytes DiskFormat.DatabaseImage.encode DiskFormat.encodeDisk
  change DiskFormat.encodePages (List.ofFn (fun i : Fin 2 => database.image.disk.read i)) = _
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [DiskFormat.encodePages, List.append_nil]
  change schemaPage.bytes.toList ++ database.dataPage.bytes.toList =
    schemaPageBytes ++ database.dataPageBytes
  rw [show schemaPage.bytes.toList = schemaPageBytes by
      exact List.toList_toArray,
    show database.dataPage.bytes.toList = database.dataPageBytes by
      exact List.toList_toArray]

theorem Database.image_headerEncoded (database : Database) :
    database.image.HeaderEncoded := by
  refine ⟨leafPageBody 100 [schemaCell] ++ database.dataPageBytes, ?_⟩
  change database.fileBytes = encodeDatabaseHeader databaseHeader ++
    (leafPageBody 100 [schemaCell] ++ database.dataPageBytes)
  rw [database.fileBytes_layout]
  simp [schemaPageBytes, List.append_assoc]

private instance (left right : Row) : Decidable (Row.keyLess left right) :=
  inferInstanceAs (Decidable (left.rowid.value < right.rowid.value))

private instance (headerOffset : Nat) (cells : List (List UInt8)) :
    Decidable (PageFit headerOffset cells) := by
  unfold PageFit
  infer_instance

def decodeDataPage : List UInt8 → Option Database
  | 13 :: 0 :: 0 :: afterFreeblock => do
      let (cellCount, afterCount) ← decodeUnsignedFixed 2 afterFreeblock
      let (contentStart, afterContentStart) ← decodeUnsignedFixed 2 afterCount
      match afterContentStart with
      | 0 :: _ =>
          let (rows, suffix) ← decodeCells cellCount
            ((13 :: 0 :: 0 :: afterFreeblock).drop contentStart)
          if _suffixEmpty : suffix = [] then
            if sorted : rows.Pairwise Row.keyLess then
              if fits : PageFit 0 (rows.map Row.encodeCell) then
                let database : Database := ⟨rows, sorted, fits⟩
                if _canonical : database.dataPageBytes =
                    13 :: 0 :: 0 :: afterFreeblock then
                  some database
                else none
              else none
            else none
          else none
      | _ => none
  | _ => none

theorem cellBytes_map_encodeCell (rows : List Row) :
    cellBytes (rows.map Row.encodeCell) = encodeCells rows := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      change row.encodeCell ++ cellBytes (rows.map Row.encodeCell) =
        row.encodeCell ++ encodeCells rows
      rw [induction]

set_option maxHeartbeats 600000 in
theorem decodeDataPage_encode (database : Database) :
    decodeDataPage database.dataPageBytes = some database := by
  let cells := database.rows.map Row.encodeCell
  let contentStart := pageSize - (cellBytes cells).length
  let afterHeader := leafPointers contentStart cells ++
    List.replicate
      (contentStart -
        (leafHeader cells.length contentStart ++ leafPointers contentStart cells).length) 0 ++
    cellBytes cells
  have bodyLayout : database.dataPageBytes =
      13 :: 0 :: 0 ::
        (encodeU16Nat cells.length ++ encodeU16Nat contentStart ++ 0 :: afterHeader) := by
    unfold Database.dataPageBytes leafPageBody leafHeader
    simp only [List.cons_append, List.nil_append]
    rfl
  have countBound : cells.length < 256 ^ 2 := by
    simpa [cells] using database.pageFits.cellCount_lt
  have contentBound : contentStart < 256 ^ 2 := by
    exact contentStart_lt cells
  have dropped : database.dataPageBytes.drop contentStart = encodeCells database.rows := by
    change (leafPageBody 0 cells).drop contentStart = encodeCells database.rows
    rw [show contentStart = pageSize - (cellBytes cells).length by rfl,
      leafPageBody_drop_content cells database.pageFits]
    exact cellBytes_map_encodeCell database.rows
  rw [bodyLayout]
  unfold decodeDataPage
  change (do
    let (cellCount, afterCount) ← decodeUnsignedFixed 2
      (encodeU16Nat cells.length ++ encodeU16Nat contentStart ++ 0 :: afterHeader)
    let (decodedStart, afterContentStart) ← decodeUnsignedFixed 2 afterCount
    match afterContentStart with
    | 0 :: _ =>
        let (rows, suffix) ← decodeCells cellCount
          (database.dataPageBytes.drop decodedStart)
        if suffixEmpty : suffix = [] then
          if sorted : rows.Pairwise Row.keyLess then
            if fits : PageFit 0 (rows.map Row.encodeCell) then
              let decoded : Database := ⟨rows, sorted, fits⟩
              if decoded.dataPageBytes = database.dataPageBytes then some decoded else none
            else none
          else none
        else none
    | _ => none) = some database
  unfold encodeU16Nat
  simp only [List.append_assoc]
  rw [decodeUnsignedFixed_encode _ countBound]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeUnsignedFixed_encode _ contentBound]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dropped]
  have cellsLength : cells.length = database.rows.length := by simp [cells]
  rw [cellsLength]
  have decodedRows := decodeCells_encode database.rows []
  simp only [List.append_nil] at decodedRows
  rw [decodedRows]
  simp only [dif_pos rfl, database.rowidsSorted, database.pageFits]
  let decoded : Database :=
    ⟨database.rows, database.rowidsSorted, database.pageFits⟩
  have decodedEq : decoded = database := Database.ext rfl
  simp [decoded, decodedEq]

def decodeImage (image : DiskFormat.DatabaseImage) : Option Database :=
  match image with
  | ⟨actualGeometry, disk⟩ =>
      if geometryMatches : actualGeometry = geometry then
        let schemaId : Fin actualGeometry.pageCount := ⟨0, by
          rw [geometryMatches]
          decide⟩
        let dataId : Fin actualGeometry.pageCount := ⟨1, by
          rw [geometryMatches]
          decide⟩
        if _schemaMatches : (disk.read schemaId).bytes.toList = schemaPageBytes then
          decodeDataPage (disk.read dataId).bytes.toList
        else none
      else none

theorem decodeImage_encode (database : Database) :
    decodeImage database.image = some database := by
  unfold decodeImage
  change (if _geometryMatches : geometry = geometry then
    if _schemaMatches : schemaPage.bytes.toList = schemaPageBytes then
      decodeDataPage database.dataPage.bytes.toList
    else none
  else none) = some database
  rw [dif_pos rfl]
  have schemaMatches : schemaPage.bytes.toList = schemaPageBytes := by
    change schemaPageBytes.toArray.toList = schemaPageBytes
    exact List.toList_toArray
  rw [dif_pos schemaMatches]
  change decodeDataPage database.dataPageBytes = some database
  exact decodeDataPage_encode database

def decodeFile (input : List UInt8) : Option Database := do
  let (image, suffix) ← DiskFormat.decodeDatabaseImage input
  if _consumed : suffix = [] then decodeImage image else none

theorem decodeFile_encode (database : Database) :
    decodeFile database.fileBytes = some database := by
  unfold decodeFile Database.fileBytes
  have decoded := DiskFormat.decodeDatabaseImage_encode database.image
    database.image_headerEncoded []
  simp only [List.append_nil] at decoded
  rw [decoded]
  simp [decodeImage_encode]

def codec : Durability.DiskCodec Database := {
  Equiv := Eq
  encode := Database.image
  decode := decodeImage
  decode_encode := fun database =>
    ⟨database, decodeImage_encode database, rfl⟩ }

def Database.storageImage (database : Database) : GrowableStorage.Image pageSize := {
  pageCount := 2
  read := fun pageId => if pageId = 0 then schemaPage else database.dataPage }

def transactionWrites (database : Database) :
    List (GrowableStorage.PageWrite pageSize) :=
  [⟨1, database.dataPage⟩]

theorem apply_transactionWrites_equiv (old new : Database) :
    (GrowableStorage.applyWrites old.storageImage
      (transactionWrites new)).Equiv new.storageImage := by
  constructor
  · simp [GrowableStorage.applyWrites, transactionWrites,
      GrowableStorage.Image.write, Database.storageImage]
  · intro pageId bound
    by_cases zero : pageId = 0
    · subst pageId
      simp [GrowableStorage.applyWrites, transactionWrites,
        GrowableStorage.Image.write, Database.storageImage]
    · have one : pageId = 1 := by
        simp [GrowableStorage.applyWrites, transactionWrites,
          GrowableStorage.Image.write, Database.storageImage] at bound
        omega
      subst pageId
      simp [GrowableStorage.applyWrites, transactionWrites,
        GrowableStorage.Image.write, Database.storageImage]

def decodeStorageImage (image : GrowableStorage.Image pageSize) : Option Database :=
  if _countMatches : image.pageCount = 2 then
    decodeImage {
      geometry
      disk := { read := fun pageId => image.read pageId.val } }
  else none

theorem decodeStorageImage_equiv (database : Database)
    {image : GrowableStorage.Image pageSize}
    (equivalent : image.Equiv database.storageImage) :
    decodeStorageImage image = some database := by
  have countMatches : image.pageCount = 2 := by
    simpa [Database.storageImage] using equivalent.1
  let opened : DiskFormat.DatabaseImage := {
    geometry
    disk := { read := fun pageId => image.read pageId.val } }
  have openedEq : opened = database.image := by
    unfold opened Database.image
    apply congrArg (fun disk => DiskFormat.DatabaseImage.mk geometry disk)
    apply congrArg Storage.Disk.mk
    funext pageId
    have pageBound : pageId.val < 2 := pageId.isLt
    have imageBound : pageId.val < image.pageCount := by
      rw [countMatches]
      exact pageBound
    rw [equivalent.2 pageId.val imageBound]
    by_cases zero : pageId.val = 0
    · simp [Database.storageImage, zero]
    · have one : pageId.val = 1 := by omega
      simp [Database.storageImage, zero, one]
  unfold decodeStorageImage
  rw [dif_pos countMatches]
  change decodeImage opened = some database
  rw [openedEq]
  exact decodeImage_encode database

/-- Logical old-or-new recovery for the concrete codec. This connects the
page-level rollback protocol to reopening the actual SQLite image. -/
theorem rollbackCommit_database_crash_atomic (old new : Database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image pageSize)
    (recoveredJournal : Option (GrowableStorage.Journal pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState old.storageImage
        (transactionWrites new) phase)
      recoveredMain recoveredJournal) :
    decodeStorageImage
        (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal) =
          some old ∨
      decodeStorageImage
        (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal) =
          some new := by
  rcases GrowableStorage.rollbackCommit_crash_atomic old.storageImage
    (transactionWrites new) phase recoveredMain recoveredJournal outcome with
    recoveredOld | recoveredWrites
  · exact .inl (decodeStorageImage_equiv old recoveredOld)
  · exact .inr (decodeStorageImage_equiv new
      (recoveredWrites.trans (apply_transactionWrites_equiv old new)))

theorem rollbackCommit_database_committed_recovers_new (old new : Database)
    (recoveredMain : GrowableStorage.Image pageSize)
    (recoveredJournal : Option (GrowableStorage.Journal pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState old.storageImage
        (transactionWrites new) GrowableStorage.CommitPhase.committed)
      recoveredMain recoveredJournal) :
    decodeStorageImage
      (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal) =
        some new := by
  apply decodeStorageImage_equiv new
  exact (GrowableStorage.rollbackCommit_committed_recovers_new old.storageImage
    (transactionWrites new) recoveredMain recoveredJournal outcome).trans
      (apply_transactionWrites_equiv old new)

end PhysicalCodec
end SQLeanite
