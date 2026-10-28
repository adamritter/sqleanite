import SQLeanite.PageFormat.SignedInteger64Bits
import SQLeanite.SQLite.Limits

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

def schemaType : Text :=
  ⟨[116, 97, 98, 108, 101], by decide⟩

def schemaName : Text :=
  ⟨[105, 116, 101, 109, 115], by decide⟩

def schemaSQL : Text :=
  ⟨[67, 82, 69, 65, 84, 69, 32, 84, 65, 66, 76, 69, 32, 105, 116, 101,
    109, 115, 40, 105, 100, 32, 73, 78, 84, 69, 71, 69, 82, 32, 80, 82,
    73, 77, 65, 82, 89, 32, 75, 69, 89, 44, 102, 105, 114, 115, 116, 44,
    115, 101, 99, 111, 110, 100, 41], by decide⟩

def rootPageInteger : SignedInteger .eight :=
  ⟨2, by decide, by decide⟩

end PhysicalCodec

end SQLeanite
