import SQLeanite.Runtime.TableCursor
import SQLeanite.CoreDecode

namespace SQLeanite.Runtime.Record

open FileFormat

def serialBytesSize : List RecordField → Nat
  | [] => 0
  | field :: fields => sqliteVarintSize (encodeSerialType field.serialType).val +
      serialBytesSize fields

def payloadSize : List RecordField → Nat
  | [] => 0
  | field :: fields => serialTypePayloadSize field.serialType + payloadSize fields

theorem serialBytesSize_eq_length (fields : List RecordField) :
    serialBytesSize fields = (encodeRecordSerialTypes fields).length := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      simp [serialBytesSize, encodeRecordSerialTypes, encodeVarint_length, ih]

theorem fieldPayloadSize_eq_length (field : RecordField) :
    serialTypePayloadSize field.serialType = field.encodePayload.length := by
  cases field with
  | null => rfl
  | constantZero => rfl
  | constantOne => rfl
  | floatBits bits => simp [RecordField.serialType, RecordField.encodePayload,
      serialTypePayloadSize, encodeUnsignedFixed_length]
  | integer width value =>
      simp only [RecordField.serialType, RecordField.encodePayload,
        encodeSignedInteger_length]
      cases width <;> rfl
  | blob metadata payload => exact payload.length_eq.symm
  | text metadata payload => exact payload.length_eq.symm

theorem payloadSize_eq_length (fields : List RecordField) :
    payloadSize fields = (fields.flatMap RecordField.encodePayload).length := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      simp [payloadSize, fieldPayloadSize_eq_length, ih]

/-- SQLite computes record sizes from serial-type metadata. Avoid allocating
and walking a freshly re-encoded record just to perform the same size check. -/
def encodedSize (record : PhysicalRecord) : Nat :=
  recordHeaderSize (serialBytesSize record.fields) + payloadSize record.fields

theorem encodedSize_eq_length (record : PhysicalRecord) :
    encodedSize record = record.encode.length := by
  rw [PhysicalRecord.encode_length]
  simp [encodedSize, PhysicalRecord.headerSize, PhysicalRecord.encodePayload,
    serialBytesSize_eq_length, payloadSize_eq_length]

def decodeRowCell (schema : Core.Schema) (source : CoreDecode.IOPageSource)
    (fuel : Nat) (input : List UInt8) : IO (Option Core.Row) := do
  let some (cell, _) := decodeTableLeafCell source.usable input | return none
  let some payload ← CoreDecode.resolvedTablePayloadIOFrom source fuel cell | return none
  let some (record, suffix) := decodePhysicalRecord payload | return none
  unless suffix = [] && encodedSize record = cell.payloadSize.val do return none
  let some fields := CoreTextEncoding.fields source.textEncoding record.fields | return none
  return CoreRecord.decodeRowFields schema cell.rowid fields

/-- Full effectful equality, including malformed input and overflow reads.
Only the allocation used by the length check changes. -/
theorem decodeRowCell_eq_reference (schema : Core.Schema)
    (source : CoreDecode.IOPageSource) (fuel : Nat) (input : List UInt8) :
    decodeRowCell schema source fuel input =
      CoreDecode.decodeRowCellIOFrom schema source fuel input := by
  simp only [decodeRowCell, CoreDecode.decodeRowCellIOFrom, encodedSize_eq_length]
  rfl

/-- Decode one located row using the existing Core record/overflow decoder.
The cursor locates a cell; this layer interprets its payload under a schema.
It currently materializes all columns of that one row. Unlike SQLite's
OP_Column it does not yet lazily decode only the requested columns. -/
def readRowWithSource (schema : Core.Schema) (source : CoreDecode.IOPageSource)
    (cell : TableCursor.Cell) : IO (Option Core.Row) := do
  let some row ← decodeRowCell schema source
      (source.pageCount + 1) cell.input | return none
  if row.rowid = cell.key then return some row else return none

/-- The shared cell view is exactly the reference input at the checked
offset. Sharing changes allocation, not the record/overflow validation. -/
theorem readRowWithSource_eq_reference (schema : Core.Schema)
    (source : CoreDecode.IOPageSource) (cell : TableCursor.Cell) :
    readRowWithSource schema source cell = (do
      let some row ← CoreDecode.decodeRowCellIOFrom schema source
        (source.pageCount + 1) (cell.bytes.toList.drop cell.offset) | return none
      if row.rowid = cell.key then return some row else return none) := by
  unfold readRowWithSource
  rw [decodeRowCell_eq_reference, cell.input_eq]

def readRow (schema : Core.Schema) (pager : ReadPager.Pager)
    (cell : TableCursor.Cell) : IO (Option Core.Row) := do
  unless pager.pageSize = PhysicalCodec.pageSize do return none
  readRowWithSource schema {
    pageCount := pager.pageCount
    readPage := fun page => do
      return (← pager.get page).map ByteArray.toList } cell

end SQLeanite.Runtime.Record
