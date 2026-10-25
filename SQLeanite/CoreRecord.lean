import SQLeanite.Core

namespace SQLeanite
namespace CoreRecord

open FileFormat
def encodeFields : Nat → List Core.Value → List RecordField
  | _, [] => []
  | 0, _ :: values => .null :: values.map PhysicalCodec.Value.recordField
  | primaryKey + 1, value :: values =>
      PhysicalCodec.Value.recordField value :: encodeFields primaryKey values

@[simp] theorem encodeFields_length (primaryKey : Nat)
    (values : List Core.Value) :
    (encodeFields primaryKey values).length = values.length := by
  induction primaryKey, values using encodeFields.induct <;>
    simp_all [encodeFields]

def decodeFields : List RecordField → Option (List Core.Value)
  | [] => some []
  | field :: fields => do
      let value ← PhysicalCodec.decodeValueField field
      let values ← decodeFields fields
      some (value :: values)

theorem decodeFields_encode (values : List Core.Value) :
    decodeFields (values.map PhysicalCodec.Value.recordField) = some values := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map_cons, decodeFields]
      rw [PhysicalCodec.decodeValueField_recordField]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [induction]

def decodeRowValues (rowid : Core.Integer) : Nat → List RecordField →
    Option (List Core.Value)
  | _, [] => none
  | 0, .null :: fields => do
      let values ← decodeFields fields
      some (PhysicalCodec.Value.integer rowid :: values)
  | 0, _ :: _ => none
  | primaryKey + 1, field :: fields => do
      let value ← PhysicalCodec.decodeValueField field
      let values ← decodeRowValues rowid primaryKey fields
      some (value :: values)

theorem decodeRowValues_encode (rowid : Core.Integer) :
    ∀ (primaryKey : Nat) (values : List Core.Value),
      values[primaryKey]? = some (PhysicalCodec.Value.integer rowid) →
      decodeRowValues rowid primaryKey (encodeFields primaryKey values) =
        some values
  | _, [], present => by simp at present
  | 0, value :: values, present => by
      change some value = some (PhysicalCodec.Value.integer rowid) at present
      injection present with present
      subst value
      simp only [encodeFields, decodeRowValues]
      rw [decodeFields_encode]
      rfl
  | primaryKey + 1, value :: values, present => by
      change values[primaryKey]? = some (PhysicalCodec.Value.integer rowid) at present
      simp only [encodeFields, decodeRowValues]
      rw [PhysicalCodec.decodeValueField_recordField]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [decodeRowValues_encode rowid primaryKey values present]

def rowRecordFields (schema : Core.Schema) (row : Core.Row) :
    List RecordField :=
  if schema.hasHiddenRowid = true ∧
      row.values.length = schema.primaryKey + 1 then
    (row.values.take schema.primaryKey).map PhysicalCodec.Value.recordField
  else encodeFields schema.primaryKey row.values

def rowRecord? (schema : Core.Schema) (row : Core.Row) :
    Option PhysicalRecord :=
  let fields := rowRecordFields schema row
  if bound : recordHeaderSize (encodeRecordSerialTypes fields).length < 2 ^ 64 then
    some ⟨fields, by simpa using bound⟩
  else none

theorem rowRecord_fields {schema : Core.Schema} {row : Core.Row}
    {record : PhysicalRecord} (encoded : rowRecord? schema row = some record) :
    record.fields = rowRecordFields schema row := by
  unfold rowRecord? at encoded
  dsimp only at encoded
  split at encoded
  next bound => exact congrArg PhysicalRecord.fields (Option.some.inj encoded.symm)
  next unbounded => contradiction

/-- Old records omit trailing columns added with ALTER TABLE. Only literal
record defaults are usable here; a hidden rowid is reconstructed separately. -/
def completeFields (schema : Core.Schema) (fields : List RecordField) : Option (List RecordField) := do
  let omitted ← (schema.catalogColumns.drop fields.length).mapM fun column =>
    (column.defaultForRecord.toOption).map PhysicalCodec.Value.recordField
  return fields ++ omitted

theorem completeFields_full (schema : Core.Schema) (fields : List RecordField)
    (full : schema.catalogColumns.length ≤ fields.length) :
    completeFields schema fields = some fields := by
  simp [completeFields, List.drop_eq_nil_iff.mpr full]

theorem completeFields_record {schema : Core.Schema} {row : Core.Row}
    (valid : row.WellFormed schema) :
    completeFields schema (rowRecordFields schema row) = some (rowRecordFields schema row) := by
  apply completeFields_full
  unfold rowRecordFields
  split
  next standard =>
    simp only [List.length_map, List.length_take]
    simp only [Core.Schema.catalogColumns, standard.1, ↓reduceIte, List.length_take]
    have width := valid.1
    omega
  next legacy =>
    rw [encodeFields_length, valid.1]
    unfold Core.Schema.catalogColumns
    split <;> simp [Nat.min_le_right]

def decodeRowFieldsExact (schema : Core.Schema) (rowid : Core.Integer)
    (fields : List RecordField) : Option Core.Row :=
  if schema.hasHiddenRowid = true ∧ fields.length = schema.primaryKey then
    match decodeFields fields with
    | some visible =>
      match Core.Row.create schema (Core.readColumnValues schema.columns (visible ++ [.integer rowid])) with
      | .ok row => some row
      | .error _ => none
    | none => none
  else
    match decodeRowValues rowid schema.primaryKey fields with
    | some values =>
        match Core.Row.create schema (Core.readColumnValues schema.columns values) with
        | .ok row => some row
        | .error _ => none
    | none => none

theorem decodeRowFieldsExact_record {schema : Core.Schema} {row : Core.Row}
    (valid : row.WellFormed schema) :
    decodeRowFieldsExact schema row.rowid (rowRecordFields schema row) = some row := by
  unfold decodeRowFieldsExact rowRecordFields
  split
  next standard =>
    have bound : schema.primaryKey < row.values.length := by omega
    have takeLength : (row.values.take schema.primaryKey).length =
        schema.primaryKey := List.length_take_of_le (by omega)
    simp only [List.length_map, takeLength, standard.1, true_and,
      ↓reduceIte]
    rw [decodeFields_encode]
    simp only
    have keyValue : row.values[schema.primaryKey]'bound = .integer row.rowid := by
      simpa [List.getElem?_eq_getElem bound] using valid.2.1
    have reconstructed : row.values.take schema.primaryKey ++
        [.integer row.rowid] = row.values := by
      rw [← keyValue, List.take_append_getElem]
      exact List.take_of_length_le (by omega)
    rw [reconstructed, Core.readColumnValues_eq_self _ _ valid.2.2,
      Core.Row.create_self schema row valid]
  next legacy =>
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp valid.2.1
    have notStandard : ¬(schema.hasHiddenRowid = true ∧
        (encodeFields schema.primaryKey row.values).length = schema.primaryKey) := by
      simp only [encodeFields_length]
      omega
    simp only [notStandard, ↓reduceIte]
    rw [decodeRowValues_encode row.rowid schema.primaryKey row.values valid.2.1]
    simp only
    rw [Core.readColumnValues_eq_self _ _ valid.2.2, Core.Row.create_self schema row valid]

def decodeRowFields (schema : Core.Schema) (rowid : Core.Integer)
    (fields : List RecordField) : Option Core.Row := do
  decodeRowFieldsExact schema rowid (← completeFields schema fields)

theorem decodeRowFields_record {schema : Core.Schema} {row : Core.Row}
    (valid : row.WellFormed schema) :
    decodeRowFields schema row.rowid (rowRecordFields schema row) = some row := by
  unfold decodeRowFields
  rw [completeFields_record valid]
  exact decodeRowFieldsExact_record valid

def encodeCell? (schema : Core.Schema) (row : Core.Row) :
    Option (List UInt8) := do
  let record ← rowRecord? schema row
  if bound : record.encode.length < 2 ^ 64 then
    let payloadSize : U64Value := ⟨record.encode.length, by simpa using bound⟩
    some (encodeVarint payloadSize ++
      encodeVarint (signedInteger64Bits row.rowid) ++ record.encode)
  else none

def decodeRowCell (schema : Core.Schema) (input : List UInt8) :
    Option (Core.Row × List UInt8) := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (rowidBits, afterRowid) ← decodeVarint afterSize
  let (record, suffix) ← decodePhysicalRecord afterRowid
  if _sizeMatches : record.encode.length = payloadSize.val then
    let rowid := signedIntegerFromUnsigned .eight rowidBits
    let row ← decodeRowFields schema rowid record.fields
    some (row, suffix)
  else none

theorem decodeRowCell_encode {schema : Core.Schema} {row : Core.Row}
    {cell : List UInt8} (valid : row.WellFormed schema)
    (encoded : encodeCell? schema row = some cell)
    (suffix : List UInt8) :
    decodeRowCell schema (cell ++ suffix) = some (row, suffix) := by
  unfold encodeCell? at encoded
  cases recordResult : rowRecord? schema row with
  | none => simp [recordResult] at encoded
  | some record =>
      simp only [recordResult, Option.bind_eq_bind, Option.bind] at encoded
      split at encoded
      next payloadBound =>
        injection encoded with cellEqual
        subst cell
        unfold decodeRowCell
        simp only [List.append_assoc]
        rw [decodeVarint_encode]
        simp only [Option.bind_eq_bind, Option.bind]
        rw [decodeVarint_encode]
        simp only [Option.bind_eq_bind, Option.bind]
        rw [decodePhysicalRecord_encode]
        simp only [Option.bind_eq_bind, Option.bind]
        simp only [dif_pos True.intro]
        rw [signedIntegerFromBits_toBits]
        rw [show record.fields = rowRecordFields schema row from
          rowRecord_fields recordResult]
        rw [decodeRowFields_record valid]
      next payloadUnbounded => contradiction

end CoreRecord
end SQLeanite
