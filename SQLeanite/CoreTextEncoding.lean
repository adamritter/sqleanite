import SQLeanite.CoreRecord
import SQLeanite.SQLite.StoredText
import SQLeanite.SQLite.TextEncoding

namespace SQLeanite.CoreTextEncoding

/-- Transcode only TEXT after physical payload/serial-type validation.
INTEGER, REAL, BLOB and NULL fields keep their exact original representation. -/
def field (encoding : Nat) (original : FileFormat.RecordField) : Option FileFormat.RecordField :=
  if encoding != 2 && encoding != 3 then some original else
    match original with
    | .text _ payload =>
        let bytes := (SQLite.TextEncoding.fromStorage encoding payload.bytes.toArray).toList
        if bound : bytes.length < PhysicalCodec.textByteLimit then
          some (PhysicalCodec.Text.recordField ⟨bytes,bound⟩)
        else none
    | _ => some original

def fields (encoding : Nat) (original : List FileFormat.RecordField) : Option (List FileFormat.RecordField) :=
  if encoding != 2 && encoding != 3 then some original else original.mapM (field encoding)

/-- The callback runs only after the record was physically validated and its
logical row decoded. Reversible values need no extra storage copy. -/
def origins (encoding : Nat) (schema : Core.Schema) (row : Core.Row)
    (physical : List FileFormat.RecordField) : List SQLite.StoredText :=
  physical.zipIdx.filterMap fun (field,position) => do
    let .text _ payload := field | none
    let .text decoded ← row.values[position]? | none
    let bytes := payload.bytes.toArray
    if SQLite.TextEncoding.toStorage encoding decoded.bytes.toArray == bytes then none else
      some { table := schema.name, rowid := row.rowid.value, column := position, encoding, bytes }

theorem field_utf8 (original : FileFormat.RecordField) : field 1 original = some original := rfl

theorem fields_utf8 (original : List FileFormat.RecordField) : fields 1 original = some original := by
  rfl

end SQLeanite.CoreTextEncoding
