import SQLeanite.SQLite.JsonText

namespace SQLeanite.SQLite.JsonReplace
open JsonValid

/-- jsonFunctionArgToBlob encodes ordinary TEXT as raw JSONB string bytes;
only TEXT carrying the actual JSON subtype is parsed as JSON input. -/
def argument (input : ScalarValue) : Except String (Array UInt8) := do
  match input.value with
  | .null => return #[0]
  | .integer _ => return JsonAccess.node 3 (Text.bytes input.value)
  | .real _ =>
      let bytes := Text.bytes input.value
      let bytes := if byte bytes 0 == 73 then "9e999".toUTF8.data
        else if byte bytes 0 == 45 && byte bytes 1 == 73 then "-9e999".toUTF8.data else bytes
      return JsonAccess.node 5 bytes
  | .text _ | .textBytes _ =>
      if input.subtype == 74 then
        let value ← JsonBinary.evaluate input.value
        let .blob bytes := value | throw "malformed JSON"
        return bytes
      return JsonAccess.node 10 (Text.bytes input.value)
  | .blob bytes =>
      unless blobLooks bytes do throw "JSON cannot hold BLOB values"
      return bytes

/-- Replacing a nested value changes only that value and its ancestor headers.
The same in-place width preservation used by merge patch applies here. -/
def replaceAt (input : Array UInt8) (pos : Nat) (insert : Array UInt8) :
    Except String (Array UInt8) := do
  let location ← JsonRemove.locate input pos (4*input.size+4) 0 0
  let (header,size) := (payload input pos).getD (0,0)
  let initial := JsonPatch.edit input pos (header+size) insert true
  let mut bytes := initial.bytes
  let mut delta := initial.delta
  for ancestor in location.ancestors do
    if delta != 0 then
      let size := ((Int.ofNat ancestor.size + delta) % (2^32)).toNat
      let replacement := JsonExtract.reservedHeader (byte input ancestor.pos % 16) size
      let updated := JsonPatch.edit bytes ancestor.pos ancestor.header replacement false
      bytes := updated.bytes
      delta := delta + updated.delta
  return bytes

def changes (input : Array UInt8) : List ScalarValue → Except String (Array UInt8)
  | [] => .ok input
  | pathValue :: value :: rest => do
      if Text.isNull pathValue.value then return ← changes input rest
      let path := Text.bytes pathValue.value
      unless byte path 0 == 36 do throw (JsonAccess.pathError path)
      let insert ← argument value
      let bytes ← if byte path 1 == 0 then pure (JsonPatch.edit input 0 input.size insert true).bytes
        else do
          let pos ← JsonAccess.select input (some pathValue.value)
          match pos with
          | none => pure input
          | some pos => replaceAt input pos insert
      changes bytes rest
  | _ => .error "json_replace() needs an odd number of arguments"

def evaluate (binary : Bool) (inputs : List ScalarValue) : Except String ScalarValue := do
  let value :: rest := inputs | return JsonText.plain .null
  unless inputs.length % 2 == 1 do throw "json_replace() needs an odd number of arguments"
  let input ← JsonBinary.evaluate value.value
  let .blob bytes := input | return JsonText.plain .null
  let bytes ← changes bytes rest
  if binary then return JsonText.plain (.blob bytes)
  JsonText.render bytes

end SQLeanite.SQLite.JsonReplace
namespace SQLeanite.SQLite.JsonReplace

theorem argument_null (tag : UInt8) : argument ⟨.null,tag⟩ = .ok #[0] := rfl

theorem argument_ordinary_text (bytes : Array UInt8) (tag : UInt8) (ordinary : tag ≠ 74) :
    argument ⟨.textBytes bytes,tag⟩ = .ok (JsonAccess.node 10 bytes) := by
  simp [argument, ordinary, Text.bytes, pure, Except.pure]

theorem argument_admitted_blob (bytes : Array UInt8) (tag : UInt8)
    (admitted : JsonValid.blobLooks bytes = true) :
    argument ⟨.blob bytes,tag⟩ = .ok bytes := by
  simp [argument, admitted, pure, Except.pure] <;> rfl

theorem argument_invalid_blob (bytes : Array UInt8) (tag : UInt8)
    (invalid : JsonValid.blobLooks bytes = false) :
    argument ⟨.blob bytes,tag⟩ = .error "JSON cannot hold BLOB values" := by
  simp [argument, invalid, pure, Except.pure] <;> rfl

theorem changes_none (bytes : Array UInt8) : changes bytes [] = .ok bytes := rfl

theorem changes_null_path (bytes : Array UInt8) (tag : UInt8)
    (value : ScalarValue) (rest : List ScalarValue) :
    changes bytes (⟨.null,tag⟩ :: value :: rest) = changes bytes rest := by
  simp [changes, Text.isNull, bind, Except.bind]

theorem evaluate_no_arguments (binary : Bool) :
    evaluate binary [] = .ok (JsonText.plain .null) := rfl

theorem evaluate_even (binary : Bool) (first : ScalarValue) (rest : List ScalarValue)
    (even : (first :: rest).length % 2 ≠ 1) :
    evaluate binary (first :: rest) = .error "json_replace() needs an odd number of arguments" := by
  have odd : (rest.length + 1) % 2 ≠ 1 := by simpa using even
  simp [evaluate, odd, pure, Except.pure] <;> rfl

end SQLeanite.SQLite.JsonReplace
