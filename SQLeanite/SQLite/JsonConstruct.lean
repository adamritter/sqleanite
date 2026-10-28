import SQLeanite.SQLite.JsonText
import SQLeanite.SQLite.Format

namespace SQLeanite.SQLite.JsonConstruct

def appendValue (input : ScalarValue) : Except String (Array UInt8) := do
  match input.value with
  | .null => return "null".toUTF8.data
  | .integer _ => return Text.bytes input.value
  | .real _ => return Text.bytes (← Format.evaluate [.text "%!0.17g", input.value])
  | .text _ | .textBytes _ =>
      let bytes := Text.bytes input.value
      return if input.subtype == 74 then bytes else JsonPretty.quoted bytes
  | .blob bytes =>
      unless JsonValid.blobLooks bytes do throw "JSON cannot hold BLOB values"
      return Text.bytes (← JsonText.render bytes).value

def finish (binary : Bool) (bytes : Array UInt8) : ScalarValue :=
  if binary then ⟨.blob (JsonExtract.unchecked bytes (4*bytes.size+4) 0 0).data,74,1,none⟩
  else JsonText.json bytes

def quote (input : ScalarValue) : Except String ScalarValue := do
  return finish false (← appendValue input)

/-- After a buffer error SQLite skips container children but still visits
primitive JSONB nodes. Their malformed flags can replace a prior BLOB error. -/
def appendAfterError (error : String) (input : ScalarValue) : String :=
  match input.value with
  | .blob bytes =>
      if JsonValid.blobLooks bytes && JsonValid.byte bytes 0 % 16 < 11 then
        match appendValue input with
        | .error message => message
        | .ok _ => error
      else error
  | _ => error

def array (binary : Bool) (inputs : List ScalarValue) : Except String ScalarValue := do
  let mut out := #[91]
  let mut first := true
  let mut error : Option String := none
  for input in inputs do
    if !first then out := out.push 44
    match error with
    | some message => error := some (appendAfterError message input)
    | none =>
        match appendValue input with
        | .error message => error := some message
        | .ok data => out := out ++ data
    first := false
  if let some message := error then throw message
  return finish binary (out.push 93)

def objectMembers : List ScalarValue → Array UInt8 → Bool → Option String → Except String (Array UInt8)
  | [], out, _, none => .ok (out.push 125)
  | [], _, _, some error => .error error
  | label :: value :: rest, out, first, error => do
      unless (match label.value with | .text _ | .textBytes _ => true | _ => false) do
        throw "json_object() labels must be TEXT"
      let out := if first then out else out.push 44
      let out := out ++ JsonPretty.quoted (Text.bytes label.value) ++ #[58]
      match error with
      | some message => objectMembers rest out false (some (appendAfterError message value))
      | none =>
          match appendValue value with
          | .error message => objectMembers rest out false (some message)
          | .ok data => objectMembers rest (out ++ data) false none
  | _, _, _, _ => .error "json_object() requires an even number of arguments"

def object (binary : Bool) (inputs : List ScalarValue) : Except String ScalarValue := do
  unless inputs.length % 2 == 0 do throw "json_object() requires an even number of arguments"
  return finish binary (← objectMembers inputs #[123] true none)

end SQLeanite.SQLite.JsonConstruct

namespace SQLeanite.SQLite.JsonConstruct

theorem finish_subtype (binary : Bool) (bytes : Array UInt8) :
    (finish binary bytes).subtype = 74 := by
  cases binary <;> rfl

theorem quote_null (subtype : UInt8) :
    quote ⟨.null, subtype,1,none⟩ = .ok (JsonText.json "null".toUTF8.data) := rfl

theorem append_tagged_text (bytes : Array UInt8) :
    appendValue ⟨.textBytes bytes,74,1,none⟩ = .ok bytes := rfl

theorem append_invalid_blob (bytes : Array UInt8) (subtype : UInt8)
    (invalid : JsonValid.blobLooks bytes = false) :
    appendValue ⟨.blob bytes, subtype,1,none⟩ = .error "JSON cannot hold BLOB values" := by
  simp [appendValue, invalid, pure, Except.pure] <;> rfl

theorem array_empty : array false [] = .ok (JsonText.json #[91,93]) := rfl

theorem object_odd (binary : Bool) (inputs : List ScalarValue)
    (odd : inputs.length % 2 ≠ 0) :
    object binary inputs = .error "json_object() requires an even number of arguments" := by
  simp [object, odd, pure, Except.pure] <;> rfl

theorem object_null_label (subtype : UInt8) (value : ScalarValue) (rest : List ScalarValue)
    (out : Array UInt8) (first : Bool) (error : Option String) :
    objectMembers (⟨.null, subtype,1,none⟩ :: value :: rest) out first error =
      .error "json_object() labels must be TEXT" := by
  simp [objectMembers, pure, Except.pure] <;> rfl

end SQLeanite.SQLite.JsonConstruct
