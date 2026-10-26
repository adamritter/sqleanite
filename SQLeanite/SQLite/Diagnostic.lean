import SQLeanite.SQLite.Text

/-! Lossless byte diagnostics carried through the existing Except String API.
UTF-8 messages remain plain strings. Non-UTF-8 messages use a reserved NUL-led
hex envelope until the executable writes stderr bytes. This encodes only the
message supplied by the failing operation; it does not inspect SQL or results. -/
namespace SQLeanite.SQLite.Diagnostic

def envelope : String := "\x00SQLeanite/error-bytes/"

def ofBytes (data : Array UInt8) : String :=
  match String.fromUTF8? ⟨data⟩ with
  | some text => if text.startsWith envelope then envelope ++ Text.hexBytes data else text
  | none => envelope ++ Text.hexBytes data

def bytes (message : String) : Array UInt8 :=
  if message.startsWith envelope then
    let encoded := (message.drop envelope.length).toString.toList.map Char.toNat
    (Text.unhexCodes [] encoded #[]).getD message.toUTF8.data
  else message.toUTF8.data

theorem ofBytes_utf8 (data : Array UInt8) (message : String)
    (valid : String.fromUTF8? ⟨data⟩ = some message)
    (ordinary : message.startsWith envelope = false) : ofBytes data = message := by
  simp [ofBytes, valid, ordinary]

theorem bytes_ordinary (message : String)
    (ordinary : message.startsWith envelope = false) : bytes message = message.toUTF8.data := by
  simp [bytes, ordinary]

theorem ofBytes_nonutf8 (data : Array UInt8)
    (invalid : String.fromUTF8? ⟨data⟩ = none) : ofBytes data = envelope ++ Text.hexBytes data := by
  simp [ofBytes, invalid]

end SQLeanite.SQLite.Diagnostic
