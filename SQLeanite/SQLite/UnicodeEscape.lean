import SQLeanite.SQLite.Text

/-! Byte-for-byte ports of func.c:unistrFunc and printf.c's %#Q quoting.
The pinned UTF-8 encoder permits surrogates and masks high bits of 32-bit
escape values. These bytes must not pass through Lean's Unicode repair. -/
namespace SQLeanite.SQLite.UnicodeEscape

/-- Consume exactly the specified number of ASCII hexadecimal digits. -/
def readHex : Nat → List UInt8 → Nat → Option (Nat × List UInt8)
  | 0, rest, value => some (value, rest)
  | _ + 1, [], _ => none
  | count + 1, byte :: rest, value => do
      let digit ← Text.hexValue (Char.ofNat byte.toNat)
      readHex count rest (value * 16 + digit)

/-- utf.c:sqlite3AppendOneUtf8Character retains only three high bits in
its four-byte prefix, even for escape values above the Unicode range. -/
def encode (value : Nat) : Array UInt8 :=
  if value < 65536 then Text.encodeCodepoint value
  else #[UInt8.ofNat (240 + value / 262144 % 8),
    UInt8.ofNat (128 + value / 4096 % 64),
    UInt8.ofNat (128 + value / 64 % 64), UInt8.ofNat (128 + value % 64)]

/-- strchr stops searching at a source NUL; the remaining original byte
suffix is copied unchanged. NUL produced by decoding an escape is different:
it does not stop decoding subsequent source bytes. -/
def decodeFuel : Nat → List UInt8 → Array UInt8 → Except String (Array UInt8)
  | _, [], result => .ok result
  | 0, _ :: _, _ => .error "Unicode escape input depth exhausted"
  | fuel + 1, source@(byte :: rest), result => do
      if byte == 0 then return result ++ source.toArray
      if byte != 92 then return ← decodeFuel fuel rest (result.push byte)
      match rest with
      | [] => throw "invalid Unicode escape"
      | next :: tail =>
          if next == 92 then return ← decodeFuel fuel tail (result.push 92)
          let decoded := if (Text.hexValue (Char.ofNat next.toNat)).isSome then readHex 4 rest 0
            else if next == 43 then readHex 6 tail 0
            else if next == 117 then readHex 4 tail 0
            else if next == 85 then readHex 8 tail 0
            else none
          let some (value, tail) := decoded | throw "invalid Unicode escape"
          decodeFuel fuel tail (result ++ encode value)

def unistr (value : Value) : Except String Value := do
  if Text.isNull value then return .null
  let source := Text.bytes value
  Text.checkedBytes (← decodeFuel source.size source.toList #[])

def quoteByte (byte : UInt8) : List UInt8 :=
  if byte == 39 || byte == 92 then [byte, byte]
  else if byte ≤ 31 then
    let low := byte.toNat % 16
    [92, 117, 48, 48, UInt8.ofNat (48 + byte.toNat / 16),
      UInt8.ofNat (if low < 10 then 48 + low else 87 + low)]
  else [byte]

def quote (value : Value) : Except String Value := do
  match value with
  | .text _ | .textBytes _ =>
      let source := (Text.bytes value).toList.takeWhile (· != 0)
      if !(source.any (· ≤ 31)) then return ← Text.quote value
      let size := source.foldl (fun size byte => size + (quoteByte byte).length) 10
      Limits.check size 1
      return Text.fromBytes (([117, 110, 105, 115, 116, 114, 40, 39] ++
        source.flatMap quoteByte ++ [39, 41]).toArray)
  | _ => Text.quote value

theorem unistr_null : unistr .null = .ok .null := rfl

theorem decodeFuel_source_nul (fuel : Nat) (rest : List UInt8) (result : Array UInt8) :
    decodeFuel (fuel + 1) (0 :: rest) result = .ok (result ++ (0 :: rest).toArray) := rfl

theorem quote_blob (bytes : Array UInt8) :
    quote (.blob bytes) = Text.quote (.blob bytes) := rfl

end SQLeanite.SQLite.UnicodeEscape
