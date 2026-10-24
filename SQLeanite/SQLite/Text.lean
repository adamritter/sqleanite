import SQLeanite.SQLite.Numeric
import SQLeanite.SQLite.Limits

/-!
Pure ports of the SQLite 3.53.4 func.c string/blob operations. TEXT retains
original bytes, including malformed UTF-8, without Unicode normalization.
The pinned default SQLITE_MAX_LENGTH bounds stored and scalar result bytes.
-/
namespace SQLeanite.SQLite.Text

def isNull : Value → Bool | .null => true | _ => false

def toText (v : Value) : Except String String :=
  match v with
  | .blob bytes | .textBytes bytes => match String.fromUTF8? (ByteArray.mk bytes) with
      | some s => .ok s
      | none => .error "unsupported verified SQL: invalid UTF-8 BLOB to TEXT"
  | _ => .ok (toString v)

def bytes : Value → Array UInt8
  | .null => #[]
  | .blob b | .textBytes b => b
  | v => (toString v).toUTF8.data

def nulPrefix (s : String) : List Char := s.toList.takeWhile (· != '\x00')

def resultLimit : Nat := Limits.maxLength

/-- A checked String is only a compact representation choice. Invalid UTF-8
remains TEXT with the identical bytes, not a BLOB or a repaired string. -/
def fromBytes (bytes : Array UInt8) : Value :=
  match String.fromUTF8? (ByteArray.mk bytes) with
  | some string => .text string
  | none => .textBytes bytes

theorem fromBytes_invalid (bytes : Array UInt8)
    (invalid : String.fromUTF8? (ByteArray.mk bytes) = none) :
    fromBytes bytes = .textBytes bytes := by
  simp [fromBytes, invalid]

def checkedBytes (bytes : Array UInt8) : Except String Value :=
  if bytes.size ≤ resultLimit then .ok (fromBytes bytes)
  else .error "string or blob too big"

def continuation (byte : UInt8) : Bool := (byte &&& 0xc0) == 0x80

/-- SQLITE_SKIP_UTF8 preserves each original byte span, even for overlong,
surrogate and incomplete sequences. Isolated continuation bytes are single spans. -/
def characterSpansFuel : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, byte :: rest =>
      if byte == 0 then []
      else if byte < 0xc0 then [byte] :: characterSpansFuel fuel rest
      else
        let (extra, tail) := rest.span continuation
        (byte :: extra) :: characterSpansFuel fuel tail

def characterSpans (bytes : Array UInt8) : List (List UInt8) :=
  characterSpansFuel bytes.size bytes.toList

def checkedText (s : String) : Except String Value :=
  if s.utf8ByteSize ≤ resultLimit then .ok (.text s)
  else .error "string or blob too big"

def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 55 + n)

def hexBytes (b : Array UInt8) : String :=
  String.ofList (b.toList.flatMap fun c => [hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)])

/-- func.c:hexFunc includes the terminating byte in contextMalloc's limit
check. Check before building the doubled output. -/
def hex (v : Value) : Except String Value := do
  let source := bytes v
  Limits.check (2 * source.size) 1
  return .text (hexBytes source)

/-- SQL concatenation checks the total before allocating its result. -/
def append (left right : Value) : Except String Value := do
  let a := bytes left
  let b := bytes right
  Limits.check (a.size + b.size)
  return fromBytes (a ++ b)

/-- upper/lower share contextMalloc's extra terminator byte. -/
def asciiCase (upper : Bool) (v : Value) : Except String Value := do
  if isNull v then return .null
  let source := bytes v
  Limits.check source.size 1
  return fromBytes (source.map fun c =>
    if upper && 97 ≤ c && c ≤ 122 then c - 32
    else if !upper && 65 ≤ c && c ≤ 90 then c + 32 else c)

/-- The zero-origin offset and count from func.c:substrFunc, with exact signed
arithmetic even for Int64.min. TEXT counts characters, BLOB counts bytes. -/
def sliceRange (total : Nat) (start count : Int) : Nat × Nat := Id.run do
  let mut p := start
  let mut n := count
  if p < 0 then
    p := p + Int.ofNat total
    if p < 0 then
      n := if n < 0 then 0 else max 0 (n + p)
      p := 0
  else if p > 0 then p := p - 1
  else if n > 0 then n := n - 1
  if n < 0 then
    n := min p (-n)
    p := p - n
  return (p.toNat, n.toNat)

def slice {α : Type} (xs : List α) (start count : Int) : List α :=
  let (offset, size) := sliceRange xs.length start count
  (xs.drop offset).take size

def substr (v start : Value) (count : Value) : Except String Value := do
  if isNull v || isNull start || isNull count then return .null
  let p := Numeric.integer start
  let n := Numeric.integer count
  match v with
  -- sqlite3_value_blob returns a null pointer for a zero-length BLOB.
  | .blob b => return if b.isEmpty then .null else .blob (slice b.toList p n).toArray
  | _ => return fromBytes ((slice (characterSpans (bytes v)) p n).flatten.toArray)

def findSub {α : Type} [BEq α] (needle : List α) : List α → Nat → Nat
  | [], pos => if needle.isEmpty then pos else 0
  | xs@(_ :: rest), pos =>
      if needle.isPrefixOf xs then pos else findSub needle rest (pos + 1)

/-- instr compares bytes at character boundaries. Unlike SQLITE_SKIP_UTF8,
its text-mode increment skips continuation bytes even after an ASCII byte. -/
def findBytesFuel (textMode : Bool) (needle : List UInt8) :
    Nat → List UInt8 → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, haystack, position =>
      if needle.isPrefixOf haystack then position
      else match haystack with
        | [] => 0
        | _ :: rest => findBytesFuel textMode needle fuel
            (if textMode then rest.dropWhile continuation else rest) (position + 1)

def instr (haystack needle : Value) : Except String Value := do
  if isNull haystack || isNull needle then return .null
  let a := bytes haystack
  let b := bytes needle
  let textMode := match haystack, needle with | .blob _, .blob _ => false | _, _ => true
  return .integer (findBytesFuel textMode b.toList (a.size + 1) a.toList 1)

def trimBytesFuel (set : List (List UInt8)) : Nat → List UInt8 → List UInt8
  | 0, input => input
  | fuel + 1, input =>
      match set.find? (fun character => !character.isEmpty && character.isPrefixOf input) with
      | none => input
      | some character => trimBytesFuel set fuel (input.drop character.length)

def trim (left right : Bool) (v chars : Value) : Except String Value := do
  if isNull v || isNull chars then return .null
  let set := characterSpans (bytes chars)
  let source := (bytes v).toList
  let source := if left then trimBytesFuel set source.length source else source
  let source := if right then
    (trimBytesFuel (set.map List.reverse) source.length source.reverse).reverse else source
  return fromBytes source.toArray

/-- Byte matching also permits replacements inside malformed UTF-8 spans.
Every recursive step consumes at least one source byte. -/
def replaceBytesLoop (pattern replacement : List UInt8) :
    Nat → List UInt8 → Array UInt8 → Except String (Array UInt8)
  | 0, [], acc => .ok acc
  | 0, _ :: _, _ => .error "replace source traversal exhausted"
  | _ + 1, [], acc => .ok acc
  | fuel + 1, source@(byte :: rest), acc => do
      let matched := !pattern.isEmpty && pattern.isPrefixOf source
      let extra := if matched then replacement.length else 1
      if acc.size + extra > resultLimit then
        throw "string or blob too big"
      if matched then
        replaceBytesLoop pattern replacement fuel (source.drop pattern.length) (acc ++ replacement.toArray)
      else replaceBytesLoop pattern replacement fuel rest (acc.push byte)

def replace (v pattern replacement : Value) : Except String Value := do
  if isNull v || isNull pattern then return .null
  let source := bytes v
  let search := bytes pattern
  if search.isEmpty || search[0]? == some 0 then return fromBytes source
  if isNull replacement then return .null
  Limits.check source.size 1
  return fromBytes (← replaceBytesLoop search.toList (bytes replacement).toList
    source.size source.toList #[])

def concatBytes (separator : Array UInt8) (values : List Value) : Except String Value := do
  let mut result := #[]
  let mut seen := false
  for v in values do
    unless isNull v do
      let source := bytes v
      let sep := if seen then separator else #[]
      if result.size + sep.size + source.size > resultLimit then
        throw "string or blob too big"
      result := result ++ sep ++ source
      seen := true
  return fromBytes result

def concat (separator : String) (values : List Value) : Except String Value :=
  concatBytes separator.toUTF8.data values

def concatWs (separator : Value) (values : List Value) : Except String Value := do
  if isNull separator then return .null
  concatBytes (bytes separator) values

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else none

/-- Ignored characters are allowed between complete byte pairs only. -/
def unicodeScalar (n : Nat) : Nat :=
  if n == 65534 || n == 65535 then 65533 else n

/-- utf.c:sqlite3Utf8Read, including its nonstandard handling of malformed
BLOB bytes and 32-bit wraparound. This observes bytes without creating TEXT. -/
def firstCodepoint : List UInt8 → Option Nat
  | [] => none
  | first :: rest =>
      let c := first.toNat
      if c == 0 then none
      else if c < 192 then some c
      else
        let initial := if c < 224 then c % 32 else if c < 240 then c % 16
          else if c < 248 then c % 8 else if c < 252 then c % 4
          else if c < 254 then c % 2 else 0
        let continuation := rest.takeWhile (fun b => b.toNat / 64 == 2)
        let value := (continuation.foldl (fun n b => n * 64 + UInt32.ofNat (b.toNat % 64))
          (UInt32.ofNat initial)).toNat
        some (if value < 128 || (55296 ≤ value && value ≤ 57343) then 65533
          else unicodeScalar value)

def unicode (v : Value) : Except String Value :=
  .ok (match firstCodepoint (bytes v).toList with
    | none => .null
    -- func.c passes the unsigned decoder result to sqlite3_result_int.
    | some n => .integer (Int32.ofInt (Int.ofNat n)).toInt)

/-- UNHEX ignores complete decoded non-hex characters between byte pairs.
Its ignore set uses the supplied byte length, including bytes after NUL. -/
def codepointsFuel (stopAtNul : Bool) : Nat → List UInt8 → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, source@(byte :: rest) =>
      if stopAtNul && byte == 0 then []
      else (firstCodepoint source).getD 0 :: codepointsFuel stopAtNul fuel
        (if byte < 0xc0 then rest else rest.dropWhile continuation)

def unhexCodes (ignored : List Nat) : List Nat → Array UInt8 → Option (Array UInt8)
  | [], acc => some acc
  | c :: rest, acc =>
      match hexValue (Char.ofNat c) with
      | none => if ignored.contains c then unhexCodes ignored rest acc else none
      | some high => match rest with
          | [] => none
          | d :: tail => match hexValue (Char.ofNat d) with
              | none => none
              | some low => unhexCodes ignored tail (acc.push (UInt8.ofNat (16 * high + low)))

def unhex (v ignored : Value) : Except String Value := do
  if isNull v || isNull ignored then return .null
  let source := bytes v
  let pass := bytes ignored
  return match unhexCodes (codepointsFuel false pass.size pass.toList)
      (codepointsFuel true source.size source.toList) #[] with
    | none => .null
    | some result => .blob result

/-- SQLite's CHAR encodes surrogate values too, retaining their UTF-8 bytes. -/
def encodeCodepoint (n : Nat) : Array UInt8 :=
  let byte := UInt8.ofNat
  if n < 128 then #[byte n]
  else if n < 2048 then #[byte (192 + n / 64), byte (128 + n % 64)]
  else if n < 65536 then #[byte (224 + n / 4096), byte (128 + n / 64 % 64), byte (128 + n % 64)]
  else #[byte (240 + n / 262144), byte (128 + n / 4096 % 64),
    byte (128 + n / 64 % 64), byte (128 + n % 64)]

def charValue (values : List Value) : Except String Value := do
  let mut result := #[]
  for v in values do
    let i := Numeric.integer v
    let n := if i < 0 || i > 1114111 then 65533 else i.toNat
    result := result ++ encodeCodepoint n
  checkedBytes result

def quote (v : Value) : Except String Value :=
  match v with
  | .text _ | .textBytes _ => do
      let source := (bytes v).toList.takeWhile (· != 0)
      let escaped := source.foldl (fun size byte => size + if byte == 39 then 2 else 1) 2
      Limits.check escaped 1
      return fromBytes (([39] ++ source.flatMap
        (fun byte => if byte == 39 then [39, 39] else [byte]) ++ [39]).toArray)
  | .blob b => do
      Limits.check (2 * b.size + 3) 1
      return .text ("X'" ++ hexBytes b ++ "'")
  | _ => checkedText (match v with
      | .null => "NULL"
      | .integer i => toString i
      | .real r => if r.isInf then (if r < 0.0 then "-9.0e+999" else "9.0e+999") else toString v
      | .blob b => "X'" ++ hexBytes b ++ "'"
      | .text _ | .textBytes _ => "")

def zeroblob (v : Value) : Except String Value :=
  let n := (Numeric.integer v).toNat
  if n ≤ resultLimit then .ok (.blob (Array.replicate n 0))
  else .error "string or blob too big"

def sign (v : Value) : Value :=
  match Numeric.applyAffinity v with
  | v@(.integer _) | v@(.real _) =>
      let r := Numeric.real v
      .integer (if r < 0.0 then -1 else if r > 0.0 then 1 else 0)
  | _ => .null

/-- SQLite min chooses the last equal argument; max chooses the first.
The chosen storage class and bit representation are preserved. -/
def minmax (maximum : Bool) (first : Value) (rest : List Value) : Value :=
  if isNull first || rest.any isNull then .null
  else rest.foldl (fun best v =>
    let order := best.compare v
    if (if maximum then order == .lt else order != .lt) then v else best) first

theorem slice_length_le {α : Type} (xs : List α) (start count : Int) :
    (slice xs start count).length ≤ xs.length := by
  simp only [slice, List.length_take, List.length_drop]
  omega

theorem findSub_empty {α : Type} [BEq α] (haystack : List α) (pos : Nat) :
    findSub [] haystack pos = pos := by
  cases haystack <;> simp [findSub]

theorem substr_null (start count : Value) : substr .null start count = .ok .null := by
  rfl

theorem minmax_null (maximum : Bool) (rest : List Value) :
    minmax maximum .null rest = .null := by simp [minmax, isNull]

theorem unhexCodes_empty (ignored : List Nat) (acc : Array UInt8) :
    unhexCodes ignored [] acc = some acc := rfl

end SQLeanite.SQLite.Text
