import SQLeanite.SQLite.Numeric

/-!
Pure ports of the SQLite 3.53.4 func.c string/blob operations. TEXT is still
Lean UTF-8: conversions producing invalid UTF-8 are explicitly rejected.
The existing Core value limit also bounds newly allocated scalar results.
-/
namespace SQLeanite.SQLite.Text

def isNull : Value → Bool | .null => true | _ => false

def toText (v : Value) : Except String String :=
  match v with
  | .blob bytes => match String.fromUTF8? (ByteArray.mk bytes) with
      | some s => .ok s
      | none => .error "unsupported verified SQL: invalid UTF-8 BLOB to TEXT"
  | _ => .ok (toString v)

def bytes : Value → Array UInt8
  | .null => #[]
  | .blob b => b
  | v => (toString v).toUTF8.data

def nulPrefix (s : String) : List Char := s.toList.takeWhile (· != '\x00')

def resultLimit : Nat := 999999

def checkedText (s : String) : Except String Value :=
  if s.utf8ByteSize ≤ resultLimit then .ok (.text s)
  else .error "unsupported verified SQL: scalar text exceeds Core value limit"

def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 55 + n)

def hexBytes (b : Array UInt8) : String :=
  String.ofList (b.toList.flatMap fun c => [hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)])

def hex (v : Value) : Except String Value := checkedText (hexBytes (bytes v))

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
  | _ => return .text (String.ofList (slice (nulPrefix (← toText v)) p n))

def findSub {α : Type} [BEq α] (needle : List α) : List α → Nat → Nat
  | [], pos => if needle.isEmpty then pos else 0
  | xs@(_ :: rest), pos =>
      if needle.isPrefixOf xs then pos else findSub needle rest (pos + 1)

def instr (haystack needle : Value) : Except String Value := do
  if isNull haystack || isNull needle then return .null
  if (bytes needle).isEmpty then return .integer 1
  match haystack, needle with
  | .blob a, .blob b => return .integer (findSub b.toList a.toList 1)
  | _, _ => return .integer (findSub (← toText needle).toList (← toText haystack).toList 1)

def trim (left right : Bool) (v chars : Value) : Except String Value := do
  if isNull v || isNull chars then return .null
  let set := nulPrefix (← toText chars)
  let source := (← toText v).toList
  let source := if left then source.dropWhile set.contains else source
  let source := if right then (source.reverse.dropWhile set.contains).reverse else source
  return .text (String.ofList source)

/-- Consumption decreases at least one source character per step. Check the
output byte bound before append, including for expanding replacements. -/
def replaceLoop (pattern replacement : List Char) (replacementBytes : Nat) :
    Nat → List Char → Array Char → Nat → Except String String
  | 0, [], acc, _ => .ok (String.ofList acc.toList)
  | 0, _ :: _, _, _ => .error "replace source traversal exhausted"
  | _ + 1, [], acc, _ => .ok (String.ofList acc.toList)
  | fuel + 1, source@(c :: rest), acc, size => do
      let matched := !pattern.isEmpty && pattern.isPrefixOf source
      let extra := if matched then replacementBytes else c.utf8Size
      if size + extra > resultLimit then
        throw "unsupported verified SQL: scalar text exceeds Core value limit"
      if matched then
        replaceLoop pattern replacement replacementBytes fuel (source.drop pattern.length)
          (acc ++ replacement.toArray) (size + extra)
      else replaceLoop pattern replacement replacementBytes fuel rest (acc.push c) (size + extra)

def replace (v pattern replacement : Value) : Except String Value := do
  if isNull v || isNull pattern then return .null
  let s ← toText v
  let p ← toText pattern
  -- SQLite returns the original TEXT before inspecting a NULL replacement.
  if (nulPrefix p).isEmpty then return .text s
  if isNull replacement then return .null
  let r ← toText replacement
  return .text (← replaceLoop p.toList r.toList r.utf8ByteSize s.length s.toList #[] 0)

def concat (separator : String) (values : List Value) : Except String Value := do
  let mut result := ""
  let mut seen := false
  for v in values do
    unless isNull v do
      let s ← toText v
      let sep := if seen then separator else ""
      if result.utf8ByteSize + sep.utf8ByteSize + s.utf8ByteSize > resultLimit then
        throw "unsupported verified SQL: scalar text exceeds Core value limit"
      result := result ++ sep ++ s
      seen := true
  return .text result

def concatWs (separator : Value) (values : List Value) : Except String Value := do
  if isNull separator then return .null
  concat (← toText separator) values

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else none

/-- Ignored characters are allowed between complete byte pairs only. -/
def unicodeScalar (n : Nat) : Nat :=
  if n == 65534 || n == 65535 then 65533 else n

def unhexChars (ignored : List Char) : List Char → Array UInt8 → Option (Array UInt8)
  | [], acc => some acc
  | c :: rest, acc =>
      match hexValue c with
      | none => if ignored.any (fun d => unicodeScalar d.toNat == unicodeScalar c.toNat) then
          unhexChars ignored rest acc else none
      | some hi => match rest with
          | [] => none
          | d :: tail => match hexValue d with
              | none => none
              | some lo => unhexChars ignored tail (acc.push (UInt8.ofNat (16 * hi + lo)))

def unhex (v ignored : Value) : Except String Value := do
  if isNull v || isNull ignored then return .null
  let source := nulPrefix (← toText v)
  let pass := (← toText ignored).toList
  return match unhexChars pass source #[] with | none => .null | some b => .blob b

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

def charValue (values : List Value) : Except String Value := do
  let mut chars := #[]
  for v in values do
    let i := Numeric.integer v
    let n := if i < 0 || i > 1114111 then 65533 else i.toNat
    if 55296 ≤ n && n ≤ 57343 then
      throw "unsupported verified SQL: surrogate codepoint creates invalid UTF-8"
    chars := chars.push (Char.ofNat n)
  checkedText (String.ofList chars.toList)

def quote (v : Value) : Except String Value :=
  checkedText (match v with
    | .null => "NULL"
    | .integer i => toString i
    | .real r => if r.isInf then (if r < 0.0 then "-9.0e+999" else "9.0e+999") else toString v
    | .blob b => "X'" ++ hexBytes b ++ "'"
    | .text s => "'" ++ String.ofList ((nulPrefix s).flatMap fun c =>
        if c == '\'' then ['\'', '\''] else [c]) ++ "'")

def zeroblob (v : Value) : Except String Value :=
  let n := (Numeric.integer v).toNat
  if n ≤ resultLimit then .ok (.blob (Array.replicate n 0))
  else .error "unsupported verified SQL: scalar blob exceeds Core value limit"

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

theorem unhexChars_empty (ignored : List Char) (acc : Array UInt8) :
    unhexChars ignored [] acc = some acc := rfl

end SQLeanite.SQLite.Text
