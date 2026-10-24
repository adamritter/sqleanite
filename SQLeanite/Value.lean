import Std
import SQLeanite.SQLite.FloatCodec

namespace SQLeanite

/-- SQLite's five storage classes. TEXT retains either a valid Lean string or
its exact bytes; both representations have the same SQL storage class. -/
inductive Value where
  | null
  | integer (value : Int)
  | real (value : Float)
  | text (value : String)
  | textBytes (value : Array UInt8)
  | blob (value : Array UInt8)
  deriving Repr, Inhabited

/-- SQLite 3.53.4's default 17-digit REAL representation. -/
private def formatFloat : Float → String := SQLite.FloatCodec.render

instance : ToString Value where
  toString
    | .null => ""
    | .integer i => toString i
    | .real f => formatFloat f
    | .text s => s
    | .textBytes b => "CAST(X'" ++ String.join (b.toList.map fun x =>
          let digit (n : Nat) := Char.ofNat (if n < 10 then 48 + n else 55 + n)
          String.ofList [digit (x.toNat / 16), digit (x.toNat % 16)]) ++ "' AS TEXT)"
    | .blob b => "X'" ++ String.join (b.toList.map fun x =>
          let hexDigit (n : Nat) := Char.ofNat (if n < 10 then '0'.toNat + n else 'A'.toNat + n - 10)
          String.mk [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)]) ++ "'"

/-- Text returned through the SQLite-style client interface. SQLite keeps BLOBs
typed internally but exposes their bytes to clients rather than SQL-literal
spelling. Valid UTF-8 blobs can therefore round-trip through the text protocol;
other blobs retain an unambiguous hexadecimal representation. -/
def Value.clientText : Value → String
  | value@(.blob bytes) => String.fromUTF8? (ByteArray.mk bytes) |>.getD (toString value)
  | value => toString value

/-- Compare an exact SQLite integer with a binary64 value without first
rounding the integer to binary64.  That rounding loses the distinction between
`Int64.max` and `2^63`, and can also lose nearby low-order bits. -/
private def compareIntegerReal (integer : Int) (real : Float) : Ordering :=
  if real >= Float.ofInt 9223372036854775808 then .lt
  else if real < Float.ofInt (-9223372036854775808) then .gt
  else
    let truncated := real.toInt64.toInt
    if integer < truncated then .lt
    else if truncated < integer then .gt
    else
      let exact := Float.ofInt truncated
      if exact < real then .lt else if real < exact then .gt else .eq

def Value.beq : Value → Value → Bool
  | .null, .null => true
  | .integer a, .integer b => a == b
  | .real a, .real b => a == b
  | .integer a, .real b => compareIntegerReal a b == .eq
  | .real a, .integer b => compareIntegerReal b a == .eq
  | .text a, .text b => a == b
  | .textBytes a, .textBytes b => a == b
  | .text a, .textBytes b => a.toUTF8.data == b
  | .textBytes a, .text b => a == b.toUTF8.data
  | .blob a, .blob b => a == b
  | _, _ => false

instance : BEq Value := ⟨Value.beq⟩

/-- SQL truth has a third, unknown value, represented separately from values. -/
inductive Truth where
  | false
  | true
  | unknown
  deriving Repr, DecidableEq, Inhabited

namespace Truth

def not : Truth → Truth
  | .false => .true
  | .true => .false
  | .unknown => .unknown

def and : Truth → Truth → Truth
  | .false, _ => .false
  | _, .false => .false
  | .true, x => x
  | x, .true => x
  | .unknown, .unknown => .unknown

def or : Truth → Truth → Truth
  | .true, _ => .true
  | _, .true => .true
  | .false, x => x
  | x, .false => x
  | .unknown, .unknown => .unknown

/-- SQL CHECK constraints accept TRUE and UNKNOWN, rejecting exactly FALSE. -/
def satisfiesCheck : Truth → Bool
  | .false => Bool.false
  | .true | .unknown => Bool.true

theorem satisfiesCheck_iff (truth : Truth) :
    truth.satisfiesCheck = Bool.true ↔ truth ≠ Truth.false := by
  cases truth <;> simp [satisfiesCheck]

theorem not_not (a : Truth) : not (not a) = a := by cases a <;> rfl
theorem and_comm (a b : Truth) : and a b = and b a := by cases a <;> cases b <;> rfl
theorem or_comm (a b : Truth) : or a b = or b a := by cases a <;> cases b <;> rfl
theorem and_assoc (a b c : Truth) : and (and a b) c = and a (and b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem or_assoc (a b c : Truth) : or (or a b) c = or a (or b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem deMorgan_and (a b : Truth) : not (and a b) = or (not a) (not b) := by
  cases a <;> cases b <;> rfl
theorem deMorgan_or (a b : Truth) : not (or a b) = and (not a) (not b) := by
  cases a <;> cases b <;> rfl

end Truth

def Value.truth : Value → Truth
  | .null => .unknown
  | .integer 0 => .false
  | .integer _ => .true
  | .real f => if f == 0.0 then .false else .true
  | .text s =>
      match s.toInt? with
      | some 0 => .false
      | some _ => .true
      | none => .false
  | .textBytes bytes =>
      match (String.ofList (bytes.toList.map (fun byte => Char.ofNat byte.toNat))).toInt? with
      | some 0 | none => .false
      | some _ => .true
  | .blob _ => .false

def Truth.toValue : Truth → Value
  | .false => .integer 0
  | .true => .integer 1
  | .unknown => .null

/-- Decimal parsing follows sqlite3AtoF's bounded unsigned mantissa and
exponent adjustment, then the ported sqlite3Fp10Convert2 conversion. -/
def parseDecimal? (source : String) : Option Float := do
  let (negative, chars) :=
    match source.toList with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | rest => (false, rest)
  let (mantissa, exponentChars) := chars.span (fun c => c != 'e' && c != 'E')
  let exponent ←
    match exponentChars with
    | [] => some 0
    | _ :: '+' :: rest => String.mk rest |>.toInt?
    | _ :: rest => String.mk rest |>.toInt?
  let mut digits : Nat := 0
  let mut decimalScale : Int := 0
  let mut afterDot := false
  let mut sawDigit := false
  for c in mantissa do
    if c == '.' && !afterDot then afterDot := true
    else if c.isDigit then
      sawDigit := true
      if afterDot then
        if digits < 1844674407370955160 then
          digits := digits * 10 + (c.toNat - '0'.toNat)
          decimalScale := decimalScale - 1
      else if digits < 1844674407370955160 then
        digits := digits * 10 + (c.toNat - '0'.toNat)
      else decimalScale := decimalScale + 1
    else failure
  if !sawDigit then failure
  let value := SQLite.FloatCodec.decimalToBinary digits (decimalScale + exponent)
  pure (if negative then -value else value)

def Value.toFloat? : Value → Option Float
  | .integer i => some (Float.ofInt i)
  | .real f => some f
  | .text s => parseDecimal? s.trimAscii.toString
  | .textBytes bytes => parseDecimal? (String.ofList (bytes.toList.map (fun b => Char.ofNat b.toNat))).trimAscii.toString
  | _ => none

def Value.toInt? : Value → Option Int
  | .integer i => some i
  | .real f => some f.toInt64.toInt
  | .text s => s.trimAscii.toString.toInt?
  | .textBytes bytes => (String.ofList (bytes.toList.map (fun b => Char.ofNat b.toNat))).trimAscii.toString.toInt?
  | _ => none

def Value.sqlEq (a b : Value) : Truth :=
  match a, b with
  | .null, _ | _, .null => .unknown
  | _, _ => if a == b then .true else .false

def Value.typeRank : Value → Nat
  | .null => 0
  | .integer _ | .real _ => 1
  | .text _ | .textBytes _ => 2
  | .blob _ => 3

/-- Total ordering used by ORDER BY. NULL sorts first, then numbers, text, blobs. -/
private def compareLT [LT α] [DecidableEq α] [DecidableRel (fun a b : α => a < b)]
    (a b : α) : Ordering := if a = b then .eq else if a < b then .lt else .gt

private def compareBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | a :: as, b :: bs =>
    if a == b then compareBytes as bs else if a < b then .lt else .gt

def Value.compare : Value → Value → Ordering
  | .null, .null => .eq
  | .null, _ => .lt
  | _, .null => .gt
  | .integer a, .integer b => compareLT a b
  | .real a, .real b => if a < b then .lt else if b < a then .gt else .eq
  | .integer a, .real b => compareIntegerReal a b
  | .real a, .integer b =>
    match compareIntegerReal b a with
    | .lt => .gt
    | .eq => .eq
    | .gt => .lt
  | .text a, .text b => compareLT a b
  | .textBytes a, .textBytes b => compareBytes a.toList b.toList
  | .text a, .textBytes b => compareBytes a.toUTF8.data.toList b.toList
  | .textBytes a, .text b => compareBytes a.toList b.toUTF8.data.toList
  | .blob a, .blob b => compareBytes a.toList b.toList
  | a, b => compareLT a.typeRank b.typeRank

theorem Value.compare_text_refl (value : String) :
    (Value.text value).compare (.text value) = .eq := by
  simp [Value.compare, compareLT]

def Value.sqlLt (a b : Value) : Truth :=
  match a, b with
  | .null, _ | _, .null => .unknown
  | _, _ => if a.compare b == .lt then .true else .false

theorem sqlEq_null_left (v : Value) : Value.sqlEq .null v = .unknown := by
  cases v <;> rfl

theorem sqlEq_null_right (v : Value) : Value.sqlEq v .null = .unknown := by
  cases v <;> rfl

end SQLeanite
