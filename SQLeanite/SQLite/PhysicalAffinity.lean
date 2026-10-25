import SQLeanite.PhysicalCodec
import SQLeanite.Binary64
import SQLeanite.SQLite.Type
import SQLeanite.SQLite.Numeric

/-! SQLite affinity at the proof-bounded physical value boundary. This module
has no SQL parser or engine dependency. Numeric scanning is ASCII, so mapping
each stored byte to a character also handles malformed UTF-8 without changing
the bytes of values that remain TEXT. -/
namespace SQLeanite.SQLite.PhysicalAffinity

open PhysicalCodec

abbrev Number := Sum (FileFormat.SignedInteger .eight) FileFormat.U64Value

def numberValue : Number → PhysicalCodec.Value
  | .inl integer => .integer integer
  | .inr bits => .realBits bits

def number? : SQLeanite.Value → Option Number
  | .integer i =>
      if lower : -(Int.ofNat FileFormat.IntegerWidth.eight.midpoint) ≤ i then
        if upper : i < Int.ofNat FileFormat.IntegerWidth.eight.midpoint then
          some (.inl ⟨i, lower, upper⟩)
        else none
      else none
  | .real r =>
      let bits := r.toBits
      some (.inr ⟨bits.toNat, by simpa using bits.toNat_lt⟩)
  | _ => none

def numericText? (bytes : List UInt8) : Option Number :=
  let source := String.ofList (bytes.map (fun byte => Char.ofNat byte.toNat))
  number? (Numeric.applyAffinity (.text source))

def numericText (original : Text) : PhysicalCodec.Value :=
  match numericText? original.bytes with
  | none => .text original
  | some value => numberValue value

def renderNumber (original : PhysicalCodec.Value) (value : SQLeanite.Value) :
    PhysicalCodec.Value :=
  let bytes := (toString value).toUTF8.data.toList
  if bound : bytes.length < textByteLimit then .text ⟨bytes, bound⟩ else original

def textual : PhysicalCodec.Value → PhysicalCodec.Value
  | v@(.integer i) => renderNumber v (.integer i.value)
  | v@(.realBits bits) => renderNumber v (.real (Float.ofBits (UInt64.ofNat bits.val)))
  | v => v

def numeric : PhysicalCodec.Value → PhysicalCodec.Value
  | .text text => numericText text
  | v@(.realBits bits) =>
      match number? (Numeric.integerAffinity (Float.ofBits (UInt64.ofNat bits.val))) with
      | some value => numberValue value
      | none => v
  | v => v

/-- Boolean contexts use numeric prefixes of TEXT/BLOB, independently of
comparison affinity. NULL retains SQL's third truth value. -/
def truth : PhysicalCodec.Value → Truth
  | .null => .unknown
  | .integer value => if value.value = 0 then .false else .true
  | .realBits bits => if Binary64.isZero bits then .false else .true
  | .text value => Numeric.truth (.textBytes value.bytes.toArray)
  | .blob value => Numeric.truth (.blob value.bytes.toArray)

/-- Comparisons only need to convert TEXT and leave already numeric operands
in their original representation; the existing exact numeric comparator
equates INTEGER/REAL representations without rounding the INTEGER operand. -/
def comparison : Affinity → PhysicalCodec.Value → PhysicalCodec.Value
  | .integer, .text text | .numeric, .text text | .real, .text text => numericText text
  | .text, value => textual value
  | _, value => value

def realRead : PhysicalCodec.Value → PhysicalCodec.Value
  | .integer i =>
      let bits := (Float.ofInt i.value).toBits
      .realBits ⟨bits.toNat, by simpa using bits.toNat_lt⟩
  | value => value

/-- OP_RealAffinity: SQLite can store an integral REAL using an integer
serial type. The logical row still exposes a REAL after OP_Column. -/
def read : Affinity → PhysicalCodec.Value → PhysicalCodec.Value
  | .real, value => realRead value
  | _, value => value

def write : Affinity → PhysicalCodec.Value → PhysicalCodec.Value
  | .integer, value | .numeric, value => numeric value
  | .real, value => realRead (numeric value)
  | .text, value => textual value
  | .blob, value => value

/-- The bounded Core admits canonical column values. Checking storage class
and numeric-prefix eligibility avoids comparing a long TEXT with itself.
This is the invariant which permits ordinary B-tree comparisons on admitted
columns. A foreign file outside this invariant is rejected, not misqueried. -/
def accepts : Affinity → PhysicalCodec.Value → Bool
  | .integer, .text text | .numeric, .text text | .real, .text text =>
      (numericText? text.bytes).isNone
  | .text, .integer _ | .text, .realBits _ | .real, .integer _ => false
  | _, _ => true

theorem comparison_eq_self {affinity : Affinity} {value : PhysicalCodec.Value}
    (accepted : accepts affinity value = true) : comparison affinity value = value := by
  cases affinity <;> cases value <;> simp_all [accepts, comparison, textual]
  all_goals
    unfold numericText
    cases converted : numericText? _ <;> simp_all

theorem read_eq_self {affinity : Affinity} {value : PhysicalCodec.Value}
    (accepted : accepts affinity value = true) : read affinity value = value := by
  cases affinity <;> cases value <;> simp_all [accepts, read, realRead]

theorem comparison_null (affinity : Affinity) : comparison affinity .null = .null := by
  cases affinity <;> rfl

theorem write_null (affinity : Affinity) : write affinity .null = .null := by
  cases affinity <;> rfl

end SQLeanite.SQLite.PhysicalAffinity
