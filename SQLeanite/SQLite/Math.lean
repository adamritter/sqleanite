import SQLeanite.SQLite.Numeric

/-! SQLite 3.53.4 func.c math functions. SQL conversions, rounding and floating
remainder are implemented here in Lean. Transcendentals use Lean's existing
Float operations (standard-library libm bindings); they are not transparent
formal models of those functions. No SQLite or project-native math binding is
introduced. Numerical agreement is checked separately on the target platform. -/
namespace SQLeanite.SQLite.Math

/-- sqlite3_value_numeric_type applies numeric affinity without converting a
REAL to INTEGER. Floating-point TEXT spelling also retains the REAL type. -/
def numeric? : Value → Option Value
  | value@(.integer _) | value@(.real _) => some value
  | value@(.text _) | value@(.textBytes _) =>
      let source := Numeric.numericText value
      let parsed :=  Numeric.parsePrefix source
      if !parsed.completeToNul then none
      else
        let real := Numeric.realPrefix source
        let integer := Numeric.realToInteger real
        let same := real == 0.0 || (real == Float.ofInt integer &&
          -2251799813685248 ≤ integer && integer < 2251799813685248)
        if !parsed.floating && (same || (parsed.complete && parsed.integerFits)) then
          some (.integer (if same then integer else Numeric.integerPrefix source))
        else some (.real real)
  | _ => none

def result (value : Float) : Value := if value.isNaN then .null else .real value

inductive Direction where
  | up | down | zero
  deriving BEq

/-- Clear fractional significand bits, then adjust by one unit when required.
This preserves signed zero and has no dependence on the host rounding mode. -/
def roundFloat (direction : Direction) (value : Float) : Float :=
  let bits := value.toBits.toNat
  let negative := bits / 9223372036854775808 != 0
  let exponent := (bits / 4503599627370496) % 2048
  let away := (direction == .up && !negative) || (direction == .down && negative)
  if exponent ≥ 1075 then value
  else if exponent < 1023 then
    if bits % 9223372036854775808 == 0 then value
    else if away then (if negative then -1.0 else 1.0)
    else Float.ofBits (UInt64.ofNat (if negative then 9223372036854775808 else 0))
  else
    let unit := 2 ^ (1075 - exponent)
    let fraction := bits % unit
    Float.ofBits (UInt64.ofNat (bits - fraction + (if away && fraction != 0 then unit else 0)))

def rounding (direction : Direction) (value : Value) : Value :=
  match numeric? value with
  | some (.integer integer) => .integer integer
  | some (.real real) => result (roundFloat direction real)
  | _ => .null

/-- The exact remainder is computed on aligned dyadic significands. The result
has at most 53 significant bits; scaling by the exact power of two is exact,
including subnormals. The shifts are bounded by the binary64 exponent range. -/
def remainder (left right : Float) : Value :=
  let a := left.toBits.toNat
  let b := right.toBits.toNat
  let sign := a / 9223372036854775808 * 9223372036854775808
  let a := a % 9223372036854775808
  let b := b % 9223372036854775808
  let ea := a / 4503599627370496
  let eb := b / 4503599627370496
  if ea == 2047 || b == 0 || (eb == 2047 && b % 4503599627370496 != 0) then .null
  else if eb == 2047 || a == 0 then .real left
  else
    let ma := a % 4503599627370496 + (if ea == 0 then 0 else 4503599627370496)
    let mb := b % 4503599627370496 + (if eb == 0 then 0 else 4503599627370496)
    let ea := max 1 ea
    let eb := max 1 eb
    let remaining := if ea ≥ eb then (ma <<< (ea - eb)) % mb
      else ma % (mb <<< (eb - ea))
    let exponent := min ea eb
    let scale := if exponent < 53 then 1 <<< (exponent - 1) else (exponent - 52) <<< 52
    let magnitude := Float.ofNat remaining * Float.ofBits (UInt64.ofNat scale)
    .real (Float.ofBits (UInt64.ofNat (magnitude.toBits.toNat + sign)))

def pi : Float := Float.ofBits 0x400921FB54442D18

def unaryNames : List String :=
  ["acos", "acosh", "asin", "asinh", "atan", "atanh", "cos", "cosh", "sin", "sinh",
   "tan", "tanh", "exp", "ln", "log", "log2", "log10", "sqrt", "radians", "degrees"]

def unary (name : String) (value : Value) : Value :=
  match numeric? value with
  | none => .null
  | some value =>
      let x := Numeric.real value
      if ["ln", "log", "log2", "log10"].contains name && x ≤ 0.0 then .null
      else result (match name with
        | "acos" => x.acos | "acosh" => x.acosh
        | "asin" => x.asin | "asinh" => x.asinh
        | "atan" => x.atan | "atanh" => x.atanh
        | "cos" => x.cos | "cosh" => x.cosh
        | "sin" => x.sin | "sinh" => x.sinh
        | "tan" => x.tan | "tanh" => x.tanh
        | "exp" => x.exp | "ln" => x.log
        | "log" | "log10" => x.log10 | "log2" => x.log2
        | "sqrt" => x.sqrt
        | "radians" => x * (pi / 180.0)
        | "degrees" => x * (180.0 / pi)
        | _ => x)

/-- Preserve logFunc's pinned behavior: the second argument uses the permissive
real conversion, and bases below or equal to one are rejected. -/
def logarithm (base value : Value) : Value :=
  match numeric? base with
  | none => .null
  | some base =>
      let base := Numeric.real base
      let x := Numeric.real value
      if base ≤ 0.0 then .null
      else
        let denominator := base.log
        if denominator ≤ 0.0 || x ≤ 0.0 then .null
        else result (x.log / denominator)

def binary (name : String) (left right : Value) : Value :=
  match numeric? left, numeric? right with
  | some left, some right =>
      let a := Numeric.real left
      let b := Numeric.real right
      if name == "mod" then remainder a b
      else result (if name == "atan2" then a.atan2 b else a.pow b)
  | _, _ => .null

def accepts (name : String) (count : Nat) : Bool :=
  (name == "pi" && count == 0) ||
  ((unaryNames.contains name || ["ceil", "ceiling", "floor", "trunc"].contains name) && count == 1) ||
  (["pow", "power", "mod", "atan2", "log"].contains name && count == 2)

def evaluate? (name : String) (values : List Value) : Option Value :=
  match name, values with
  | "pi", [] => some (.real pi)
  | "ceil", [value] | "ceiling", [value] => some (rounding .up value)
  | "floor", [value] => some (rounding .down value)
  | "trunc", [value] => some (rounding .zero value)
  | "log", [base, value] => some (logarithm base value)
  | name, [value] => if unaryNames.contains name then some (unary name value) else none
  | name, [left, right] =>
      if ["pow", "power", "mod", "atan2"].contains name then some (binary name left right) else none
  | _, _ => none

theorem numeric_integer (integer : Int) : numeric? (.integer integer) = some (.integer integer) := rfl

theorem rounding_integer (direction : Direction) (integer : Int) :
    rounding direction (.integer integer) = .integer integer := rfl

theorem unary_null (name : String) : unary name .null = .null := rfl

end SQLeanite.SQLite.Math
