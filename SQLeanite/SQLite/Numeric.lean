import SQLeanite.Value

/-!
SQLite 3.53.4 value conversions, adapted from util.c (sqlite3Atoi64,
sqlite3AtoF), vdbemem.c (sqlite3VdbeIntValue, sqlite3VdbeMemNumerify), and
vdbe.c (computeNumericType). This is pure Lean, not an SQLite FFI.
Decimal-to-binary64 conversion uses the port in SQLite.FloatCodec.
Algorithm provenance is not a proof of equivalence to the C compiler output.
-/
namespace SQLeanite.SQLite.Numeric

def minInt : Int := -9223372036854775808
def maxInt : Int := 9223372036854775807

def fits (i : Int) : Bool := minInt ≤ i && i ≤ maxInt

def space (c : Char) : Bool := c == ' ' || ('\t' ≤ c && c ≤ '\r')

def signedDigits (source : String) : Bool × List Char :=
  match source.toList.dropWhile space with
  | '-' :: rest => (true, rest)
  | '+' :: rest => (false, rest)
  | rest => (false, rest)

/-- Saturating prefix conversion. Unlike a numeric cast, an INTEGER cast
ignores decimal points and exponents; hexadecimal text is not recognized. -/
def integerPrefix (source : String) : Int :=
  let (negative, chars) := signedDigits source
  let magnitude := (chars.takeWhile Char.isDigit).foldl
    (fun n c => min 9223372036854775808 (n * 10 + c.toNat - '0'.toNat)) 0
  max minInt (min maxInt (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude))

structure Prefix where
  spelling : String
  floating : Bool
  integerFits : Bool
  complete : Bool
  completeToNul : Bool
  deriving Repr

/-- The decimal prefix and the two distinctions needed by computeNumericType:
whether a decimal point/exponent occurred, and whether the integer fits. -/
def parsePrefix (source : String) : Prefix := Id.run do
  let (negative, chars) := signedDigits source
  let (whole, rest) := chars.span Char.isDigit
  let (fraction, rest, dot) := match rest with
    | '.' :: tail => let (digits, rest) := tail.span Char.isDigit; (digits, rest, true)
    | _ => ([], rest, false)
  let mantissa := whole ++ (if dot then ['.'] ++ fraction else [])
  let sawDigit := !whole.isEmpty || !fraction.isEmpty
  let mut suffix := []
  let mut tail := rest
  let mut hasExponent := false
  match rest with
  | e :: afterE =>
    if (e == 'e' || e == 'E') && sawDigit then
      let (sign, digits) := match afterE with
        | '+' :: xs => (['+'], xs)
        | '-' :: xs => (['-'], xs)
        | xs => ([], xs)
      let (digits, remaining) := digits.span Char.isDigit
      if !digits.isEmpty then
        -- Bound exponent work just as sqlite3AtoF does.
        let exponent := digits.foldl (fun n c => min 10000 (n * 10 + c.toNat - 48)) 0
        suffix := e :: sign ++ (toString exponent).toList
        tail := remaining
        hasExponent := true
  | [] => pure ()
  let magnitude := whole.foldl
    (fun n c => min 9223372036854775809 (n * 10 + c.toNat - 48)) 0
  return {
    spelling := if sawDigit then
      String.ofList ((if negative then ['-'] else []) ++ mantissa ++ suffix)
      else "0"
    floating := (dot && sawDigit) || hasExponent
    integerFits := magnitude ≤ (if negative then 9223372036854775808 else 9223372036854775807)
    complete := sawDigit && (tail.dropWhile space).isEmpty
    completeToNul := sawDigit && ((tail.takeWhile (· != '\x00')).dropWhile space).isEmpty }

/-- Numeric prefixes are ASCII, so an invalid UTF-8 byte terminates the
prefix. BLOB values are not decoded or rewritten in storage. -/
def numericText : Value → String
  | .text s => s
  | .blob bytes => String.ofList ((bytes.toList.takeWhile (·.toNat < 128)).map
      (fun byte => Char.ofNat byte.toNat))
  | value => toString value

def realPrefix (source : String) : Float :=
  (parseDecimal? (parsePrefix source).spelling).getD 0.0

def realToInteger (r : Float) : Int :=
  if r.isNaN then 0
  else if r < -9223372036854774784.0 then minInt
  else if r > 9223372036854774784.0 then maxInt
  else r.toInt64.toInt

def integer : Value → Int
  | .null => 0
  | .integer i => i
  | .real r => realToInteger r
  | v => integerPrefix (numericText v)

def real : Value → Float
  | .null => 0.0
  | .integer i => Float.ofInt i
  | .real r => r
  | v => realPrefix (numericText v)

/-- Arithmetic numericType preserves REAL spelling (e.g. '1.0'), unlike
CAST AS NUMERIC, which can recover an integer. -/
def arithmetic : Value → Value
  | v@(.text _) | v@(.blob _) =>
      let s := numericText v
      let p := parsePrefix s
      if !p.floating && p.integerFits && (!p.completeToNul || p.complete) then
        .integer (integerPrefix s)
      else .real (realPrefix s)
  | v => v

def numerify (v : Value) : Value :=
  match v with
  | .text _ | .blob _ =>
      let source := numericText v
      let p := parsePrefix source
      let n : Value := if !p.floating && p.integerFits then .integer (integerPrefix source)
        else .real (realPrefix source)
      match n with
      | .real r =>
          let i := realToInteger r
          if r == 0.0 || (r == Float.ofInt i && -2251799813685248 ≤ i && i < 2251799813685248)
          then .integer i else n
      | _ => n
  | _ => v

def truth : Value → Truth
  | .null => .unknown
  | v => if real v == 0.0 then .false else .true

/-- vdbemem.c: sqlite3VdbeIntegerAffinity. The extreme integers are excluded
from the round-trip test, avoiding the rounded Int64.max = 2^63 trap. -/
def integerAffinity (r : Float) : Value :=
  let i := realToInteger r
  if !r.isNaN && r == Float.ofInt i && minInt < i && i < maxInt then .integer i
  else .real r

/-- vdbe.c: applyNumericAffinity / alsoAnInt. Invalid numeric text and BLOBs
remain unchanged; decimal/exponent spelling can still yield an INTEGER. -/
def applyAffinity : Value → Value
  | v@(.text source) =>
      let p := parsePrefix source
      if !p.completeToNul then v
      else
        let r := realPrefix source
        let i := realToInteger r
        let same := r == 0.0 || (r == Float.ofInt i &&
          -2251799813685248 ≤ i && i < 2251799813685248)
        if !p.floating && (same || (p.complete && p.integerFits)) then
          .integer (if same then i else integerPrefix source)
        else integerAffinity r
  | .real r => integerAffinity r
  | v => v

theorem fits_iff (i : Int) : fits i = true ↔ minInt ≤ i ∧ i ≤ maxInt := by
  simp [fits]

theorem integerPrefix_bounds (source : String) :
    minInt ≤ integerPrefix source ∧ integerPrefix source ≤ maxInt := by
  unfold integerPrefix
  exact ⟨Int.le_max_left _ _, Int.max_le.mpr ⟨by decide, Int.min_le_left _ _⟩⟩

end SQLeanite.SQLite.Numeric
