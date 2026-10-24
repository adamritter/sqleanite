import Std

namespace SQLeanite.SQLite.NumericLiteral

/-- Underscores are removed from numeric tokens after checking that each one
has a digit on both sides. Runtime conversions of stored strings do not use it. -/
def normalize (source : String) : String := source.replace "_" ""

def digitSeparators (digit : Char → Bool) : Bool → List Char → Bool
  | _, [] => true
  | previous, '_' :: next :: rest =>
      previous && digit next && digitSeparators digit false (next :: rest)
  | _, '_' :: [] => false
  | _, c :: rest => digit c && digitSeparators digit true rest

/-- SQLite interprets a hexadecimal token as a signed 64-bit bit pattern. -/
def signedHex (value : Nat) : Int :=
  if value < 9223372036854775808 then Int.ofNat value
  else Int.ofNat value - 18446744073709551616

/-- Only a positive 31-bit integer is stored directly in SQLite's expression
node. Other integer tokens retain their normalized source spelling. -/
def integerSpelling (value : Int) (source : String) : Option String :=
  if 0 ≤ value && value ≤ 2147483647 then none else some (normalize source)

theorem signedHex_bounds (value : Nat) (fits : value < 18446744073709551616) :
    -9223372036854775808 ≤ signedHex value ∧ signedHex value ≤ 9223372036854775807 := by
  unfold signedHex
  simp only [Int.ofNat_eq_natCast]
  split <;> omega

theorem signedHex_low (value : Nat) (small : value < 9223372036854775808) :
    signedHex value = Int.ofNat value := by simp [signedHex, small]

theorem signedHex_high (value : Nat) (high : 9223372036854775808 ≤ value) :
    signedHex value = Int.ofNat value - 18446744073709551616 := by
  simp [signedHex, Nat.not_lt.mpr high]

theorem digitSeparators_trailing (digit : Char → Bool) (previous : Bool) :
    digitSeparators digit previous ['_'] = false := rfl

end SQLeanite.SQLite.NumericLiteral
