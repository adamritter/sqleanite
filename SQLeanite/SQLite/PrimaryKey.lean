import SQLeanite.PhysicalQuery

/-! Canonical numeric equality keys for non-alias SQLite primary indexes.
Only the lookup key changes; stored values retain their original storage class. -/
namespace SQLeanite.SQLite.PrimaryKey

open PhysicalCodec

/-- Truncate an exact binary significand using integer arithmetic. Equality
with the original bit pattern is checked before this candidate is admitted. -/
def integerCandidate (bits : FileFormat.U64Value) : Int :=
  let biased := Binary64.exponent bits
  let significand := if biased = 0 then Binary64.fraction bits
    else Binary64.fractionModulus + Binary64.fraction bits
  let effective := if biased = 0 then 1 else biased
  let magnitude := if 1075 ≤ effective then significand * 2 ^ (effective - 1075)
    else significand / 2 ^ (1075 - effective)
  if Binary64.sign bits then -Int.ofNat magnitude else Int.ofNat magnitude

/-- Integral REALs and INTEGERs use the same key, including signed zero and
INT64_MIN. Infinities and non-integral REALs retain their bit representation. -/
def canonical : PhysicalCodec.Value → PhysicalCodec.Value
  | original@(.realBits bits) =>
      if Binary64.exponent bits = 2047 then original else
        let value := integerCandidate bits
        if lower : -(Int.ofNat FileFormat.IntegerWidth.eight.midpoint) ≤ value then
          if upper : value < Int.ofNat FileFormat.IntegerWidth.eight.midpoint then
            if Binary64.compareInteger value bits = .eq then .integer ⟨value, lower, upper⟩
            else original
          else original
        else original
  | value => value

/-- Canonicalization never merges numerically different values. The check is
against the exact integer/binary64 comparator, without host floating rounding. -/
theorem canonical_compare (value : PhysicalCodec.Value) :
    PhysicalQuery.compareValue (canonical value) value = .eq := by
  cases value with
  | realBits bits =>
      simp only [canonical]
      split
      · exact PhysicalQuery.compareValue_self _
      · split
        · split
          · split
            · next equal => exact equal
            · exact PhysicalQuery.compareValue_self _
          · exact PhysicalQuery.compareValue_self _
        · exact PhysicalQuery.compareValue_self _
  | _ => exact PhysicalQuery.compareValue_self _

end SQLeanite.SQLite.PrimaryKey
