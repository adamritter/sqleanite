import SQLeanite.FileFormat

namespace SQLeanite
namespace Binary64

open FileFormat

def signDivisor : Nat := 2 ^ 63
def exponentDivisor : Nat := 2 ^ 52
def exponentModulus : Nat := 2 ^ 11
def fractionModulus : Nat := 2 ^ 52

def sign (bits : U64Value) : Bool := bits.val / signDivisor = 1
def exponent (bits : U64Value) : Nat :=
  (bits.val / exponentDivisor) % exponentModulus
def fraction (bits : U64Value) : Nat := bits.val % fractionModulus

def isZero (bits : U64Value) : Bool :=
  exponent bits == 0 && fraction bits == 0

def isNaN (bits : U64Value) : Bool :=
  exponent bits == 2047 && fraction bits != 0

def magnitudeBits (bits : U64Value) : Nat := bits.val % signDivisor

def reverse : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/-- Exact IEEE-754 ordering for non-NaN binary64 bit patterns. The sign-bit
transform is monotone on positive values and antitone on negative values;
positive and negative zero are identified. -/
def compareBits (left right : U64Value) : Ordering :=
  if isZero left && isZero right then .eq
  else if sign left != sign right then if sign left then .lt else .gt
  else if sign left then reverse (compare (magnitudeBits left) (magnitudeBits right))
  else compare (magnitudeBits left) (magnitudeBits right)

theorem compareBits_self (bits : U64Value) : compareBits bits bits = .eq := by
  simp [compareBits, reverse]

theorem compareBits_zero_signs (positiveZero negativeZero : U64Value)
    (positive : isZero positiveZero = true)
    (negative : isZero negativeZero = true) :
    compareBits positiveZero negativeZero = .eq := by
  simp [compareBits, positive, negative]

/-- Compare a natural number with a nonnegative finite binary64 exactly, using
the integer significand and a power-of-two scale. No host floating operation
or rounding participates. -/
def compareNat (integer : Nat) (bits : U64Value) : Ordering :=
  let biased := exponent bits
  let significand := if biased = 0 then fraction bits
    else fractionModulus + fraction bits
  let effectiveExponent := if biased = 0 then 1 else biased
  if 1075 ≤ effectiveExponent then
    compare integer (significand * 2 ^ (effectiveExponent - 1075))
  else
    compare (integer * 2 ^ (1075 - effectiveExponent)) significand

/-- Exact comparison between a mathematical integer and a finite, non-NaN
binary64 bit pattern. -/
def compareInteger (integer : Int) (bits : U64Value) : Ordering :=
  if isZero bits then compare integer 0
  else if sign bits then
    if 0 ≤ integer then .gt
    else reverse (compareNat (-integer).toNat bits)
  else if integer < 0 then .lt
  else compareNat integer.toNat bits

theorem compareInteger_zero (integer : Int) (bits : U64Value)
    (zero : isZero bits = true) :
    compareInteger integer bits = compare integer 0 := by
  simp [compareInteger, zero]

end Binary64
end SQLeanite
