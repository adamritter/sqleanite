import SQLeanite.FileFormat.DecodeDatabaseHeaderEncode

namespace SQLeanite
namespace FileFormat

theorem decodeUnsignedFixed_encode {width value : Nat} (suffix : List UInt8)
    (bound : value < 256 ^ width) :
    decodeUnsignedFixed width (encodeUnsignedFixed width value ++ suffix) =
      some (value, suffix) := by
  induction width generalizing value suffix with
  | zero =>
      simp only [Nat.pow_zero] at bound
      have valueZero : value = 0 := by omega
      subst value
      rfl
  | succ width induction =>
      have quotientBound : value / 256 < 256 ^ width := by
        rw [Nat.pow_succ] at bound
        omega
      simp only [encodeUnsignedFixed, List.append_assoc, List.cons_append,
        List.nil_append, decodeUnsignedFixed]
      rw [induction (suffix := UInt8.ofNat (value % 256) :: suffix) quotientBound]
      simp only [Option.bind_eq_bind, Option.bind, unsignedFixedByte_toNat]
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      simpa [Nat.mul_comm] using Nat.div_add_mod value 256

theorem decodeUnsignedFixed_consumes {width : Nat} {input suffix : List UInt8}
    {value : Nat} (decoded : decodeUnsignedFixed width input = some (value, suffix)) :
    input.length = width + suffix.length := by
  induction width generalizing input value suffix with
  | zero =>
      simp only [decodeUnsignedFixed] at decoded
      have pairEquality : (0, input) = (value, suffix) := Option.some.inj decoded
      injection pairEquality with valueEquality suffixEquality
      subst value
      subst input
      simp
  | succ width induction =>
      simp only [decodeUnsignedFixed] at decoded
      cases prefixResult : decodeUnsignedFixed width input with
      | none =>
          rw [prefixResult] at decoded
          simp at decoded
      | some result =>
          rcases result with ⟨decodedPrefix, afterPrefix⟩
          rw [prefixResult] at decoded
          simp only [Option.bind_eq_bind, Option.bind] at decoded
          cases afterPrefix with
          | nil => simp at decoded
          | cons byte rest =>
              have pairEquality : (decodedPrefix * 256 + byte.toNat, rest) =
                  (value, suffix) := Option.some.inj decoded
              injection pairEquality with valueEquality suffixEquality
              subst value
              subst suffix
              have prefixConsumed := induction prefixResult
              simp only [List.length_cons] at prefixConsumed
              omega

theorem decodeUnsignedFixed_short {width : Nat} (input : List UInt8)
    (short : input.length < width) :
    decodeUnsignedFixed width input = none := by
  cases decoded : decodeUnsignedFixed width input with
  | none => rfl
  | some result =>
      rcases result with ⟨value, suffix⟩
      have consumed := decodeUnsignedFixed_consumes decoded
      omega

/-- The only signed integer widths used by SQLite record serial types. -/
inductive IntegerWidth where
  | one | two | three | four | six | eight
  deriving Repr, DecidableEq
namespace IntegerWidth

def bytes : IntegerWidth → Nat
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .six => 6
  | .eight => 8

def modulus : IntegerWidth → Nat
  | .one => 256
  | .two => 65536
  | .three => 16777216
  | .four => 4294967296
  | .six => 281474976710656
  | .eight => 18446744073709551616

def midpoint : IntegerWidth → Nat
  | .one => 128
  | .two => 32768
  | .three => 8388608
  | .four => 2147483648
  | .six => 140737488355328
  | .eight => 9223372036854775808

theorem modulus_eq_pow (width : IntegerWidth) :
    width.modulus = 256 ^ width.bytes := by
  cases width <;> decide

theorem modulus_eq_twice_midpoint (width : IntegerWidth) :
    width.modulus = 2 * width.midpoint := by
  cases width <;> decide

theorem modulus_positive (width : IntegerWidth) : 0 < width.modulus := by
  cases width <;> decide

theorem midpoint_positive (width : IntegerWidth) : 0 < width.midpoint := by
  cases width <;> decide
end IntegerWidth

/-- A signed integer known to fit exactly in one SQLite integer width. -/
structure SignedInteger (width : IntegerWidth) where
  value : Int
  lowerBound : -(Int.ofNat width.midpoint) ≤ value
  upperBound : value < Int.ofNat width.midpoint
  deriving DecidableEq

theorem SignedInteger.ext {width : IntegerWidth} {left right : SignedInteger width}
    (valueEquality : left.value = right.value) : left = right := by
  cases left
  cases right
  cases valueEquality
  rfl

def SignedInteger.toUnsigned {width : IntegerWidth}
    (value : SignedInteger width) : Nat :=
  if value.value < 0 then
    (value.value + Int.ofNat width.modulus).toNat
  else value.value.toNat

theorem SignedInteger.toUnsigned_lt {width : IntegerWidth}
    (value : SignedInteger width) : value.toUnsigned < width.modulus := by
  have lowerBound := value.lowerBound
  have upperBound := value.upperBound
  simp only [Int.ofNat_eq_coe] at lowerBound upperBound
  unfold SignedInteger.toUnsigned
  simp only [Int.ofNat_eq_coe]
  split <;> rename_i sign
  · rw [Int.toNat_lt' width.modulus_positive]
    omega
  · rw [Int.toNat_lt' width.modulus_positive]
    have modulusIdentity := width.modulus_eq_twice_midpoint
    omega

def signedIntFromUnsigned (width : IntegerWidth) (value : Fin width.modulus) : Int :=
  if value.val < width.midpoint then Int.ofNat value.val
  else Int.ofNat value.val - Int.ofNat width.modulus

def signedIntegerFromUnsigned (width : IntegerWidth)
    (unsigned : Fin width.modulus) : SignedInteger width :=
  if below : unsigned.val < width.midpoint then {
    value := Int.ofNat unsigned.val
    lowerBound := by
      simp only [Int.ofNat_eq_coe]
      omega
    upperBound := by
      simp only [Int.ofNat_eq_coe]
      omega
  } else {
    value := Int.ofNat unsigned.val - Int.ofNat width.modulus
    lowerBound := by
      have modulusIdentity := width.modulus_eq_twice_midpoint
      simp only [Int.ofNat_eq_coe]
      omega
    upperBound := by
      have unsignedBound := unsigned.isLt
      have midpointPositive := width.midpoint_positive
      simp only [Int.ofNat_eq_coe]
      omega
  }

theorem signedIntegerFromUnsigned_value (width : IntegerWidth)
    (unsigned : Fin width.modulus) :
    (signedIntegerFromUnsigned width unsigned).value =
      signedIntFromUnsigned width unsigned := by
  unfold signedIntegerFromUnsigned signedIntFromUnsigned
  split <;> rfl

theorem signedIntegerFromUnsigned_toUnsigned {width : IntegerWidth}
    (value : SignedInteger width) :
    signedIntegerFromUnsigned width ⟨value.toUnsigned, value.toUnsigned_lt⟩ = value := by
  apply SignedInteger.ext
  rw [signedIntegerFromUnsigned_value]
  unfold signedIntFromUnsigned SignedInteger.toUnsigned
  simp only [Int.ofNat_eq_coe]
  have lowerBound := value.lowerBound
  have upperBound := value.upperBound
  simp only [Int.ofNat_eq_coe] at lowerBound upperBound
  split <;> rename_i sign
  · have modulusIdentity := width.modulus_eq_twice_midpoint
    have sumNonnegative : 0 ≤ value.value + (width.modulus : Int) := by omega
    have unsignedNotBelow :
        ¬(value.value + (width.modulus : Int)).toNat < width.midpoint := by
      rw [Int.toNat_lt' width.midpoint_positive]
      omega
    simp only [unsignedNotBelow, ↓reduceIte]
    have recovered := Int.toNat_of_nonneg sumNonnegative
    omega
  · have valueNonnegative : 0 ≤ value.value := by omega
    have unsignedBelow : value.value.toNat < width.midpoint := by
      rw [Int.toNat_lt' width.midpoint_positive]
      exact upperBound
    simp only [unsignedBelow, ↓reduceIte]
    exact Int.toNat_of_nonneg valueNonnegative

/-- Encoding after signed interpretation recovers the original fixed-width
bit pattern.  This is the converse direction needed by page-routing codecs. -/
theorem SignedInteger.toUnsigned_fromUnsigned (width : IntegerWidth)
    (unsigned : Fin width.modulus) :
    (signedIntegerFromUnsigned width unsigned).toUnsigned = unsigned.val := by
  unfold SignedInteger.toUnsigned
  rw [signedIntegerFromUnsigned_value]
  unfold signedIntFromUnsigned
  split <;> rename_i below
  · rw [if_neg (by simp only [Int.ofNat_eq_coe]; omega)]
    simp
  · have unsignedBound := unsigned.isLt
    have modulusPositive := width.modulus_positive
    rw [if_pos (by simp only [Int.ofNat_eq_coe]; omega)]
    simp only [Int.ofNat_eq_coe]
    have sumIdentity :
        (unsigned.val : Int) - (width.modulus : Int) +
          (width.modulus : Int) = unsigned.val := by omega
    rw [sumIdentity]
    simp

/-- Encode a bounded signed SQLite integer as fixed-width two's-complement
big-endian bytes. -/
def encodeSignedInteger {width : IntegerWidth}
    (value : SignedInteger width) : List UInt8 :=
  encodeUnsignedFixed width.bytes value.toUnsigned

/-- Decode one fixed-width two's-complement SQLite integer. -/
def decodeSignedInteger (width : IntegerWidth) (input : List UInt8) :
    Option (SignedInteger width × List UInt8) := do
  let (unsigned, suffix) ← decodeUnsignedFixed width.bytes input
  if bound : unsigned < width.modulus then
    some (signedIntegerFromUnsigned width ⟨unsigned, bound⟩, suffix)
  else none

theorem encodeSignedInteger_length {width : IntegerWidth}
    (value : SignedInteger width) :
    (encodeSignedInteger value).length = width.bytes := by
  exact encodeUnsignedFixed_length _ _

theorem decodeSignedInteger_encode {width : IntegerWidth}
    (value : SignedInteger width) (suffix : List UInt8) :
    decodeSignedInteger width (encodeSignedInteger value ++ suffix) =
      some (value, suffix) := by
  have unsignedBound := value.toUnsigned_lt
  have encodedBound : value.toUnsigned < 256 ^ width.bytes := by
    rw [← width.modulus_eq_pow]
    exact unsignedBound
  unfold decodeSignedInteger encodeSignedInteger
  rw [decodeUnsignedFixed_encode suffix encodedBound]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos unsignedBound]
  rw [signedIntegerFromUnsigned_toUnsigned]

theorem decodeSignedInteger_short (width : IntegerWidth) (input : List UInt8)
    (short : input.length < width.bytes) :
    decodeSignedInteger width input = none := by
  unfold decodeSignedInteger
  rw [decodeUnsignedFixed_short input short]
  rfl

end FileFormat

end SQLeanite
