import Std

/-!
SQLite 3.53.4 util.c: powerOfTen, sqlite3Multiply128/160,
sqlite3Fp2Convert10, sqlite3Fp10Convert2, and the 17-digit sqlite3FpDecode
path; printf.c: %!.17g rendering. Tables are copied from the pinned source.
Nat products replace C's 128-bit intrinsics without adding native bindings.
This is the default 17-digit conversion, not the entire printf subsystem.
-/
namespace SQLeanite.SQLite.FloatCodec

private def base : Array Nat := #[
  0x8000000000000000, 0xa000000000000000, 0xc800000000000000, 0xfa00000000000000,
  0x9c40000000000000, 0xc350000000000000, 0xf424000000000000, 0x9896800000000000,
  0xbebc200000000000, 0xee6b280000000000, 0x9502f90000000000, 0xba43b74000000000,
  0xe8d4a51000000000, 0x9184e72a00000000, 0xb5e620f480000000, 0xe35fa931a0000000,
  0x8e1bc9bf04000000, 0xb1a2bc2ec5000000, 0xde0b6b3a76400000, 0x8ac7230489e80000,
  0xad78ebc5ac620000, 0xd8d726b7177a8000, 0x878678326eac9000, 0xa968163f0a57b400,
  0xd3c21bcecceda100, 0x84595161401484a0, 0xa56fa5b99019a5c8]

private def scale : Array Nat := #[
  0x8049a4ac0c5811ae, 0xcf42894a5dce35ea, 0xa76c582338ed2621, 0x873e4f75e2224e68,
  0xda7f5bf590966848, 0xb080392cc4349dec, 0x8e938662882af53e, 0xe65829b3046b0afa,
  0xba121a4650e4ddeb, 0x964e858c91ba2655, 0xf2d56790ab41c2a2, 0xc428d05aa4751e4c,
  0x9e74d1b791e07e48, 0xcccccccccccccccc, 0xcecb8f27f4200f3a, 0xa70c3c40a64e6c51,
  0x86f0ac99b4e8dafd, 0xda01ee641a708de9, 0xb01ae745b101e9e4, 0x8e41ade9fbebc27d,
  0xe5d3ef282a242e81, 0xb9a74a0637ce2ee1, 0x95f83d0a1fb69cd9, 0xf24a01a73cf2dccf,
  0xc3b8358109e84f07, 0x9e19db92b4e31ba9]

private def scaleLo : Array Nat := #[
  0x205b896d, 0x52064cad, 0xaf2af2b8, 0x5a7744a7,
  0xaf39a475, 0xbd8d794e, 0x547eb47b, 0x0cb4a5a3,
  0x92f34d62, 0x3a6a07f9, 0xfae27299, 0xaa97e14c,
  0x775ea265, 0xcccccccc, 0x00000000, 0x999090b6,
  0x69a028bb, 0xe80e6f48, 0x5ec05dd0, 0x14588f14,
  0x8f1668c9, 0x6d953e2c, 0x4abdaf10, 0xbc633b39,
  0x0a862f81, 0x6c07a2c2]

def multiply128 (a b : Nat) : Nat × Nat :=
  (a * b / 2^64, a * b % 2^64)

def multiply160 (a low b : Nat) : Nat × Nat :=
  let product := a * b + low * b / 2^32
  (product / 2^64, product / 2^32 % 2^32)

def powerOfTen (p : Int) : Nat × Nat :=
  if p == -1 then (scale[13]!, scaleLo[13]!)
  else if 0 ≤ p && p < 27 then (base[p.toNat]!, 0)
  else
    -- Euclidean division is required here, including negative exponents.
    let group := p / 27
    let index := (p % 27).toNat
    let high := scale[(group + 13).toNat]!
    let low := scaleLo[(group + 13).toNat]!
    if index == 0 then (high, low)
    else
      let (high, low) := multiply160 high low base[index]!
      if high < 2^63 then (high * 2 + low / 2^31, (low * 2 + 1) % 2^32)
      else (high, low)

def power10to2 (p : Int) : Int := (p * 108853) / 32768
def power2to10 (p : Int) : Int := (p * 78913) / 262144

def binaryToDecimal (mantissa : Nat) (exponent : Int) : Nat × Int :=
  let p := 17 - power2to10 (exponent + 63)
  let high := (multiply128 mantissa (powerOfTen p).1).1
  let high := high >>> (-(exponent + power10to2 p + 2)).toNat
  ((high + ((high <<< 1) &&& 2)) >>> 1, -p)

/-- The SQLite decimal-to-binary64 algorithm. Its mantissa input is unsigned
64-bit; its exponent checks precede table access and all large shifts. -/
def decimalToBinary (digits : Nat) (power : Int) : Float := Id.run do
  let digits := digits % 2^64
  if digits == 0 || power < -348 then return 0.0
  if power > 347 then return Float.ofBits 0x7ff0000000000000
  let bits := digits.log2 + 1
  let lp := power10to2 power
  let mut e := 53 - Int.ofNat bits - lp
  if e > 1074 then
    if e ≥ 1130 then return 0.0
    e := 1074
  let shift := (-(e - Int.ofNat (64 - bits) + lp + 3)).toNat
  let (high, low) := powerOfTen power
  let (high, low) := if low != 0 then (high + 1, 2^32 - 1 - low) else (high, low)
  let x := digits <<< (64 - bits)
  let (hi, lo) := multiply128 x high
  let mid1 := lo >>> 32
  let mut hi := hi
  let mut sticky := 1
  if (hi &&& (2^shift - 1)) == 0 then
    let mid2 := (multiply128 x (low <<< 32)).1 >>> 32
    sticky := if (mid1 + 2^32 - mid2) % 2^32 > 1 then 1 else 0
    hi := hi - (if mid1 < mid2 then 1 else 0)
  let mut u := (hi >>> shift) ||| sticky
  if u ≥ 2^55 - 2 then
    u := (u >>> 1) ||| (u &&& 1)
    e := e - 1
  let mut m := (u + 1 + ((u >>> 2) &&& 1)) >>> 2
  if e ≤ -972 then return Float.ofBits 0x7ff0000000000000
  if (m &&& 2^52) != 0 then
    m := (m % 2^52) ||| ((1075 - e).toNat <<< 52)
  return Float.ofBits (UInt64.ofNat m)

private def digitsValue (digits : List Char) : Nat :=
  digits.foldl (fun n c => n * 10 + c.toNat - 48) 0

private def trimZeros (digits : List Char) : List Char :=
  (digits.reverse.dropWhile (· == '0')).reverse

/-- Significant digits and decimal-point position. Port of the 17-digit
rounding and round-trip shortening branches in sqlite3FpDecode. -/
def decode17 (r : Float) : String × Int := Id.run do
  let bits := r.toBits.toNat
  let exponent := (bits >>> 52) &&& 2047
  let mantissa := bits &&& (2^52 - 1)
  let (mantissa, exponent) := if exponent == 0 then
      let leading := 64 - (mantissa.log2 + 1)
      (mantissa <<< leading, -1074 - Int.ofNat leading)
    else ((mantissa <<< 11) ||| 2^63, Int.ofNat exponent - 1086)
  let (digits, power) := binaryToDecimal mantissa exponent
  let raw := (toString digits).toList
  let n := raw.length
  let mut point := Int.ofNat n + power
  let mut rounding := 17
  if n > 17 then
    if raw[15]! == '9' && raw[14]! == '9' then
      let j := 14 - ((raw.take 14).reverse.takeWhile (· == '9')).length
      let v := if j == 0 then 1 else digitsValue (raw.take j) + 1
      if r == decimalToBinary v (power + Int.ofNat n - Int.ofNat j) then rounding := j + 1
    else if point ≥ Int.ofNat n ||
        (raw[15]! == '0' && raw[14]! == '0' && raw[13]! == '0') then
      let j := 13 - ((raw.take 13).reverse.takeWhile (· == '0')).length
      let v := digitsValue (raw.take j)
      if r == decimalToBinary v (power + Int.ofNat n - Int.ofNat j) then rounding := j + 1
    let rounded := digitsValue (raw.take rounding) + (if raw[rounding]! ≥ '5' then 1 else 0)
    let digits := (toString rounded).toList
    if digits.length > rounding then point := point + 1
    return (String.ofList (trimZeros digits), point)
  return (String.ofList (trimZeros raw), point)

/-- sqlite3FpDecode with a fixed number of fractional digits and the `%!f`
20-significant-digit cap. The input is a positive finite nonzero magnitude.
The 17-digit shortening rule is shared with the ordinary REAL text path. -/
def decodeFixed (r : Float) (precision : Nat) : String × Int := Id.run do
  let bits := r.toBits.toNat
  let exponent := (bits >>> 52) &&& 2047
  let mantissa := bits &&& (2^52 - 1)
  let (mantissa, exponent) := if exponent == 0 then
      let leading := 64 - (mantissa.log2 + 1)
      (mantissa <<< leading, -1074 - Int.ofNat leading)
    else ((mantissa <<< 11) ||| 2^63, Int.ofNat exponent - 1086)
  let (digits, power) := binaryToDecimal mantissa exponent
  let mut raw := (toString digits).toList
  let mut point := Int.ofNat raw.length + power
  let mut rounding := point + Int.ofNat precision
  if rounding == 0 && raw.head! ≥ '5' then
    raw := '0' :: raw
    point := point + 1
    rounding := 1
  if rounding > 0 && (rounding < Int.ofNat raw.length || raw.length > 20) then
    let count := min rounding.toNat 20
    if count == 17 then return decode17 r
    let rounded := digitsValue (raw.take count) + (if raw[count]! ≥ '5' then 1 else 0)
    let digits := (toString rounded).toList
    if digits.length > count then point := point + 1
    return (String.ofList (trimZeros digits), point)
  return (String.ofList (trimZeros raw), point)

/-- The fixed-decimal `%!.*f` text used by roundFunc. Digits below the
requested decimal place are truncated only after the decoder rounds them. -/
def renderFixed (value : Float) (precision : Nat) : String :=
  if !value.isFinite then if value.isNaN then "NaN" else if value < 0.0 then "-Inf" else "Inf"
  else if value == 0.0 then "0.0"
  else
    let negative := value < 0.0
    let (digits, point) := decodeFixed (if negative then -value else value) precision
    let chars := digits.toList
    let whole := if point ≤ 0 then "0" else
      String.ofList (chars.take point.toNat ++ List.replicate (point.toNat - chars.length) '0')
    let fraction := if point ≤ 0 then List.replicate (-point).toNat '0' ++ chars
      else chars.drop point.toNat
    let fraction := String.ofList (trimZeros (fraction.take precision))
    (if negative then "-" else "") ++ whole ++ "." ++ (if fraction.isEmpty then "0" else fraction)

/-- SQLite's default REAL-to-TEXT conversion (%!.17g), including the mandatory
fractional digit, exponent padding, special values, and unsigned zero. -/
def render (value : Float) : String :=
  if !value.isFinite then if value.isNaN then "NaN" else if value < 0.0 then "-Inf" else "Inf"
  else if value == 0.0 then "0.0"
  else
    let negative := value < 0.0
    let magnitude := if negative then -value else value
    let (digits, point) := decode17 magnitude
    let chars := digits.toList
    let sign := if negative then "-" else ""
    let exponent := point - 1
    if exponent < -4 || exponent > 16 then
      let fraction := String.ofList chars.tail!
      let suffix := toString exponent.natAbs
      sign ++ chars.head!.toString ++ "." ++ (if fraction.isEmpty then "0" else fraction) ++
        "e" ++ (if exponent < 0 then "-" else "+") ++
        (if suffix.length < 2 then "0" else "") ++ suffix
    else if point ≤ 0 then
      sign ++ "0." ++ String.ofList (List.replicate (-point).toNat '0') ++ digits
    else
      let whole := String.ofList (chars.take point.toNat) ++
        String.ofList (List.replicate (point.toNat - chars.length) '0')
      let fraction := String.ofList (chars.drop point.toNat)
      sign ++ whole ++ "." ++ (if fraction.isEmpty then "0" else fraction)

theorem multiply128_reconstruct (a b : Nat) :
    (multiply128 a b).1 * 2^64 + (multiply128 a b).2 = a * b := by
  simp only [multiply128]
  rw [Nat.mul_comm (a * b / 2^64)]
  exact Nat.div_add_mod _ _

end SQLeanite.SQLite.FloatCodec

