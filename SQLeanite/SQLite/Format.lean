import SQLeanite.SQLite.Text
import SQLeanite.SQLite.UnicodeEscape

/-! Byte-oriented port of the SQL-facing SQLite 3.53.4 printf.c formatter.
The argument stream is SQL Values, not C varargs. Unknown/internal conversions
stop at the already produced prefix. The floating decoder uses the pinned
integer conversion tables in FloatCodec, without a host printf dependency. -/
namespace SQLeanite.SQLite.Format

structure Options where
  left : Bool := false
  sign : String := ""
  alternate : Bool := false
  characters : Bool := false
  zero : Bool := false
  commas : Bool := false
  width : Nat := 0
  precision : Option Nat := none

private def flag (options : Options) (byte : UInt8) : Option Options :=
  match byte.toNat with
  | 45 => some { options with left := true }
  | 43 => some { options with sign := "+" }
  | 32 => some { options with sign := " " }
  | 35 => some { options with alternate := true }
  | 33 => some { options with characters := true }
  | 48 => some { options with zero := true }
  | 44 => some { options with commas := true }
  | _ => none

private def flags : List UInt8 → Options → Options × List UInt8
  | [], options => (options, [])
  | byte :: rest, options => match flag options byte with
      | none => (options, byte :: rest)
      | some options => flags rest options

private def argument : List Value → Value × List Value
  | [] => (.null, [])
  | value :: rest => (value, rest)

private def decimal (bytes : List UInt8) : Nat :=
  bytes.foldl (fun n byte => (n * 10 + byte.toNat - 48) % 2147483648) 0

private def digit (byte : UInt8) : Bool := 48 ≤ byte && byte ≤ 57

/-- Width and precision parse as unsigned 32-bit decimal counters; star
arguments first narrow to a signed 32-bit integer, including its minimum. -/
def parse (bytes : List UInt8) (values : List Value) :
    Options × Option UInt8 × List UInt8 × List Value := Id.run do
  let (initial, tail) := flags bytes {}
  let mut options := initial
  let mut bytes := tail
  let mut values := values
  match bytes with
  | 42 :: rest =>
      let (value, remaining) := argument values
      let width := (Int32.ofInt (Numeric.integer value)).toInt
      options := { options with
        left := options.left || (width < 0)
        width := if width == -2147483648 then 0 else width.natAbs }
      bytes := rest
      values := remaining
  | _ =>
      let (digits, rest) := bytes.span digit
      options := { options with width := decimal digits }
      bytes := rest
  match bytes with
  | 46 :: rest =>
      match rest with
      | 42 :: rest =>
          let (value, remaining) := argument values
          let precision := (Int32.ofInt (Numeric.integer value)).toInt
          let precision := if precision == -2147483648 then none else some precision.natAbs
          options := { options with precision }
          bytes := rest
          values := remaining
      | _ =>
          let (digits, rest) := rest.span digit
          options := { options with precision := some (decimal digits) }
          bytes := rest
  | _ => pure ()
  bytes := match bytes with
    | 108 :: 108 :: rest => rest
    | 108 :: rest => rest
    | _ => bytes
  match bytes with
  | [] => return (options, none, [], values)
  | code :: rest => return (options, some code, rest, values)

private def ascii (text : String) : List UInt8 := text.toUTF8.data.toList

private def spaces (count : Nat) : List UInt8 := List.replicate count 32

private def widthPad (options : Options) (value : List UInt8) (written : Nat) :
    Except String (List UInt8) := do
  let extra := if options.characters && options.width > 0 then
    (value.filter Text.continuation).length else 0
  let pad := options.width + extra - value.length
  Limits.check (written + value.length + pad) 1
  return if options.left then value ++ spaces pad else spaces pad ++ value

private def digitsFuel : Nat → Nat → Nat → Bool → List UInt8
  | 0, _, _, _ => []
  | fuel + 1, value, base, upper =>
      let d := value % base
      let byte := UInt8.ofNat (if d < 10 then 48 + d else (if upper then 55 else 87) + d)
      if value < base then [byte] else digitsFuel fuel (value / base) base upper ++ [byte]

private def grouped (value : List UInt8) : List UInt8 :=
  value.zipIdx |>.flatMap fun (byte, index) =>
    if index > 0 && (value.length - index) % 3 == 0 then [44, byte] else [byte]

def integer (options : Options) (code : UInt8) (value : Value) (written : Nat) :
    Except String (List UInt8) := do
  let signed := [100, 105, 114].contains code.toNat
  let value := Numeric.integer value
  let magnitude := if signed then value.natAbs else (value % 18446744073709551616).toNat
  let sign := if signed then (if value < 0 then "-" else options.sign) else ""
  let base := if [120, 88, 112].contains code.toNat then 16 else if code == 111 then 8 else 10
  let suffix := if code == 114 then
      if (magnitude / 10) % 10 == 1 then "th" else
        match magnitude % 10 with | 1 => "st" | 2 => "nd" | 3 => "rd" | _ => "th"
    else ""
  let digits := digitsFuel 64 magnitude base (code == 88 || code == 112) ++ ascii suffix
  let precision := max (options.precision.getD 0)
    (if options.zero then options.width - sign.utf8ByteSize else 0)
  let commas := options.commas && [100, 105, 117].contains code.toNat
  if precision ≥ 37 then Limits.check (precision + 10 + (if commas then precision / 3 else 0))
  let length := max precision digits.length
  Limits.check (written + length + (if commas then (length - 1) / 3 else 0) + sign.utf8ByteSize) 1
  let digits := List.replicate (precision - digits.length) 48 ++ digits
  let digits := if commas then grouped digits else digits
  let radix := if options.alternate && magnitude != 0 then
      if code == 120 || code == 112 then "0x" else if code == 88 then "0X"
      else if code == 111 then "0" else ""
    else ""
  widthPad { options with characters := false } (ascii radix ++ ascii sign ++ digits) written

private def trimZeros (bytes : List Char) : List Char := (bytes.reverse.dropWhile (· == '0')).reverse
private def digitsValue (bytes : List Char) : Nat := bytes.foldl (fun n c => n * 10 + c.toNat - 48) 0

/-- sqlite3FpDecode's general precision path. Input is a positive finite
magnitude; the existing 17-digit round-trip shortening path is shared. -/
def decodeFloat (value : Float) (roundAt : Int) (maximum : Nat) : String × Int := Id.run do
  if value == 0.0 then return ("0", 1)
  let bits := value.toBits.toNat
  let exponent := (bits >>> 52) &&& 2047
  let mantissa := bits &&& (2^52 - 1)
  let (mantissa, exponent) := if exponent == 0 then
      let leading := 64 - (mantissa.log2 + 1)
      (mantissa <<< leading, -1074 - Int.ofNat leading)
    else ((mantissa <<< 11) ||| 2^63, Int.ofNat exponent - 1086)
  let count := if roundAt ≤ 0 || roundAt ≥ 18 then 18 else roundAt + 1
  let power := count - 1 - FloatCodec.power2to10 (exponent + 63)
  let high := (FloatCodec.multiply128 mantissa (FloatCodec.powerOfTen power).1).1
  let digits := if count == 18 then
      let high := high >>> (-(exponent + FloatCodec.power10to2 power + 2)).toNat
      (high + ((high <<< 1) &&& 2)) >>> 1
    else high >>> (-(exponent + FloatCodec.power10to2 power + 1)).toNat
  let mut raw := (toString digits).toList
  let mut point := Int.ofNat raw.length - power
  let mut rounding := if roundAt ≤ 0 then point - roundAt else roundAt
  if roundAt ≤ 0 && rounding == 0 && raw.head! ≥ '5' then
    raw := '0' :: raw
    point := point + 1
    rounding := 1
  if rounding > 0 && (rounding < Int.ofNat raw.length || raw.length > maximum) then
    let count := min rounding.toNat maximum
    if count == 17 then return FloatCodec.decode17 value
    let rounded := digitsValue (raw.take count) + (if raw[count]! ≥ '5' then 1 else 0)
    let digits := (toString rounded).toList
    if digits.length > count then point := point + 1
    return (String.ofList (trimZeros digits), point)
  return (String.ofList (trimZeros raw), point)

private def floatPad (options : Options) (sign body : String) (written : Nat) :
    Except String (List UInt8) := do
  let size := sign.utf8ByteSize + body.utf8ByteSize
  let pad := options.width - size
  Limits.check (written + size + pad) 1
  if options.left then return ascii (sign ++ body) ++ spaces pad
  if options.zero then return ascii sign ++ List.replicate pad 48 ++ ascii body
  return spaces pad ++ ascii (sign ++ body)

def floating (options : Options) (code : UInt8) (value : Value) (written : Nat) :
    Except String (List UInt8) := do
  let real := Numeric.real value
  if real.isNaN then
    return ← widthPad { options with characters := false } (ascii (if options.zero then "null" else "NaN")) written
  let negative := real < 0.0
  let sign := if negative then "-" else options.sign
  if !real.isFinite && !options.zero then
    return ← widthPad { options with characters := false } (ascii (sign ++ "Inf")) written
  let precision := min (options.precision.getD 6) 100000000
  let generic := code == 103 || code == 71
  let precision := if generic then max 1 precision else precision
  let roundAt : Int := if code == 102 then -(Int.ofNat precision)
    else if generic then Int.ofNat precision else Int.ofNat precision + 1
  let (digits, point) := if !real.isFinite then ("9", 1000) else
    decodeFloat (if negative then -real else real) roundAt (if options.characters then 20 else 16)
  let sign := if negative && options.alternate && options.sign.isEmpty && code == 102 && point ≤ roundAt
    then "" else sign
  let exponent := point - 1
  let exponential := if generic then exponent < -4 || exponent > Int.ofNat (precision - 1)
    else code == 101 || code == 69
  let precision := if generic then
      if exponential then precision - 1 else (Int.ofNat precision - point).toNat
    else precision
  let before : Int := if exponential then 1 else point
  let trim := if generic then !options.alternate else options.characters
  let dot := precision > 0 || options.alternate || options.characters
  let extraCommas := if options.commas && before > 1 then (before.toNat + 1) / 3 else 0
  Limits.check (written + (before - 1).toNat + precision + options.width + 10 + extraCommas)
  let chars := digits.toList
  let whole := if before ≤ 0 then ['0'] else
    chars.take before.toNat ++ List.replicate (before.toNat - chars.length) '0'
  let whole := if options.commas then grouped (ascii (String.ofList whole)) else ascii (String.ofList whole)
  let fractional := if before ≤ 0 then List.replicate (-before).toNat '0' ++ chars
    else chars.drop before.toNat
  let fractional := fractional.take precision
  let fractional := if trim then trimZeros fractional
    else fractional ++ List.replicate (precision - fractional.length) '0'
  let fractional := if dot then
      if fractional.isEmpty && trim then (if options.characters then ".0" else "")
      else "." ++ String.ofList fractional
    else ""
  let suffix := if exponential then
      let power := toString exponent.natAbs
      (if code == 69 || code == 71 then "E" else "e") ++ (if exponent < 0 then "-" else "+") ++
        (if power.length < 2 then "0" else "") ++ power
    else ""
  floatPad options sign ((String.fromUTF8! (ByteArray.mk whole.toArray)) ++ fractional ++ suffix) written

private def textPrefix (value : Value) : List UInt8 :=
  (Text.bytes value).toList.takeWhile (· != 0)

private def shortened (options : Options) (bytes : List UInt8) : List UInt8 :=
  match options.precision with
  | none => bytes
  | some count => if options.characters then
      (Text.characterSpans bytes.toArray).take count |>.flatten else bytes.take count

def quoted (options : Options) (code : UInt8) (value : Value) (written : Nat) :
    Except String (List UInt8) := do
  let isNull := Text.isNull value
  let source := shortened options (if isNull then ascii (if code == 81 then "NULL" else "(NULL)")
    else textPrefix value)
  let quote := if code == 119 then 34 else 39
  let escapes := options.alternate && code != 119 && (code == 113 || source.any (· ≤ 31))
  let quoted := code == 81 && !isNull
  let opening :=  if quoted then (if escapes then "unistr('" else "'") else ""
  let close := if quoted then (if escapes then "')" else "'") else ""
  let encode := fun byte => if escapes then UnicodeEscape.quoteByte byte
    else if byte == quote then [byte, byte] else [byte]
  let count := source.foldl (fun n byte => n + (encode byte).length) 0
  Limits.check (count + 3 + (if quoted && escapes then 10 else 0))
  widthPad options (ascii opening ++ source.flatMap encode ++ ascii close) written

def character (options : Options) (value : Value) (written : Nat) :
    Except String (List UInt8) := do
  let source := Text.bytes value |>.toList
  let bytes := match source with
    | [] => [0]
    | first :: rest => first :: (if first ≥ 192 then (rest.takeWhile Text.continuation).take 3 else [])
  let count := max 1 (options.precision.getD 1)
  let width := Int.ofNat options.width - Int.ofNat (count - 1)
  let pad := if width > 1 && !options.left then (width - 1).toNat else
    (width + (if width > 0 then Int.ofNat (bytes.filter Text.continuation).length else 0) -
      Int.ofNat bytes.length).toNat
  Limits.check (written + count * bytes.length + pad) 1
  let output := (List.replicate count bytes).flatten
  return if options.left then output ++ spaces pad else spaces pad ++ output

/-- An absent conversion produces no output and consumes no value. SQL %n
is a successful empty conversion and also consumes no value. -/
def field (options : Options) (code : UInt8) (values : List Value) (written : Nat) :
    Except String (Option (List UInt8 × List Value)) := do
  if code == 110 then return some ([], values)
  if code == 37 then return some (← widthPad { options with characters := false } [37] written, values)
  let (value, rest) := argument values
  if [100, 105, 117, 120, 88, 111, 112, 114].contains code.toNat then
    return some (← integer options code value written, rest)
  if [102, 101, 69, 103, 71].contains code.toNat then
    return some (← floating options code value written, rest)
  if [115, 122].contains code.toNat then
    return some (← widthPad options (shortened options (if Text.isNull value then [] else textPrefix value)) written, rest)
  if [113, 81, 119].contains code.toNat then
    return some (← quoted options code value written, rest)
  if code == 99 then return some (← character options value written, rest)
  return none

def runFuel : Nat → List UInt8 → List Value → Array UInt8 → Bool → Except String Value
  | 0, _, _, _, _ => .error "format parser fuel exhausted"
  | _ + 1, [], _, output, allocated => .ok (if allocated then Text.fromBytes output else .null)
  | fuel + 1, byte :: rest, values, output, allocated => do
      if byte != 37 then
        let (literal, rest) := (byte :: rest).span (· != 37)
        Limits.check (output.size + literal.length) 1
        runFuel fuel rest values (output ++ literal.toArray) true
      else if rest.isEmpty then
        Limits.check (output.size + 1) 1
        return Text.fromBytes (output.push 37)
      else
        let (options, code, rest, values) := parse rest values
        match code with
        | none => return if allocated then Text.fromBytes output else .null
        | some code =>
            match ← field options code values output.size with
            | none => return if allocated then Text.fromBytes output else .null
            | some (bytes, values) =>
                Limits.check (output.size + bytes.length) 1
                runFuel fuel rest values (output ++ bytes.toArray) true

def evaluate : List Value → Except String Value
  | [] | .null :: _ => .ok .null
  | format :: values =>
      let bytes := textPrefix format
      runFuel (bytes.length + 1) bytes values #[] false

theorem evaluate_no_arguments : evaluate [] = .ok .null := rfl

theorem evaluate_null (values : List Value) : evaluate (.null :: values) = .ok .null := rfl

theorem field_count_ignored (options : Options) (values : List Value) (written : Nat) :
    field options 110 values written = .ok (some ([], values)) := by
  simp [field]
  rfl

end SQLeanite.SQLite.Format
