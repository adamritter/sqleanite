import SQLeanite.SQLite.Format

/-! Pure deterministic date/time operations ported from the pinned SQLite
3.53.4 src/date.c. Julian milliseconds and cached civil/time fields are kept
separate because SQLite deliberately retains some unnormalized input fields.
Host current-time and local timezone services are explicit unsupported seams.
No SQLite or project-native date binding is used. -/
namespace SQLeanite.SQLite.DateTime

structure Civil where
  year : Int := 2000
  month : Int := 1
  day : Int := 1
  deriving Repr

structure Clock where
  hour : Int := 0
  minute : Int := 0
  second : Float := 0.0
  deriving Repr

structure State where
  jd : Option Int := none
  civil : Option Civil := none
  clock : Option Clock := none
  raw : Option Float := none
  floorDays : Int := 0
  subsec : Bool := false
  deriving Repr

def valid (jd : Int) : Bool := 0 ≤ jd && jd ≤ 464269060799999

def monthDays (year month : Int) : Int :=
  if month == 2 then
    if year % 4 != 0 || (year % 100 == 0 && year % 400 != 0) then 28 else 29
  else if [4, 6, 9, 11].contains month then 30 else 31

def overflow (date : Civil) : Int := max 0 (date.day - monthDays date.year date.month)

def julian (date : Civil) (time : Clock) : Option Int := do
  if date.year < -4713 || date.year > 9999 then none else do
    let y := date.year - (if date.month ≤ 2 then 1 else 0)
    let m := date.month + (if date.month ≤ 2 then 12 else 0)
    let a := (y + 4800) / 100
    let b := 38 - a + a / 4
    let x1 := 36525 * (y + 4716) / 100
    let x2 := 306001 * (m + 1) / 10000
    return (x1 + x2 + date.day + b) * 86400000 - 131716800000 +
      time.hour * 3600000 + time.minute * 60000 +
      Numeric.realToInteger (time.second * 1000.0 + 0.5)

def compute (state : State) : Option State := do
  if state.jd.isSome then some state
  else if state.raw.isSome then none
  else return { state with jd := some (← julian (state.civil.getD {}) (state.clock.getD {})) }

def clear (state : State) : State := { state with civil := none, clock := none }

def civilOf (jd : Int) : Civil :=
  let z := (jd + 43200000) / 86400000
  let alpha := (4 * z + 128179) / 146097 - 52
  let a := z + 1 + alpha - (alpha + 100) / 4 + 25
  let b := a + 1524
  let c := (100 * b - 12210) / 36525
  let d := 36525 * (c % 32768) / 100
  let e := (10000 * (b - d)) / 306001
  let m := if e < 14 then e - 1 else e - 13
  { year := c - (if m > 2 then 4716 else 4715), month := m,
    day := b - d - 306001 * e / 10000 }

def clockOf (jd : Int) : Clock :=
  let ms := (jd + 43200000) % 86400000
  { hour := ms / 3600000, minute := ms / 60000 % 60,
    second := Float.ofInt (ms % 60000) / 1000.0 }

def fields (state : State) : State :=
  { state with
    civil := some (state.civil.getD (civilOf (state.jd.getD 0)))
    clock := some (state.clock.getD (clockOf (state.jd.getD 0)))
    raw := if state.clock.isNone then none else state.raw }

def digits (input : List Char) (width : Nat) (lo hi : Int) : Option (Int × List Char) := do
  let taken := input.take width
  if taken.length != width || !taken.all Char.isDigit then none else do
    let n : Int := taken.foldl (fun n c => n * 10 + Int.ofNat (c.toNat - 48)) 0
    if n < lo || hi < n then none else some (n, input.drop width)

def separator (wanted : Char) : List Char → Option (List Char)
  | c :: rest => if c == wanted then some rest else none
  | [] => none

def timezone (input : List Char) : Option Int := do
  let input := input.dropWhile Numeric.space
  match input with
  | [] => some 0
  | 'z' :: rest | 'Z' :: rest => if (rest.dropWhile Numeric.space).isEmpty then some 0 else none
  | sign :: rest => do
      if sign != '+' && sign != '-' then none else do
        let (h, rest) ← digits rest 2 0 14
        let rest ← separator ':' rest
        let (m, rest) ← digits rest 2 0 59
        if !(rest.dropWhile Numeric.space).isEmpty then none
        else some ((h * 60 + m) * if sign == '-' then -1 else 1)

def parseClock (input : List Char) : Option (Clock × Int) := do
  let (h, rest) ← digits input 2 0 24
  let rest ← separator ':' rest
  let (m, rest) ← digits rest 2 0 59
  let (s, rest) ← match rest with
    | ':' :: rest => do
        let (s, rest) ← digits rest 2 0 59
        match rest with
        | '.' :: next :: rest =>
            if next.isDigit then do
              let (fraction, tail) := (next :: rest).span Char.isDigit
              let pair := fraction.foldl (fun (a, b) c =>
                (a * 10.0 + Float.ofNat (c.toNat - 48), b * 10.0)) (0.0, 1.0)
              let f := pair.1 / pair.2
              some (Float.ofInt s + (if f > 0.999 then 0.999 else f), tail)
            else none
        | _ => some (Float.ofInt s, rest)
    | _ => some (0.0, rest)
  return ({ hour := h, minute := m, second := s }, ← timezone rest)

def fromParts (civil : Option Civil) (clock : Option Clock) (tz : Int) : Option State := do
  let state : State := { civil, clock, floorDays := civil.map overflow |>.getD 0 }
  if tz == 0 then some state
  else
    let state ← compute state
    return clear { state with jd := state.jd.map (· - tz * 60000) }

def parseCivil (input : List Char) : Option State := do
  let (negative, input) := match input with | '-' :: rest => (true, rest) | _ => (false, input)
  let (y, rest) ← digits input 4 0 9999
  let rest ← separator '-' rest
  let (m, rest) ← digits rest 2 1 12
  let rest ← separator '-' rest
  let (d, rest) ← digits rest 2 1 31
  let rest := rest.dropWhile (fun c => Numeric.space c || c == 'T')
  let date : Civil := { year := if negative then -y else y, month := m, day := d }
  if rest.isEmpty then fromParts (some date) none 0
  else
    let (time, tz) ← parseClock rest
    fromParts (some date) (some time) tz

def rawNumber (number : Float) : State :=
  { raw := some number,
    jd := if number ≥ 0.0 && number < 5373484.5 then
      some (Numeric.realToInteger (number * 86400000.0 + 0.5)) else none }

/-- Date parsers use SQLite's NUL-terminated byte view; non-ASCII bytes cannot
form a date token, and are never silently removed from a BLOB. -/
def stringValue (value : Value) : String :=
  String.ofList ((Text.bytes value).toList.takeWhile (· != 0) |>.map (fun b => Char.ofNat b.toNat))

def number? (source : String) : Option Float :=
  if (Numeric.parsePrefix source).complete then some (Numeric.realPrefix source) else none

def parseValue : Value → Option State
  | .null => none
  | .integer value => some (rawNumber (Float.ofInt value))
  | .real value => some (rawNumber value)
  | value =>
      let source := stringValue value
      (parseCivil source.toList).orElse fun _ =>
        ((parseClock source.toList).bind fun (clock, tz) => fromParts none (some clock) tz).orElse fun _ =>
          rawNumber <$> number? source

def unix (state : State) : Option State := do
  let raw ← state.raw
  let n := raw * 1000.0 + 210866760000000.0
  if n < 0.0 || n ≥ 464269060800000.0 then none
  else return clear { state with jd := some (Numeric.realToInteger (n + 0.5)), raw := none }

def shiftMonths (date : Civil) (months : Int) : Civil :=
  let m := date.month + months
  let years := (m - 1) / 12
  { date with year := date.year + years, month := m - years * 12 }

def shiftCalendar (state : State) (years months : Int) : Option State := do
  let state := fields (← compute state)
  let date := state.civil.getD {}
  let date := shiftMonths { date with year := date.year + years } months
  compute { state with civil := some date, jd := none, floorDays := overflow date }

def numericModifier (state : State) (source : String) : Option State := do
  let input := source.toList
  let first ← input.head?
  if first != '+' && first != '-' && !first.isDigit then none else do
    let (token, rest) := input.span (fun c => !Numeric.space c)
    let n ← number? (String.ofList token)
    let unit := String.ofList (rest.dropWhile Numeric.space)
    let unit := if unit.endsWith "s" then (unit.dropEnd 1).toString else unit
    let (limit, scale) ← match unit with
      | "second" => some (464269992787968.0, 1.0)
      | "minute" => some (7737900007424.0, 60.0)
      | "hour" => some (128969998336.0, 3600.0)
      | "day" => some (5373485.0, 86400.0)
      | "month" => some (176546.0, 2592000.0)
      | "year" => some (14713.0, 31536000.0)
      | _ => none
    if n ≤ -limit || n ≥ limit then none else do
      let state ← compute { state with floorDays := 0 }
      let integer := Numeric.realToInteger n
      let state ← if unit == "month" then shiftCalendar state 0 integer
        else if unit == "year" then shiftCalendar state integer 0 else some state
      let fraction := if unit == "month" || unit == "year" then n - Float.ofInt integer else n
      let delta := Numeric.realToInteger (fraction * 1000.0 * scale + if n < 0.0 then -0.5 else 0.5)
      return clear { state with jd := state.jd.map (· + delta) }

def clockModifier (state : State) (source : String) : Option State := do
  let input := source.toList
  let (negative, input) := match input with
    | '-' :: rest => (true, rest) | '+' :: rest => (false, rest) | _ => (false, input)
  let (time, tz) ← parseClock input
  let encoded ← fromParts none (some time) tz >>= compute
  let delta := ((encoded.jd.getD 0) - 43200000) % 86400000
  let state ← compute state
  return clear { state with jd := state.jd.map (· + if negative then -delta else delta) }

def calendarModifier (state : State) (source : String) : Option State := do
  let (negative, input) ← match source.toList with
    | '-' :: rest => some (true, rest) | '+' :: rest => some (false, rest) | _ => none
  let width := if input[4]? == some '-' then 4 else 5
  let (y, rest) ← digits input width 0 14712
  let rest ← separator '-' rest
  let (m, rest) ← digits rest 2 0 11
  let rest ← separator '-' rest
  let (d, rest) ← digits rest 2 0 30
  let sign : Int := if negative then -1 else 1
  let state ← shiftCalendar state (sign * y) (sign * m)
  let state := clear { state with jd := state.jd.map (· + sign * d * 86400000) }
  if rest.isEmpty then some state
  else match rest with
    | c :: tail => if Numeric.space c then
        clockModifier state ((if negative then "-" else "+") ++ String.ofList tail) else none
    | [] => none

def modifier (state : State) (index : Nat) (value : Value) : Option State := do
  if Text.isNull value then none else do
    let source := (stringValue value).toLower
    if source == "subsec" || source == "subsecond" then return { state with subsec := true }
    if source == "unixepoch" then if index == 1 then unix state else none
    else if source == "julianday" then
      if index == 1 && state.raw.isSome && state.jd.isSome then some { state with raw := none } else none
    else if source == "auto" then
      if index != 1 then none
      else if state.raw.isNone || state.jd.isSome then some { state with raw := none }
      else if state.raw.any (fun n => n ≥ -210866760000.0 && n ≤ 253402300799.0) then unix state
      else some state
    else if source == "ceiling" || source == "floor" then
      let state ← compute state
      return clear { state with
        jd := state.jd.map (· - if source == "floor" then state.floorDays * 86400000 else 0)
        floorDays := if source == "ceiling" then 0 else state.floorDays }
    else if source.startsWith "weekday " then
      let n ← number? (source.drop 8).toString
      let weekday := Numeric.realToInteger n
      if n < 0.0 || n ≥ 7.0 || n != Float.ofInt weekday then none else do
        let state := fields (← compute state)
        let state ← compute { state with jd := none }
        let day := ((state.jd.getD 0 + 129600000) / 86400000) % 7
        return clear { state with jd := state.jd.map (· + ((weekday - day) % 7) * 86400000) }
    else if source.startsWith "start of " then
      if state.jd.isNone && state.civil.isNone && state.clock.isNone then none else do
        let state := fields (← compute state)
        let date := state.civil.getD {}
        let date ← match (source.drop 9).toString with
          | "year" => some { date with month := 1, day := 1 }
          | "month" => some { date with day := 1 }
          | "day" => some date
          | _ => none
        return { state with jd := none, civil := some date, clock := some {}, raw := none }
    else (calendarModifier state source).orElse fun _ =>
      (clockModifier state source).orElse fun _ => numericModifier state source

def arguments (values : List Value) : Option State := do
  let first ← values.head?
  let state ← parseValue first
  let state ← (values.drop 1).zipIdx.foldlM (fun state (value, index) => modifier state (index+1) value) state
  let state ← compute state
  if !valid (state.jd.getD (-1)) then none
  else return if values.length == 1 && state.civil.any (fun date => date.day > 28) then
    { state with civil := none } else state

def pad (width : Nat) (value : Int) (space : Bool := false) : String :=
  let digits := toString value.natAbs
  let sign := if value < 0 then "-" else ""
  let zeros := String.ofList (List.replicate (width - digits.length - sign.length) (if space then ' ' else '0'))
  if space then zeros ++ sign ++ digits else sign ++ zeros ++ digits

def printf (format : String) (value : Value) : String :=
  ((Format.evaluate [.text format, value]).toOption.map toString).getD ""

def dateText (date : Civil) (iso : Bool := false) : String :=
  pad (if iso && date.year < 0 then 5 else 4) date.year ++ "-" ++ pad 2 date.month ++ "-" ++ pad 2 date.day

def clockText (time : Clock) (subsec : Bool) : String :=
  pad 2 time.hour ++ ":" ++ pad 2 time.minute ++ ":" ++
    if subsec then printf "%06.3f" (.real time.second) else pad 2 (Numeric.realToInteger time.second)

def yearDay (state : State) : Int :=
  let date := state.civil.getD {}
  let jan := (julian { date with month := 1, day := 1 } (state.clock.getD {})).getD 0
  ((state.jd.getD 0) - jan + 43200000) / 86400000

def substitution (state : State) (code : Char) : Option String := do
  let date := state.civil.getD {}
  let time := state.clock.getD {}
  let jd := state.jd.getD 0
  let monday := ((jd + 43200000) / 86400000) % 7
  let sunday := ((jd + 129600000) / 86400000) % 7
  let thursday := fields { state with jd := some (jd + (3 - monday) * 86400000), civil := none }
  match code with
  | 'd' => some (pad 2 date.day) | 'e' => some (pad 2 date.day true)
  | 'f' => some (printf "%06.3f" (.real (min time.second 59.999)))
  | 'F' => some (dateText date)
  | 'G' => some (pad 4 (thursday.civil.getD {}).year)
  | 'g' => some (pad 2 ((thursday.civil.getD {}).year.tmod 100))
  | 'H' => some (pad 2 time.hour) | 'k' => some (pad 2 time.hour true)
  | 'I' | 'l' => some (pad 2 (if time.hour == 0 then 12 else if time.hour > 12 then time.hour - 12 else time.hour) (code == 'l'))
  | 'j' => some (pad 3 (yearDay state + 1))
  | 'J' => some (printf "%.16g" (.real (Float.ofInt jd / 86400000.0)))
  | 'm' => some (pad 2 date.month) | 'M' => some (pad 2 time.minute)
  | 'p' => some (if time.hour ≥ 12 then "PM" else "AM")
  | 'P' => some (if time.hour ≥ 12 then "pm" else "am")
  | 'R' => some (pad 2 time.hour ++ ":" ++ pad 2 time.minute)
  | 's' => some (if state.subsec then printf "%.3f" (.real (Float.ofInt (jd - 210866760000000) / 1000.0))
      else toString (jd / 1000 - 210866760000))
  | 'S' => some (pad 2 (Numeric.realToInteger time.second))
  | 'T' => some (clockText time false)
  | 'u' => some (toString (if sunday == 0 then 7 else sunday))
  | 'w' => some (toString sunday)
  | 'U' => some (pad 2 ((yearDay state - sunday + 7) / 7))
  | 'V' => some (pad 2 (yearDay thursday / 7 + 1))
  | 'W' => some (pad 2 ((yearDay state - monday + 7) / 7))
  | 'Y' => some (pad 4 date.year) | '%' => some "%"
  | _ => none

def formatBytes (state : State) : List UInt8 → Option (List UInt8)
  | [] => some []
  | 0 :: _ => some []
  | 37 :: code :: rest => do
      let field ← substitution state (Char.ofNat code.toNat)
      return field.toUTF8.data.toList ++ (← formatBytes state rest)
  | [37] => none
  | byte :: rest => (byte :: ·) <$> formatBytes state rest

def names : List String := ["date", "time", "datetime", "julianday", "unixepoch", "strftime"]

def render (name : String) (values : List Value) : Value :=
  let inputs := if name == "strftime" then values.drop 1 else values
  match arguments inputs with
  | none => .null
  | some state =>
      let state := fields state
      let date := state.civil.getD {}
      let time := state.clock.getD {}
      match name with
      | "date" => .text (dateText date true)
      | "time" => .text (clockText time state.subsec)
      | "datetime" => .text (dateText date true ++ " " ++ clockText time state.subsec)
      | "julianday" => .real (Float.ofInt (state.jd.getD 0) / 86400000.0)
      | "unixepoch" => if state.subsec then .real (Float.ofInt (state.jd.getD 0 - 210866760000000) / 1000.0)
        else .integer (state.jd.getD 0 / 1000 - 210866760000)
      | "strftime" =>
          match values.head? with
          | none | some .null => .null
          | some format => match formatBytes state (Text.bytes format).toList with
            | none => .null | some bytes => Text.fromBytes bytes.toArray
      | _ => .null

/-- Unsupported host-dependent services are reported explicitly, not silently
converted into SQL NULL. Invalid deterministic date inputs produce SQL NULL. -/
def evaluate? (name : String) (values : List Value) : Option (Except String Value) :=
  if !names.contains name then none
  else
    let inputs := if name == "strftime" then values.drop 1 else values
    let current := inputs.isEmpty && (name != "strftime" || !values.isEmpty) ||
      inputs.head?.any (fun value => ["now", "subsec", "subsecond"].contains (stringValue value).toLower)
    let usesLocal :=  (inputs.drop 1).any (fun value => ["localtime", "utc"].contains (stringValue value).toLower)
    if current || usesLocal then some (.error "unsupported verified SQL: date/time host clock or timezone service")
    else some (.ok (render name values))

theorem parseValue_null : parseValue .null = none := rfl
theorem arguments_null (rest : List Value) : arguments (.null :: rest) = none := by
  simp [arguments, parseValue, bind, Option.bind]
theorem evaluate_unknown (name : String) (values : List Value) (unknown : names.contains name = false) :
    evaluate? name values = none := by
  unfold evaluate?
  rw [unknown]
  rfl

end SQLeanite.SQLite.DateTime
