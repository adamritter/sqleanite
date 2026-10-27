import SQLeanite.SQLite.PhysicalAffinity

/-! SUM, AVG and TOTAL's ordered accumulator, ported from SQLite 3.53.4
func.c. Integer input stays exact until overflow or a non-integer input;
approximate sums use Kahan-Babushka-Neumaier compensation. This algorithmic
port and its component contracts are not a whole-SQLite equivalence proof. -/
namespace SQLeanite.SQLite.AggregateSum

abbrev Value := PhysicalCodec.Value

structure State where
  integerSum : Int := 0
  count : Nat := 0
  approximate : Bool := false
  overflow : Bool := false
  realSum : Float := 0.0
  error : Float := 0.0

/-- sqlite3_value_numeric_type uses numeric affinity without the extra
integer conversion of decimal/exponent TEXT; BLOB always remains BLOB. -/
def numericType : Value → SQLeanite.Value
  | .null => .null
  | .integer i => .integer i.value
  | .realBits bits => .real (Float.ofBits (UInt64.ofNat bits.val))
  | .blob bytes => .blob bytes.bytes.toArray
  | .text bytes =>
      let text := String.ofList (bytes.bytes.map (fun byte => Char.ofNat byte.toNat))
      let parsed := Numeric.parsePrefix text
      if !parsed.completeToNul then .text text
      else if parsed.floating then .real (Numeric.realPrefix text)
      else Numeric.applyAffinity (.text text)

def State.addReal (state : State) (value : Float) : State :=
  let previous := state.realSum
  let next := previous + value
  let adjustment := if previous.abs > value.abs then (previous - next) + value
    else (value - next) + previous
  { state with realSum := next, error := state.error + adjustment }

/-- Split wide integers at 14 bits before converting to binary64. The
remainder uses C's truncation toward zero, including for negative integers. -/
def State.addInteger (state : State) (value : Int) : State :=
  if value ≤ -4503599627370496 || 4503599627370496 ≤ value then
    let small := value.tmod 16384
    (state.addReal (Float.ofInt (value - small))).addReal (Float.ofInt small)
  else state.addReal (Float.ofInt value)

def State.initializeReal (state : State) : State :=
  if state.integerSum ≤ -4503599627370496 || 4503599627370496 ≤ state.integerSum then
    let small := state.integerSum.tmod 16384
    { state with realSum := Float.ofInt (state.integerSum - small), error := Float.ofInt small }
  else { state with realSum := Float.ofInt state.integerSum, error := 0.0 }

def State.step (state : State) (input : Value) : State :=
  match numericType input with
  | .null => state
  | .integer value =>
      let state := { state with count := state.count + 1 }
      if state.approximate then state.addInteger value
      else if Numeric.fits (state.integerSum + value) then
        { state with integerSum := state.integerSum + value }
      else
        ({ state.initializeReal with approximate := true, overflow := true }).addInteger value
  | value =>
      let state := { state with count := state.count + 1, overflow := false }
      let state := if state.approximate then state
        else { state.initializeReal with approximate := true }
      state.addReal (Numeric.real value)

/-- Sliding-window inverse from sqlite3 sumInverse. Approximate mode persists
when the floating input leaves the frame; removing INT64_MIN uses two steps. -/
def State.inverse (state : State) (input : Value) : State :=
  match numericType input with
  | .null => state
  | value => Id.run do
      let mut state := { state with count := state.count - 1 }
      if !state.approximate then
        let amount := Numeric.integer value
        if Numeric.fits (state.integerSum - amount) then
          return { state with integerSum := state.integerSum - amount }
        state := { state.initializeReal with approximate := true, overflow := true }
      match value with
      | .integer amount =>
          if amount == -9223372036854775808 then
            return (state.addInteger 9223372036854775807).addInteger 1
          return state.addInteger (-amount)
      | _ => return state.addReal (-(Numeric.real value))

theorem State.inverse_null (state : State) : state.inverse .null = state := rfl

def accumulate (values : List Value) : State := values.foldl State.step {}

/-- An infinite or NaN compensation term is discarded, as in sqlite3IsOverflow.
A NaN final result is SQL NULL, the sqlite3_result_double convention. -/
def State.total (state : State) : Float :=
  if !state.approximate then Float.ofInt state.integerSum
  else if state.error.isInf || state.error.isNaN then state.realSum
  else state.realSum + state.error

def realValue (value : Float) : Value :=
  if value.isNaN then .null
  else
    let bits := value.toBits
    .realBits ⟨bits.toNat, by simpa using bits.toNat_lt⟩

def State.sumResult (state : State) : Except String Value :=
  if state.count == 0 then .ok .null
  else if state.approximate then
    if state.overflow then .error "integer overflow"
    else .ok (realValue state.total)
  else match PhysicalAffinity.number? (.integer state.integerSum) with
    | some number => .ok (PhysicalAffinity.numberValue number)
    | none => .error "integer overflow"

def sum (values : List Value) : Except String Value := (accumulate values).sumResult

def average (values : List Value) : Value :=
  let state := accumulate values
  if state.count == 0 then .null
  else realValue (state.total / Float.ofNat state.count)

def total (values : List Value) : Value := realValue (accumulate values).total

theorem State.step_null (state : State) : state.step .null = state := rfl

theorem accumulate_nulls (count : Nat) : accumulate (List.replicate count .null) = {} := by
  have unchanged (values : List Value) (state : State)
      (nulls : ∀ value ∈ values, value = .null) : values.foldl State.step state = state := by
    induction values generalizing state with
    | nil => rfl
    | cons value values ih =>
        have head := nulls value (by simp)
        simp only [List.foldl_cons, head, State.step_null]
        exact ih state (fun v hv => nulls v (by simp [hv]))
  exact unchanged _ _ (by simp)

theorem sum_nulls (count : Nat) : sum (List.replicate count .null) = .ok .null := by
  simp [sum, accumulate_nulls, State.sumResult]

theorem average_nulls (count : Nat) : average (List.replicate count .null) = .null := by
  simp [average, accumulate_nulls]

end SQLeanite.SQLite.AggregateSum
