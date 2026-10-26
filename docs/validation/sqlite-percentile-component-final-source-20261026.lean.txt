import SQLeanite.SQLite.Math

/-! Ordinary percentile accumulators from pinned SQLite 3.53.4 func.c.
The tested AArch64 oracle contracts interpolation to an FMADD instruction;
Float.fma retains that rounding through Lean's existing Float implementation.
This module adds no project-native binding or external SQLite dependency. -/
namespace SQLeanite.SQLite.Percentile

inductive Kind where
  | median | percentile | continuous | discrete
  deriving BEq, DecidableEq, Repr

def Kind.name : Kind → String
  | .median => "median"
  | .percentile => "percentile"
  | .continuous => "percentile_cont"
  | .discrete => "percentile_disc"

structure State where
  fraction : Option Float := none
  values : Array Float := #[]

def fraction (kind : Kind) (value : Value) : Except String Float := do
  if kind == .median then return 0.5
  let maximum := if kind == .percentile then 100.0 else 1.0
  let error := "the fraction argument to " ++ kind.name ++ "() is not between 0.0 and " ++
    (if kind == .percentile then "100.0" else "1.0")
  let some numeric := Math.numeric? value | throw error
  let result := Numeric.real numeric / maximum
  if result < 0.0 || result > 1.0 then throw error
  return result

def State.step (state : State) (kind : Kind) (value parameter : Value) : Except String State := do
  let next ← Percentile.fraction kind parameter
  if let some previous := state.fraction then
    let difference := previous - next
    unless difference ≥ -0.001 && difference ≤ 0.001 do
      throw ("the fraction argument to " ++ kind.name ++ "() is not the same for all input rows")
  let state := { state with fraction := some (state.fraction.getD next) }
  if let .null := value then return state
  let numeric ← match value with
    | .integer number => pure (Float.ofInt number)
    | .real number => pure number
    | _ => throw ("input to " ++ kind.name ++ "() is not numeric")
  if (numeric.toBits.toNat / 4503599627370496) % 2048 == 2047 then
    throw ("Inf input to " ++ kind.name ++ "()")
  return { state with values := state.values.push numeric }

def State.finish (state : State) (kind : Kind) : Value := Id.run do
  if state.values.isEmpty then return .null
  let values := (state.values.toList.mergeSort (fun a b => a ≤ b)).toArray
  let index := state.fraction.getD 0.5 * Float.ofNat (values.size-1)
  let first := (Numeric.realToInteger index).toNat
  let left := values[first]!
  if kind == .discrete then return Math.result left
  let second := if index == Float.ofNat first || first == values.size-1 then first else first+1
  let right := values[second]!
  return Math.result (Float.fma (right-left) (index-Float.ofNat first) left)

def run (kind : Kind) (inputs : List (Value × Value)) : Except String Value := do
  let state ← inputs.foldlM (fun state pair => state.step kind pair.1 pair.2) ({} : State)
  return state.finish kind


theorem fraction_median (value : Value) : fraction .median value = .ok 0.5 := by
  rfl

theorem finish_empty (kind : Kind) (parameter : Option Float) :
    ({ fraction := parameter, values := #[] } : State).finish kind = .null := by
  rfl

theorem step_invalid_fraction (state : State) (kind : Kind) (value parameter : Value)
    (message : String) (invalid : fraction kind parameter = .error message) :
    state.step kind value parameter = .error message := by
  simp [State.step, invalid, bind, Except.bind]

theorem run_empty (kind : Kind) : run kind [] = .ok .null := by
  rfl

end SQLeanite.SQLite.Percentile
