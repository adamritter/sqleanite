import SQLeanite.SQLite.Text

/-! SQLite's ordinary GROUP_CONCAT/STRING_AGG accumulator. Each accepted row
supplies its own separator, which precedes that row after the first non-NULL
value. TEXT keeps all source bytes; the terminator counts against StrAccum's
allocation limit. Argument evaluation and DISTINCT happen in CoreAggregate. -/
namespace SQLeanite.SQLite.AggregateConcat

structure State where
  bytes : Array UInt8 := #[]
  seen : Bool := false

def State.step (state : State) (value separator : Value) : Except String State := do
  if Text.isNull value then return state
  let source := Text.bytes value
  let separator := if state.seen then Text.bytes separator else #[]
  Limits.check (state.bytes.size + separator.size + source.size) 1
  return { bytes := state.bytes ++ separator ++ source, seen := true }

def State.finish (state : State) : Value :=
  if state.seen then Text.fromBytes state.bytes else .null

def run (inputs : List (Value × Value)) : Except String Value := do
  let state ← inputs.foldlM (fun state pair => state.step pair.1 pair.2) ({} : State)
  return state.finish

theorem State.step_null (state : State) (separator : Value) :
    state.step .null separator = .ok state := rfl

theorem State.first_separator_ignored (value left right : Value) :
    ({} : State).step value left = ({} : State).step value right := by
  simp [State.step]

theorem run_nil : run [] = .ok .null := rfl

end SQLeanite.SQLite.AggregateConcat
