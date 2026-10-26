import SQLeanite.SQLite.DateTime

/-! Calendar-aware timediff, ported from SQLite 3.53.4 src/date.c.
Month adjustment is a total bounded walk. Exhausting its explicit 24-month
budget rejects the value; it never invents a duration from an unfinished walk.
The returned shift is evaluated independently by the date/time modifier path.
-/
namespace SQLeanite.SQLite.DateDifference
open DateTime

structure Adjustment where
  state : State
  years : Int
  months : Int

def step (forward : Bool) (adjustment : Adjustment) : Option Adjustment := do
  let date := adjustment.state.civil.getD {}
  let date := shiftMonths date (if forward then -1 else 1)
  let state ← compute { adjustment.state with civil := some date, jd := none }
  let months := adjustment.months - 1
  return {
    state
    years := adjustment.years - (if months < 0 then 1 else 0)
    months := if months < 0 then 11 else months }

def crossed (forward : Bool) (target : Int) (state : State) : Bool :=
  if forward then target < state.jd.getD 0 else target > state.jd.getD 0

def align (forward : Bool) (target : Int) : Nat → Adjustment → Option Adjustment
  | 0, adjustment => if crossed forward target adjustment.state then none else some adjustment
  | fuel+1, adjustment =>
      if crossed forward target adjustment.state then
        (step forward adjustment).bind (align forward target fuel)
      else some adjustment

theorem align_stopped (forward : Bool) (target : Int) (fuel : Nat) (adjustment : Adjustment)
    (stopped : crossed forward target adjustment.state = false) :
    align forward target fuel adjustment = some adjustment := by
  cases fuel <;> simp only [align, stopped, Bool.false_eq_true, if_false]

theorem align_exhausted (forward : Bool) (target : Int) (adjustment : Adjustment)
    (unfinished : crossed forward target adjustment.state = true) :
    align forward target 0 adjustment = none := by simp [align, unfinished]

def difference (left right : Value) : Option String := do
  let a := fields (← arguments [left])
  let b := fields (← arguments [right])
  let da := a.civil.getD {}
  let db := b.civil.getD {}
  let forward := a.jd.getD 0 ≥ b.jd.getD 0
  let years := if forward then da.year - db.year else db.year - da.year
  let b ← if years != 0 then compute { b with civil := some { db with year := da.year }, jd := none }
    else some b
  let months := if forward then da.month - db.month else db.month - da.month
  let years := years - if months < 0 then 1 else 0
  let months := months + if months < 0 then 12 else 0
  let b ← if months != 0 then compute { b with civil := some { b.civil.getD {} with month := da.month }, jd := none }
    else some b
  let adjusted ← align forward (a.jd.getD 0) 24 { state := b, years, months }
  let delta := if forward then a.jd.getD 0 - adjusted.state.jd.getD 0
    else adjusted.state.jd.getD 0 - a.jd.getD 0
  let remainder := fields { jd := some (delta + 148699540800000) }
  return (if forward then "+" else "-") ++ pad 4 adjusted.years ++ "-" ++ pad 2 adjusted.months ++ "-" ++
    pad 2 ((remainder.civil.getD {}).day - 1) ++ " " ++ clockText (remainder.clock.getD {}) true

def evaluate (left right : Value) : Except String Value :=
  if [left, right].any (fun value => ["now", "subsec", "subsecond"].contains (stringValue value).toLower) then
    .error "unsupported verified SQL: date/time host clock or timezone service"
  else .ok ((difference left right).map Value.text |>.getD .null)

theorem difference_null_left (right : Value) : difference .null right = none := by
  simp [difference, arguments_null, bind, Option.bind]

end SQLeanite.SQLite.DateDifference
