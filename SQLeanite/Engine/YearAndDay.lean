import SQLeanite.Engine.MiniBindings

namespace SQLeanite

def yearAndDay (days year : Nat) : Nat × Nat :=
  if days < daysInYear year then (year, days)
  else yearAndDay (days - daysInYear year) (year + 1)
termination_by days
decreasing_by have := daysInYear_positive year; omega

theorem yearAndDay_returns_valid_day (days year : Nat) :
    let result := yearAndDay days year
    result.2 < daysInYear result.1 := by
  rw [yearAndDay]
  split
  · assumption
  · exact yearAndDay_returns_valid_day (days - daysInYear year) (year + 1)
termination_by days
decreasing_by have := daysInYear_positive year; omega

def daysInMonth (year month : Nat) : Nat :=
  if month == 2 then if isLeapYear year then 29 else 28
  else if month == 4 || month == 6 || month == 9 || month == 11 then 30
  else 31

theorem daysInMonth_positive (year month : Nat) : 0 < daysInMonth year month := by
  simp only [daysInMonth]
  split <;> split <;> omega

def monthAndDay (year remaining month : Nat) : Nat × Nat :=
  if remaining < daysInMonth year month then (month, remaining + 1)
  else monthAndDay year (remaining - daysInMonth year month) (month + 1)
termination_by remaining
decreasing_by have := daysInMonth_positive year month; omega

theorem monthAndDay_returns_valid_day (year remaining month : Nat) :
    let result := monthAndDay year remaining month
    1 ≤ result.2 ∧ result.2 ≤ daysInMonth year result.1 := by
  rw [monthAndDay]
  split
  · simp only [Prod.fst, Prod.snd]
    constructor <;> omega
  · exact monthAndDay_returns_valid_day year (remaining - daysInMonth year month) (month + 1)
termination_by remaining
decreasing_by have := daysInMonth_positive year month; omega

def pad2 (value : Nat) : String :=
  if value < 10 then "0" ++ toString value else toString value

/-- Pure UTC conversion keeps time-dependent SQL deterministic and testable. -/
def dateTimeStrings (epoch : Int) : String × String × String :=
  let nonnegative := max 0 epoch |>.toNat
  let days := nonnegative / 86400
  let seconds := nonnegative % 86400
  let (year, dayOfYear) := yearAndDay days 1970
  let (month, day) := monthAndDay year dayOfYear 1
  let hour := seconds / 3600
  let minute := (seconds % 3600) / 60
  let second := seconds % 60
  let date := toString year ++ "-" ++ pad2 month ++ "-" ++ pad2 day
  let time := pad2 hour ++ ":" ++ pad2 minute ++ ":" ++ pad2 second
  (date, time, date ++ " " ++ time)

def expressionMentionsColumn (target : String) (expression : Expr) : Bool :=
  expression.any fun
    | .column _ name => nameEq name target
    | _ => false

def miniHasAggregate (expression : Expr) : Bool :=
  expression.anyOutsideSubqueries fun
    | .call name args _ =>
        let name := aggregateFunctionName name
        ["count", "sum", "total", "avg", "group_concat", "string_agg",
          "legacy_count", "md5sum"].contains name ||
          ((nameEq name "min" || nameEq name "max") && args.size == 1)
    | _ => false

end SQLeanite
