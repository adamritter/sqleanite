import SQLeanite.SQLite.Scalar

/-! Constant LIMIT/OFFSET values use OP_MustBeInt numeric affinity. Admission
checks both expressions before evaluation; a zero count skips offset execution.
Original expressions stay in Select for independent concrete-token replay. -/
namespace SQLeanite.SQLite.Limit

def integer (value : Value) : Except String Int :=
  match Numeric.applyAffinity value with
  | .integer value =>
      if Numeric.fits value then .ok value else .error "datatype mismatch"
  | _ => .error "datatype mismatch"

def evaluate (expression : Expr) : Except String Int := do
  integer (← Scalar.eval expression)

def admitted (clause : LimitClause) : Bool :=
  Scalar.admitted clause.count && clause.offset.all Scalar.admitted

def resolve (clause : LimitClause) : Except String (Option Nat × Nat) := do
  unless admitted clause do throw "unsupported constant LIMIT/OFFSET expression"
  let count ← evaluate clause.count
  let skip ← if count == 0 then pure 0 else
    match clause.offset with
    | none => pure 0
    | some expression => evaluate expression
  return (if count < 0 then none else some count.toNat,
    if count == 0 then 0 else (max 0 skip).toNat)

/-- CTAS performs this check after determining that CREATE is needed.
Ordinary SELECT admission already checks resolve during token replay. -/
def validate : Option LimitClause → Except String Unit
  | none => .ok ()
  | some clause => (resolve clause).map (fun _ => ())

theorem integer_of_fits (value : Int) (fits : Numeric.fits value = true) :
    integer (.integer value) = .ok value := by
  simp [integer, Numeric.applyAffinity, fits]

theorem resolve_zero (clause : LimitClause)
    (accepted : admitted clause = true) (zero : evaluate clause.count = .ok 0) :
    resolve clause = .ok (some 0, 0) := by
  simp [resolve, accepted, zero, bind, Except.bind, pure, Except.pure]

end SQLeanite.SQLite.Limit
