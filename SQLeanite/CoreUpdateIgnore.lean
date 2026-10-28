import SQLeanite.CoreEngine.ChooseExtremeEqLeftOrRight
import SQLeanite.CoreInsertIgnore

/-! A candidate UPDATE uses a private deletion of its old row for constraint
checking. Ignoring the candidate returns the original state, so no deletion can
escape. Successful replacement is still performed by the checked Core commands. -/
namespace SQLeanite.CoreUpdateIgnore

def finish (before removed : Core.State) (table : String) (remaining : Core.Table)
    (values : List Core.Value) : Except String (Core.State × Core.Result) := do
  if ← CoreInsertIgnore.shouldInsert remaining values then Core.execute removed (.insert table values)
  else return (before, {})

theorem finish_skips (before removed : Core.State) (table : String) (remaining : Core.Table)
    (values : List Core.Value) (skip : CoreInsertIgnore.shouldInsert remaining values = .ok false) :
    finish before removed table remaining values = .ok (before, {}) := by
  simp [finish, skip, bind, Except.bind, pure, Except.pure]

theorem finish_inserts (before removed : Core.State) (table : String) (remaining : Core.Table)
    (values : List Core.Value) (accept : CoreInsertIgnore.shouldInsert remaining values = .ok true) :
    finish before removed table remaining values = Core.execute removed (.insert table values) := by
  simp [finish, accept, bind, Except.bind]

/-- Unlike INSERT, UPDATE rowid=NULL is a datatype error. IGNORE may suppress
constraint conflicts, but cannot turn this NULL into automatic allocation. -/
def row (state : Core.State) (table : String) (schema : Core.Schema) (old : Core.Integer)
    (values : List Core.Value) : Except String (Core.State × Core.Result) := do
  match values[schema.primaryKey]? with
  | some (.integer _) => pure ()
  | _ => throw "datatype mismatch"
  let (removed, deletion) ← Core.execute state (.deleteWhere table (some (.equal schema.primaryKey (.integer old))))
  if deletion.changes == 0 then return (state, {})
  let remaining ← match removed.database.findTable? table with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  finish state removed table remaining values

end SQLeanite.CoreUpdateIgnore
