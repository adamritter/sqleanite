import SQLeanite.CoreInsertIgnore

/-! Schema NOT NULL policies for the default statement conflict action.
Explicit OR actions use their existing paths and override these declarations.
The Core currently admits no DEFAULT values, so NOT NULL REPLACE means ABORT. -/
namespace SQLeanite.CoreNullConflict

def active (schema : Core.Schema) : Bool :=
  schema.columns.any (fun column => column.notNullConflict != .abort)

/-- Check in declared column order. An early IGNORE must skip the row before a
later NOT NULL ABORT is reached. The physical rowid is checked separately. -/
def columns (schema : Core.Schema) (values : List Core.Value) : Except String Bool := do
  for ((column, value), position) in (schema.columns.zip values).zipIdx do
    if position != schema.primaryKey && column.notNull && value == .null then
      match column.notNullConflict with
      | .ignore => return false
      | .abort | .replace => throw s!"NOT NULL constraint failed: {schema.name}.{column.name}"
  return true

def shouldWrite (schema : Core.Schema) (values : List Core.Value) (updating : Bool) : Except String Bool := do
  unless values.length == schema.columns.length do throw "row width mismatch"
  match values[schema.primaryKey]? with
  | some (.integer _) => pure ()
  | some .null => if updating then throw "datatype mismatch" else pure ()
  | _ => throw "datatype mismatch"
  columns schema values

def insert (state : Core.State) (table : String) (schema : Core.Schema)
    (values : List Core.Value) : Except String (Core.State × Core.Result) := do
  if ← shouldWrite schema values false then Core.execute state (.insert table values)
  else return (state, {})

theorem insert_skips (state : Core.State) (table : String) (schema : Core.Schema)
    (values : List Core.Value) (skip : shouldWrite schema values false = .ok false) :
    insert state table schema values = .ok (state, {}) := by
  simp [insert, skip, bind, Except.bind, pure, Except.pure]

def update (state : Core.State) (table : String) (schema : Core.Schema) (old : Core.Integer)
    (values : List Core.Value) : Except String (Core.State × Core.Result) := do
  unless ← shouldWrite schema values true do return (state, {})
  let _ ← Core.Row.create schema values
  let (removed, _) ← Core.execute state (.deleteWhere table (some (.equal schema.primaryKey (.integer old))))
  Core.execute removed (.insert table values)

theorem update_skips (state : Core.State) (table : String) (schema : Core.Schema)
    (old : Core.Integer) (values : List Core.Value)
    (skip : shouldWrite schema values true = .ok false) :
    update state table schema old values = .ok (state, {}) := by
  simp [update, skip, bind, Except.bind, pure, Except.pure]

end SQLeanite.CoreNullConflict
