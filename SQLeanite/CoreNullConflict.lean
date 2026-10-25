import SQLeanite.CoreInsertIgnore

/-! Ordered NOT NULL checks. REPLACE first substitutes a declared default;
a second pass rejects remaining NULLs after every earlier IGNORE opportunity. -/
namespace SQLeanite.CoreNullConflict

def active (schema : Core.Schema) : Bool :=
  schema.columns.any (fun column => column.notNullConflict != .abort)

/-- Replacement code is compiled even if no NULL candidate reaches it.
UPDATE supplies only assigned positions; INSERT supplies every position. -/
def validate (schema : Core.Schema) (positions : List Nat)
    (override : Option Core.NotNullConflict := none) : Except String Unit := do
  for position in positions do
    if position != schema.primaryKey then
      if let some column := schema.columns[position]? then
        if column.notNull && override.getD column.notNullConflict == .replace then
          if let some spec := column.defaultValue then ColumnDefault.validateUse spec

def prepare (schema : Core.Schema) (values : List Core.Value) (updating : Bool)
    (override : Option Core.NotNullConflict := none) : Except String (Option (List Core.Value)) := do
  unless values.length == schema.columns.length do throw "row width mismatch"
  match values[schema.primaryKey]? with
  | some (.integer _) => pure ()
  | some .null => if updating then throw "datatype mismatch" else pure ()
  | _ => throw "datatype mismatch"
  let mut result := values
  for ((column, value), position) in (schema.columns.zip values).zipIdx do
    if position != schema.primaryKey && column.notNull && value == .null then
      match override.getD column.notNullConflict with
      | .ignore => return none
      | .abort => throw s!"NOT NULL constraint failed: {schema.name}.{column.name}"
      | .replace =>
          let some spec := column.defaultValue | throw s!"NOT NULL constraint failed: {schema.name}.{column.name}"
          let replacement ← ColumnDefault.evaluate spec
          result := result.set position (SQLite.PhysicalAffinity.write column.affinity replacement)
  for ((column, value), position) in (schema.columns.zip result).zipIdx do
    if position != schema.primaryKey && column.notNull && value == .null then
      throw s!"NOT NULL constraint failed: {schema.name}.{column.name}"
  return some result

def insert (state : Core.State) (table : String) (schema : Core.Schema)
    (values : List Core.Value) : Except String (Core.State × Core.Result) := do
  let some values ← prepare schema values false | return (state, {})
  Core.execute state (.insert table values)

theorem insert_skips (state : Core.State) (table : String) (schema : Core.Schema)
    (values : List Core.Value) (skip : prepare schema values false = .ok none) :
    insert state table schema values = .ok (state, {}) := by
  simp [insert, skip, bind, Except.bind, pure, Except.pure]

def update (state : Core.State) (table : String) (schema : Core.Schema) (old : Core.Integer)
    (values : List Core.Value) : Except String (Core.State × Core.Result) := do
  let some values ← prepare schema values true | return (state, {})
  let _ ← Core.Row.create schema values
  let (removed, _) ← Core.execute state (.deleteWhere table (some (.equal schema.primaryKey (.integer old))))
  Core.execute removed (.insert table values)

theorem update_skips (state : Core.State) (table : String) (schema : Core.Schema)
    (old : Core.Integer) (values : List Core.Value)
    (skip : prepare schema values true = .ok none) :
    update state table schema old values = .ok (state, {}) := by
  simp [update, skip, bind, Except.bind, pure, Except.pure]

end SQLeanite.CoreNullConflict
