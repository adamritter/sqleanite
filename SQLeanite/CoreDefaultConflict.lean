import SQLeanite.CoreNullConflict

/-! Default schema policies lower to ordinary checked Core commands. Rowid
constraints precede non-REPLACE unique indexes, and REPLACE is deferred until
all constraints that can skip or abort have been checked (SQLite insert.c). -/
namespace SQLeanite.CoreDefaultConflict

def primaryPolicy (schema : Core.Schema) : Core.NotNullConflict :=
  ((schema.columns[schema.declaredPrimaryKey]?).map (·.primaryConflict)).getD .abort

def active (schema : Core.Schema) : Bool :=
  CoreNullConflict.active schema || primaryPolicy schema != .abort

def declaredConflict (schema : Core.Schema) (left right : Core.Row) : Bool :=
  schema.hasHiddenRowid && schema.declaredPrimaryKey?.isSome &&
    Core.uniqueValueConflict (left.value schema.declaredPrimaryKey) (right.value schema.declaredPrimaryKey)

def commands (stored : Core.Table) (old : Option Core.Integer) (row : Core.Row) : List Core.Command :=
  let removed := stored.rows.filter fun other =>
    old.any (· == other.rowid) || other.rowid == row.rowid || declaredConflict stored.schema row other
  removed.map (fun other => Core.Command.deleteWhere stored.schema.name
    (some (.equal stored.schema.primaryKey (.integer other.rowid)))) ++
      [.insert stored.schema.name row.values]

theorem commands_last (stored : Core.Table) (old : Option Core.Integer) (row : Core.Row) :
    (commands stored old row).getLast? = some (.insert stored.schema.name row.values) := by
  simp [commands]

def validate (stored : Core.Table) (old : Option Core.Integer) : Except String Unit :=
  if old.isSome then .ok ()
  else CoreNullConflict.validate stored.schema (List.range stored.schema.columns.length)

def plan (stored : Core.Table) (values : List Core.Value) (old : Option Core.Integer) :
    Except String (Option (Core.Row × List Core.Command)) := do
  validate stored old
  let some values ← CoreNullConflict.prepare stored.schema values old.isSome | return none
  let row ← if old.isSome then Core.Row.create stored.schema values else stored.createRow values
  let others := stored.rows.filter fun other => !old.any (· == other.rowid)
  let rowidConflict := others.any fun other => other.rowid == row.rowid
  let policy := primaryPolicy stored.schema
  let rowidPolicy := if stored.schema.hasHiddenRowid then .abort else policy
  if rowidConflict then
    match rowidPolicy with
    | .ignore => return none
    | .abort => throw "UNIQUE constraint failed: rowid"
    | .replace => pure ()
  if stored.indexes.any (fun index => others.any (index.rowConflict row)) then
    throw "UNIQUE constraint failed: index"
  if others.any (declaredConflict stored.schema row) then
    match policy with
    | .ignore => return none
    | .abort => throw "UNIQUE constraint failed: PRIMARY KEY"
    | .replace => pure ()
  return some (row, commands stored old row)

theorem plan_skips_null (stored : Core.Table) (values : List Core.Value) (old : Option Core.Integer)
    (compiled : validate stored old = .ok ())
    (skip : CoreNullConflict.prepare stored.schema values old.isSome = .ok none) :
    plan stored values old = .ok none := by
  simp [plan, compiled, skip, bind, Except.bind, pure, Except.pure]

end SQLeanite.CoreDefaultConflict
