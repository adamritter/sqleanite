import SQLeanite.CoreEngine
import SQLeanite.CoreExpr
import SQLeanite.CoreNames

/-! AUTOINCREMENT tracks a statement-local maximum and publishes sqlite_sequence
only after the successful statement. The sequence itself remains an ordinary
SQLite table, visible to SQL and included in transaction snapshots and files. -/
namespace SQLeanite.CoreAutoIncrement

private def zero : Core.Integer := ⟨0, by decide, by decide⟩

def sequenceName : String := "sqlite_sequence"

def sequenceSchema : Core.Schema := {
  name := sequenceName
  columns := [{ name := "name" }, { name := "seq" }, Core.hiddenRowidColumn]
  primaryKey := 2
  declaredPrimaryKey := 3 }

def ensure (state : Core.State) : Except String Core.State := do
  if (CoreNames.table? state.database sequenceName).isSome then return state
  let (next, _) ← Core.execute state (.createTable sequenceSchema)
  let some table := next.database.findTable? sequenceName | throw "created sqlite_sequence is missing"
  let retained ← table.withCatalogSQL "CREATE TABLE sqlite_sequence(name,seq)"
  let database ← next.database.updateTable retained
  return { next with database }

def sequenceTable (state : Core.State) : Except String Core.Table := do
  let some stored := CoreNames.table? state.database sequenceName
    | throw "database disk image is malformed: missing sqlite_sequence"
  unless stored.schema.visibleColumns.length == 2 do
    throw "database disk image is malformed: invalid sqlite_sequence"
  return stored

structure Context where
  tableName : String
  sequenceRowid : Option Core.Integer
  original : Option Core.Integer
  maximum : Core.Integer

def beginContext (state : Core.State) (tableName : String) : Except String Context := do
  let stored ← sequenceTable state
  let name ← SQLSurface.value (.text tableName)
  match stored.rows.find? (fun row => row.values[0]? == some name) with
  | none => return { tableName, sequenceRowid := none, original := none, maximum := zero }
  | some row =>
      let value ← CoreExpr.value (row.values[1]?.getD .null)
      let maximum ← SQLSurface.signed64 (SQLite.Numeric.integer value)
      return { tableName, sequenceRowid := some row.rowid, original := some maximum, maximum }

/-- OP_NewRowid uses the greater of the current table end and the sequence
register. A full signed rowid range is an error, never random reuse. -/
def allocate (stored : Core.Table) (context : Context) : Except String Core.Integer :=
  let next := max ((stored.lastRow?.map (fun row => row.rowid.value + 1)).getD 1)
    (context.maximum.value + 1)
  if lower : -(Int.ofNat FileFormat.IntegerWidth.eight.midpoint) ≤ next then
    if upper : next < Int.ofNat FileFormat.IntegerWidth.eight.midpoint then
      .ok ⟨next, lower, upper⟩
    else .error "database or disk is full"
  else .error "database or disk is full"

theorem allocate_greater_maximum (stored : Core.Table) (context : Context) (rowid : Core.Integer)
    (allocated : allocate stored context = .ok rowid) : context.maximum.value < rowid.value := by
  unfold allocate at allocated
  dsimp only at allocated
  split at allocated
  · split at allocated
    · have equal := Except.ok.inj allocated
      have value := congrArg (fun identifier : Core.Integer => identifier.value) equal
      have bound := Int.le_max_right
        ((stored.lastRow?.map (fun row => row.rowid.value + 1)).getD 1) (context.maximum.value + 1)
      dsimp only at value
      omega
    · contradiction
  · contradiction

def advance (context : Context) (rowid : Core.Integer) : Context :=
  if context.maximum.value < rowid.value then { context with maximum := rowid } else context

theorem advance_monotone (context : Context) (rowid : Core.Integer) :
    context.maximum.value ≤ (advance context rowid).maximum.value := by
  unfold advance
  split <;> simp_all <;> omega

/-- Resolve the rowid before NOT NULL/unique conflict actions. Even an ignored
candidate advances the statement register after a successful allocation. -/
def prepare (stored : Core.Table) (context : Context) (values : List Core.Value) :
    Except String (Context × List Core.Value) := do
  let rowid ← match values[stored.schema.primaryKey]? with
    | some .null => allocate stored context
    | some (.integer rowid) => pure rowid
    | _ => throw "datatype mismatch"
  return (advance context rowid, values.set stored.schema.primaryKey (.integer rowid))

/-- Preserve the original sqlite_sequence storage class if its integerized
value did not increase. A previously absent entry is written even after an
empty SELECT or a statement whose candidates were all ignored. -/
def finish (state : Core.State) (context : Context) : Except String Core.State := do
  if context.original.any (fun old => context.maximum.value ≤ old.value) then return state
  let stored ← sequenceTable state
  match context.sequenceRowid with
  | some rowid =>
      let (next, _) ← Core.execute state (.updateWhere stored.schema.name
        [(1, .integer context.maximum)] (some (.equal stored.schema.primaryKey (.integer rowid))))
      return { next with lastInsertRowid := state.lastInsertRowid }
  | none =>
      let name ← SQLSurface.value (.text context.tableName)
      let values := (List.replicate stored.schema.columns.length (.null : Core.Value)).set 0 name
        |>.set 1 (.integer context.maximum)
      let (next, _) ← Core.execute state (.insert stored.schema.name values)
      return { next with lastInsertRowid := state.lastInsertRowid }

theorem finish_unchanged (state : Core.State) (context : Context) (old : Core.Integer)
    (original : context.original = some old) (unchanged : context.maximum.value ≤ old.value) :
    finish state context = .ok state := by
  simp [finish, original, unchanged, pure, Except.pure]

def remove (state : Core.State) (tableName : String) : Except String Core.State := do
  let some stored := CoreNames.table? state.database sequenceName | return state
  let name ← SQLSurface.value (.text tableName)
  let (next, _) ← Core.execute state (.deleteWhere stored.schema.name (some (.equal 0 name)))
  return next

def rename (state : Core.State) (oldName newName : String) : Except String Core.State := do
  let some stored := CoreNames.table? state.database sequenceName | return state
  let old ← SQLSurface.value (.text oldName)
  let name ← SQLSurface.value (.text newName)
  let (next, _) ← Core.execute state (.updateWhere stored.schema.name [(0, name)] (some (.equal 0 old)))
  return next

end SQLeanite.CoreAutoIncrement
