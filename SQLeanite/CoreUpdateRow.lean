import SQLeanite.CoreDefaultConflict

/-! A SQL UPDATE is not an INSERT of all columns. Preserve its actual SET
positions while installing the checked row through the Core table operations,
including rekeying and REPLACE victims. Retained catalog programs are unchanged. -/
namespace SQLeanite.CoreUpdateRow

def keeps (stored : Core.Table) (old : Core.Integer) (row other : Core.Row) : Bool :=
  other.rowid != old && other.rowid != row.rowid &&
    !CoreDefaultConflict.declaredConflict stored.schema row other &&
    !(stored.indexes.any fun index => index.rowConflict row other)

def install (stored : Core.Table) (old : Core.Integer) (row : Core.Row)
    (valid : row.WellFormed stored.schema) : Except String Core.Table :=
  match retained : stored.retainRows (keeps stored old row) with
  | .error message => .error message
  | .ok remaining =>
      have rowValid : row.WellFormed remaining.schema := by
        rw [Core.Table.retainRows_schema retained]
        exact valid
      .ok (remaining.upsert row rowValid)

theorem install_rows {stored next : Core.Table} {old : Core.Integer} {row : Core.Row}
    {valid : row.WellFormed stored.schema}
    (installed : install stored old row valid = .ok next) :
    next.rows = Core.orderedUpsert row (stored.rows.filter (keeps stored old row)) := by
  unfold install at installed
  split at installed
  · contradiction
  · next remaining retained =>
      cases installed
      rw [Core.Table.upsert_rows]
      rw [Core.Table.retainRows_exact retained]

def keyError (schema : Core.Schema) (position : Nat) : String :=
  let name := if schema.hasHiddenRowid && position == schema.primaryKey then "rowid"
    else ((schema.columns[position]?).map (·.name)).getD "rowid"
  s!"UNIQUE constraint failed: {schema.name}.{name}"

def overridePolicy : ConflictAction → Option Core.NotNullConflict
  | .default => none
  | .ignore => some .ignore
  | .replace => some .replace
  | _ => some .abort

def publish (state : Core.State) (table : Core.Table) : Except String (Core.State × Core.Result) := do
  let database ← state.database.updateTable table
  return ({ state with database }, { changes := 1 })

theorem publish_lastInsertRowid {state next : Core.State} {table : Core.Table} {result : Core.Result}
    (published : publish state table = .ok (next,result)) : next.lastInsertRowid = state.lastInsertRowid := by
  unfold publish at published
  cases updated : state.database.updateTable table with
  | error message => simp [updated, bind, Except.bind] at published
  | ok database =>
      simp [updated, bind, Except.bind, pure, Except.pure] at published
      rw [← published.1]

def apply (state : Core.State) (stored : Core.Table) (old : Core.Integer)
    (values : List Core.Value) (assigned : List Nat) (policy : ConflictAction) :
    Except String (Core.State × Core.Result) := do
  if (stored.findRowid? old).isNone then return (state, {})
  let override := overridePolicy policy
  let some values ← CoreNullConflict.prepare stored.schema values true override | return (state, {})
  let row ← Core.Row.create stored.schema values
  if let some message ← stored.checkFailure row (some assigned) then
    if policy == .ignore then return (state, {}) else throw message
  let others := stored.rows.filter fun other => other.rowid != old
  let declared := CoreDefaultConflict.primaryPolicy stored.schema
  let rowidPolicy := override.getD (if stored.schema.hasHiddenRowid then .abort else declared)
  if others.any (fun other => other.rowid == row.rowid) then
    match rowidPolicy with
    | .ignore => return (state, {})
    | .abort => throw (keyError stored.schema stored.schema.primaryKey)
    | .replace => pure ()
  if stored.indexes.any (fun index => others.any (index.rowConflict row)) then
    match override.getD .abort with
    | .ignore => return (state, {})
    | .abort => throw (Core.uniqueRowsError stored.schema stored.indexes (row :: others))
    | .replace => pure ()
  if others.any (CoreDefaultConflict.declaredConflict stored.schema row) then
    match override.getD declared with
    | .ignore => return (state, {})
    | .abort => throw (keyError stored.schema stored.schema.declaredPrimaryKey)
    | .replace => pure ()
  let installed ← match created : Core.Row.create stored.schema values with
    | .error message => .error message
    | .ok row => install stored old row (Core.Row.create_wellFormed created)
  publish state installed

end SQLeanite.CoreUpdateRow
