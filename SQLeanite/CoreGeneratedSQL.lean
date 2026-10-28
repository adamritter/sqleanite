import SQLeanite.CoreSQL

/-! Source-level generated programs prepare physical registers before Core's
ordinary constraint and row operations. No generated expression changes the
meaning of a source-free Core command. -/
namespace SQLeanite.CoreGeneratedSQL

def specs (table : Core.Table) : Except String (List CoreGeneratedSyntax.Spec) :=
  match table.catalogSource with
  | none => .ok []
  | some source => source.compiledGeneratedColumns

/-- Host-dependent date/time operations are forbidden in schema programs.
The callback is invoked by the ordinary lazy scalar evaluator only for an
actually evaluated call, with its actual typed arguments. -/
def builtin (name : String) (arguments : Array SQLite.ScalarValue) : Except String SQLite.ScalarValue :=
  match SQLite.DateTime.evaluate? name (arguments.toList.map (·.value)) with
  | some result => (SQLite.Scalar.plainScalar <$> result).mapError fun message =>
      if message == "unsupported verified SQL: date/time host clock or timezone service" then
        s!"non-deterministic use of {name}() in a generated column" else message
  | none => SQLite.Scalar.builtinTyped name arguments

def calculate (table : Core.Table) (program : List CoreGeneratedSyntax.Spec)
    (input : CoreSQL.RowInput) : Except String CoreSQL.RowInput := do
  let ctx : CoreExpr.Context := { schema := table.schema, sourceName := table.schema.name }
  let mut cells := input.cells
  let mut converted := input.converted
  for spec in program do
    let registers := cells.zipIdx.map fun (cell,position) =>
      if converted.contains position then cell else
        cell.writeAffinity ((table.schema.columns[position]?).map (·.affinity) |>.getD .blob)
    let value ← CoreReturning.Cell.fromScalar (← SQLite.Scalar.evalTypedWithBuiltin
      (CoreReturning.lookup ctx registers) ctx.affinity builtin (ctx.bindNames spec.expression))
    let affinity := (table.schema.columns[spec.position]?).map (·.affinity) |>.getD .blob
    cells := cells.set spec.position (value.writeAffinity affinity)
    if !converted.contains spec.position then converted := spec.position :: converted
  return { input with cells, converted }

def prepare (_state : Core.State) (table : Core.Table) (policy : ConflictAction)
    (input : CoreSQL.RowInput) : Except String (Option CoreSQL.RowInput) := do
  let definitions ← specs table
  let program ← CoreGeneratedSyntax.order definitions
  unless input.cells.length == table.schema.columns.length do throw "row width mismatch"
  let mut input := input
  match (input.cells[table.schema.primaryKey]?).map CoreReturning.Cell.value with
  | some (.integer _) => pure ()
  | some .null =>
      if input.assigned.isSome then throw "datatype mismatch"
      let some rowid := table.nextGeneratedRowid? | throw "database or disk is full"
      input := { input with cells := input.cells.set table.schema.primaryKey (.plain (.integer rowid)) }
  | _ => throw "datatype mismatch"
  let ordinary := (List.range table.schema.columns.length).filter fun position =>
    !definitions.any (fun spec => spec.position == position)
  input := { input with
    cells := input.cells.zipIdx.map fun (cell,position) =>
      if input.converted.contains position || !ordinary.contains position then cell else
        cell.writeAffinity ((table.schema.columns[position]?).map (·.affinity) |>.getD .blob)
    converted := ordinary ++ input.converted }
  if let some source := table.catalogSource then
    if let some types ← source.compiledStrictColumns then
      let pairs := (types.zip (input.cells.map (·.value))).zipIdx.filterMap fun (pair,position) =>
        if ordinary.contains position then some pair else none
      CoreStrictSyntax.require table.schema.name (pairs.map Prod.fst) (pairs.map Prod.snd)
  input ← calculate table program input
  let override : Option Core.NotNullConflict :=
    if policy == .ignore then some .ignore else if policy == .replace then some .replace
    else if policy == .abort then some .abort else none
  let mut replaced := false
  -- insert.c's first pass visits changed ordinary columns. Generated NOT
  -- NULL fields are deferred until replacement defaults have been applied.
  for (column,position) in table.schema.columns.zipIdx do
    if position == table.schema.primaryKey || definitions.any (fun spec => spec.position == position) then continue
    if input.assigned.any (fun positions => !positions.contains position) then continue
    if column.notNull && (input.cells[position]?).any (fun cell => cell.value == .null) then
      match override.getD column.notNullConflict with
      | .ignore => return none
      | .abort => throw s!"NOT NULL constraint failed: {table.schema.name}.{column.name}"
      | .replace =>
          let some default := column.defaultValue | throw s!"NOT NULL constraint failed: {table.schema.name}.{column.name}"
          input := { input with
            cells := input.cells.set position (← CoreReturning.defaultValue column default)
            converted := position :: input.converted }
          replaced := true
  if replaced then input ← calculate table program input
  -- On the second pass an ordinary REPLACE becomes ABORT. A generated
  -- IGNORE can still precede a later remaining ordinary NULL in schema order.
  for (column,position) in table.schema.columns.zipIdx do
    if position == table.schema.primaryKey then continue
    let generated := definitions.any (fun spec => spec.position == position)
    if !generated && (override.getD column.notNullConflict != .replace ||
        input.assigned.any (fun positions => !positions.contains position)) then continue
    if column.notNull && (input.cells[position]?).any (fun cell => cell.value == .null) then
      if generated && override.getD column.notNullConflict == .ignore then return none
      throw s!"NOT NULL constraint failed: {table.schema.name}.{column.name}"
  return some { input with assigned := input.assigned.map (CoreGeneratedSyntax.affected definitions) }

def names (table : Core.Table) (columns : Option (Array String))
    (definitions : List CoreGeneratedSyntax.Spec) : Except String (Option (Array String)) := do
  if let some columns := columns then
    for name in columns do
      if let some spec := definitions.find? (fun spec => spec.name.toLower == name.toLower) then
        throw s!"cannot INSERT into generated column \"{spec.name}\""
    return some columns
  return some ((table.schema.catalogColumns.zipIdx.filterMap fun (column,position) =>
    if definitions.any (fun spec => spec.position == position) then none else some column.name).toArray)

def assignments (definitions : List CoreGeneratedSyntax.Spec) (values : Array (String × Expr)) : Except String Unit := do
  for (name,_) in values do
    if let some spec := definitions.find? (fun spec => spec.name.toLower == name.toLower) then
      throw s!"cannot UPDATE generated column \"{spec.name}\""

/-- Binding and dependency-cycle errors precede execution even for an empty
INSERT SELECT or UPDATE. Omitted INSERT lists contain ordinary columns only. -/
def statement (state : Core.State) : Statement → Except String Statement
  | .insert name columns rows conflict returning => do
      let some table := CoreNames.table? state.database name | return .insert name columns rows conflict returning
      let definitions ← specs table
      if definitions.isEmpty then return .insert name columns rows conflict returning
      let targets ← names table columns definitions
      discard <| CoreGeneratedSyntax.order definitions
      if columns.isNone then
        for row in rows do
          if !row.isEmpty && row.size != (targets.getD #[]).size then
            throw s!"table {table.schema.name} has {(targets.getD #[]).size} columns but {row.size} values were supplied"
      let targets := if columns.isNone && rows.size == 1 && rows[0]!.isEmpty then none else targets
      return .insert name targets rows conflict returning
  | .insertSelect name columns query conflict returning => do
      let some table := CoreNames.table? state.database name | return .insertSelect name columns query conflict returning
      let definitions ← specs table
      if definitions.isEmpty then return .insertSelect name columns query conflict returning
      let targets ← names table columns definitions
      discard <| CoreGeneratedSyntax.order definitions
      return .insertSelect name targets query conflict returning
  | .update name alias values condition conflict returning => do
      let some table := CoreNames.table? state.database name | return .update name alias values condition conflict returning
      let definitions ← specs table
      assignments definitions values
      discard <| CoreGeneratedSyntax.order definitions
      return .update name alias values condition conflict returning
  | .upsert base alias clauses => do
      let base ← statement state base
      let target := match base with | .insert name .. | .insertSelect name .. => some name | _ => none
      if let some name := target then
        if let some table := CoreNames.table? state.database name then
          let definitions ← specs table
          for clause in clauses do
            if let some values := clause.assignments then assignments definitions values
      return .upsert base alias clauses
  | other => .ok other

def preparation (state : Core.State) (name : String) : Except String (Option CoreSQL.RowPreparation) := do
  let some table := CoreNames.table? state.database name | return none
  if (← specs table).isEmpty then return none
  return some prepare

theorem calculate_empty (table : Core.Table) (input : CoreSQL.RowInput) :
    calculate table [] input = .ok input := by
  cases input
  rfl

end SQLeanite.CoreGeneratedSQL
