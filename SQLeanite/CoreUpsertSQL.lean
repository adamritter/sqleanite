import SQLeanite.CoreConnectionSQL
import SQLeanite.CoreScalarQuery

/-! UPSERT resolves its conflict targets before visiting candidates. Each
candidate sees earlier accepted rows, and DO UPDATE always uses ABORT semantics.
The excluded frame follows the affinity stage of the selected constraint; it never becomes a table or a persistent SQL name. -/
namespace SQLeanite.CoreUpsertSQL

structure Clause where
  target : Option Nat
  assignments : Option (Array (String × Expr))
  condition : Option Expr

def target (stored : Core.Table) (ctx : CoreExpr.Context) (clause : UpsertClause) :
    Except String (Option Nat) := do
  let some expressions := clause.target | return none
  for expression in expressions do ctx.validate expression
  discard <| clause.targetWhere.mapM ctx.validate
  let failure := "ON CONFLICT clause does not match any PRIMARY KEY or UNIQUE constraint"
  unless expressions.size == 1 do throw failure
  let expression := expressions[0]!
  let .column qualifier name := SQLite.ExprCollation.strip expression | throw failure
  let some index := ctx.column? qualifier name | throw s!"no such column: {name}"
  if index == stored.schema.primaryKey && (SQLite.ExprCollation.name expression).isSome then throw failure
  unless ((SQLite.ExprCollation.name expression).getD "binary").toLower == "binary" do throw failure
  unless index == stored.schema.primaryKey || index == stored.schema.declaredPrimaryKey ||
      stored.indexes.any (fun item => item.unique && item.column == index) do throw failure
  return some index

def bindExcluded (ctx : CoreExpr.Context) (values : List Core.Value) (expression : Expr) : Except String Expr :=
  CoreScalarQuery.bind ctx [{ context := { schema := ctx.schema, sourceName := "excluded" }, row := values }]
    [] (expression.height + 1) expression

def compile (state : Core.State) (stored : Core.Table) (ctx : CoreExpr.Context)
    (clause : UpsertClause) : Except String Clause := do
  let column ← target stored ctx clause
  let assignments := clause.assignments.map (·.map fun (name,value) =>
    (name, CoreConnectionSQL.counterExpression state value))
  let condition := clause.where_.map (CoreConnectionSQL.counterExpression state)
  let dummy := List.replicate stored.schema.columns.length (.null : Core.Value)
  let bind := fun expr => bindExcluded ctx dummy (CoreLastInsert.bind state expr)
  if let some assignments := assignments then
    discard <| CoreSQL.expressionAssignmentsWith true ctx
      (← assignments.toList.mapM fun (name,expr) => return (name, ← bind expr))
  discard <| condition.mapM fun expr => do ctx.validate (← bind expr)
  return { target := column, assignments, condition }

/-- Target matching uses SQL uniqueness: NULL never conflicts, while numeric
INTEGER/REAL comparisons do not depend on their record encoding. -/
def conflictingRow (stored : Core.Table) (candidate : Core.Row) (column : Nat) : Option Core.Row :=
  if column == stored.schema.primaryKey then stored.findRowid? candidate.rowid
  else stored.rows.find? fun row => Core.uniqueValueConflict (candidate.value column) (row.value column)

def conflictColumns (stored : Core.Table) : List Nat :=
  [stored.schema.primaryKey] ++
    (if stored.schema.declaredPrimaryKey?.isSome && stored.schema.hasHiddenRowid then
      [stored.schema.declaredPrimaryKey] else []) ++
    (stored.indexes.filter (·.unique)).reverse.map (·.column)

def conflict (stored : Core.Table) (candidate : Core.Row) : Option (Nat × Core.Row) :=
  (conflictColumns stored).findSome? fun column =>
    (conflictingRow stored candidate column).map fun row => (column,row)

def choose (stored : Core.Table) (candidate : Core.Row) : List Clause → Option (Clause × Core.Row)
  | [] => none
  | clause :: rest =>
      let found := match clause.target with
        | some column => conflictingRow stored candidate column
        | none => (conflict stored candidate).map Prod.snd
      match found with
      | some row => some (clause,row)
      | none => choose stored candidate rest

theorem choose_empty (stored : Core.Table) (candidate : Core.Row) :
    choose stored candidate [] = none := rfl

def uniqueError (schema : Core.Schema) (column : Nat) : String :=
  let name := if schema.hasHiddenRowid && column == schema.primaryKey then "rowid"
    else ((schema.columns[column]?).map (·.name)).getD "rowid"
  s!"UNIQUE constraint failed: {schema.name}.{name}"

/-- Evaluate the assignment list once against the old row. The checked Core
trace is only committed after all constraints and RETURNING have succeeded. -/
def update (state : Core.State) (stored : Core.Table) (ctx outputCtx : CoreExpr.Context)
    (excluded : List Core.Value) (old : Core.Row) (clause : Clause) (projection : List Expr)
    (preparation : Option CoreSQL.RowPreparation := none) :
    Except String (Core.State × Option (List Core.Value)) := do
  let some assignments := clause.assignments | return (state, none)
  let bind := fun expr => bindExcluded ctx excluded (CoreLastInsert.bind state expr)
  let bound ← CoreSQL.expressionAssignmentsWith true ctx
    (← assignments.toList.mapM fun (name,expr) => return (name, ← bind expr))
  let condition ← clause.condition.mapM bind
  unless ← ctx.matches old.values condition do return (state, none)
  let updates ← CoreSQL.evaluateAssignmentsTyped ctx old bound
  let cells := updates.foldl (fun values (index,input) => values.set index input)
    (old.values.map CoreReturning.Cell.plain)
  let some input ← (match preparation with
    | none => pure (some ({ cells, assigned := some (bound.map Prod.fst) } : CoreSQL.RowInput))
    | some prepare => prepare state stored .abort { cells, assigned := some (bound.map Prod.fst), converted := List.range stored.schema.columns.length }) | return (state, none)
  let cells := input.cells
  let assigned := input.assigned.getD (bound.map Prod.fst)
  let some cells ← CoreReturning.prepareValues stored.schema cells true (some .abort)
    | throw "unexpected skipped UPSERT update"
  let row ← Core.Row.create stored.schema (cells.map (·.value))
  let (next, _) ← if stored.hasChecks then
      CoreUpdateRow.apply state stored old.rowid row.values assigned .abort
    else do
      stored.requireChecks row
      let (removed, _) ← Core.execute state (.deleteWhere stored.schema.name
        (some (.equal stored.schema.primaryKey (.integer old.rowid))))
      let some remaining := removed.database.findTable? stored.schema.name | throw "missing UPSERT table"
      if let some (column,_) := conflict remaining row then throw (uniqueError stored.schema column)
      Core.execute removed (.insert stored.schema.name row.values)
  let output ← CoreReturning.project outputCtx (CoreReturning.withValues cells row.values)
    (projection.map (CoreLastInsert.bind state))
  let next := next.recordForeignWrite stored.schema.name row.rowid (some assigned)
  return ({ next with lastInsertRowid := state.lastInsertRowid }, some output)

theorem update_nothing (state : Core.State) (stored : Core.Table)
    (ctx outputCtx : CoreExpr.Context) (excluded : List Core.Value) (old : Core.Row)
    (clause : Clause) (projection : List Expr) (nothing : clause.assignments = none) :
    update state stored ctx outputCtx excluded old clause projection = .ok (state, none) := by
  simp [update, nothing, pure, Except.pure]

theorem choose_mem (stored : Core.Table) (candidate : Core.Row) (clauses : List Clause)
    (selected : Clause) (row : Core.Row)
    (found : choose stored candidate clauses = some (selected,row)) : selected ∈ clauses := by
  induction clauses with
  | nil => simp [choose] at found
  | cons first rest ih =>
      simp only [choose] at found
      split at found
      · cases found
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem first (ih found)

def execute (state : Core.State) (source : Statement) (alias : Option String)
    (clauses : Array UpsertClause) (preparation : Option CoreSQL.RowPreparation := none) : Except String (Core.State × List Core.Result) := do
  let (table,columns,inputSource,policy,returning) ← match source with
    | .insert table columns inputs policy returning => pure (table,columns,Sum.inl inputs,policy,returning)
    | .insertSelect table columns query policy returning => pure (table,columns,Sum.inr query,policy,returning)
    | _ => throw "unsupported UPSERT source"
  unless policy == .default || policy == .abort || policy == .ignore || policy == .replace do
    throw "unsupported UPSERT conflict policy"
  let some stored := CoreNames.table? state.database table | throw s!"no such table: {table}"
  let name := stored.schema.name
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD name }
  let outputCtx : CoreExpr.Context := { schema := stored.schema, sourceName := name }
  if let .inl inputs := inputSource then CoreInsertPrepare.check stored.schema columns inputs
  let clauses ← clauses.toList.mapM (compile state stored ctx)
  let returning := returning.map fun col => { col with expr := CoreConnectionSQL.counterExpression state col.expr }
  let projection ← CoreLastInsert.prepareReturning state outputCtx returning.toList
  let inputs ← match inputSource with
    | .inl inputs => pure inputs
    | .inr query => do
        let query := CoreConnectionSQL.select state query.compoundHeight query
        let selected ← CoreSQL.executeSelect state query
        CoreSQL.checkInsertSelectColumns stored.schema columns selected.width
        pure (← selected.result.rows.mapM CoreSQL.selectedRowExpressions).toArray
  let inputs := inputs.map (·.map fun expr =>
    let expr := CoreConnectionSQL.counterExpression state expr
    if returning.isEmpty then expr else CoreLastInsert.bind state expr)
  let override := if policy == .ignore then some Core.NotNullConflict.ignore
    else if policy == .replace then some .replace else if policy == .abort then some .abort else none
  CoreNullConflict.validate stored.schema (List.range stored.schema.columns.length) override
  let mut sequence ← if stored.schema.autoIncrement then
      some <$> CoreAutoIncrement.beginContext state name else pure none
  let mut current := state
  let mut outputs := []
  let mut changes := 0
  let mut defaults := []
  for input in inputs do
    let some stored := current.database.findTable? name | throw s!"no such table: {name}"
    -- A rowid conflict can precede OP_Affinity for the other columns.
    let rawSchema := { stored.schema with columns := stored.schema.columns.mapIdx fun index col =>
      if index == stored.schema.primaryKey then col else { name := col.name, defaultValue := col.defaultValue } }
    let rawCells ← CoreSQL.inputRowValuesTyped rawSchema columns (inputs.size > 1)
      (input.map (CoreLastInsert.bind current)) defaults
    let rawCells ← if let some context := sequence then do
        let (context, values) ← CoreAutoIncrement.prepare stored context (rawCells.map (·.value))
        sequence := some context
        pure (CoreReturning.withValues rawCells values)
      else pure rawCells
    let some inputFrame ← (match preparation with
      | none => pure (some ({ cells := rawCells } : CoreSQL.RowInput))
      | some prepare => prepare current stored policy { cells := rawCells, converted := [stored.schema.primaryKey] })
      | continue
    let rawCells := inputFrame.cells
    let some rawCells ← CoreReturning.prepareValues stored.schema rawCells false override | continue
    let cells := rawCells.zipIdx.map fun (cell,index) =>
      if inputFrame.converted.contains index then cell else
        cell.writeAffinity ((stored.schema.columns[index]?).map (·.affinity) |>.getD .blob)
    let candidate ← stored.prepareRow (cells.map (·.value))
    if let some message ← stored.checkFailure candidate then
      if policy == .ignore then continue else throw message
    let (next, output) ← match choose stored candidate clauses with
      | some (clause, old) => do
          let firstRowid := (clauses.head?.bind (·.target)).getD stored.schema.primaryKey == stored.schema.primaryKey
          let earlyRowid := firstRowid && candidate.rowid == old.rowid &&
            clause.target.getD stored.schema.primaryKey == stored.schema.primaryKey
          let excluded ← if earlyRowid then
              rawCells.zipIdx.mapM fun (cell,index) => do
                if index == stored.schema.primaryKey then return .integer candidate.rowid
                -- OP_RealAffinity changes an integer register, not numeric text.
                if ((stored.schema.columns[index]?).map (·.affinity)) == some .real then
                  if let .integer number := cell.value then
                    return ← SQLSurface.value (.real number.value.toFloat)
                return cell.value
            else pure candidate.values
          update current stored ctx outputCtx excluded old clause projection preparation
      | none => CoreSQL.insertReturningValues current name policy outputCtx projection cells
    current := next
    if let some row := output then
      changes := changes + 1
      if !returning.isEmpty then outputs := row :: outputs
      defaults := CoreSQL.insertDefaultRegisters stored.schema columns input cells
  if let some context := sequence then current ← CoreAutoIncrement.finish current context
  return ({ current with lastChanges := changes, totalChanges := state.totalChanges + changes },
    [{ rows := outputs.reverse, changes }])

end SQLeanite.CoreUpsertSQL
