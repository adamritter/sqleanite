import SQLeanite.CoreDefaultConflict
import SQLeanite.CoreIndexPrepare
import SQLeanite.CoreNames
import SQLeanite.CoreReturning

namespace SQLeanite
namespace CoreSQL

def resolveTableName (state : Core.State) (name : String) : String :=
  CoreNames.tableName state.database name

def literal (expression : Expr) : Except String Core.Value :=
  SQLSurface.literal expression

def columnLiteral (column : Core.Column) (expression : Expr) : Except String Core.Value :=
  SQLite.PhysicalAffinity.write column.affinity <$> literal expression

/-- Canonical admitted rows are fixed points of their column's comparison
affinity. A comparison requesting a different coercion of the stored operand
needs a general VDBE expression operand, which is not yet in this Core subset.
Reject that shape rather than using an unsound index equality. -/
def comparisonLiteral (schema : Core.Schema) (index : Nat) (expression : Expr) :
    Except String Core.Value := do
  let value ← literal expression
  unless SQLite.ExprCollation.kind? expression == some .binary do
    unsupported "comparison requires an explicit non-BINARY collation"
  let ctx : CoreExpr.Context := { schema, sourceName := schema.name }
  if ctx.hasBooleanColumn expression then unsupported "row-dependent boolean keyword comparison"
  let target ← match schema.columns[index]? with
    | some target => .ok target
    | none => .error "comparison column is out of range"
  let aff := SQLite.Scalar.comparisonAffinity (some target.affinity)
    (SQLite.Scalar.expressionAffinity expression)
  unless aff == .blob || aff.comparison == target.affinity.comparison do
    unsupported "comparison requiring conversion of the stored column"
  return SQLite.PhysicalAffinity.comparison aff value

def findColumn? (schema : Core.Schema) (name : String) : Option Nat :=
  schema.column? name

def column (schema : Core.Schema) (name : String) : Except String Nat :=
  match findColumn? schema name with
  | some index => .ok index
  | none => .error s!"no such column: {name}"

abbrev indexColumn := CoreIndexPrepare.indexColumn

def columnRef? : Expr → Option (Option String × String)
  | .column qualifier name => some (qualifier, name)
  | _ => none

theorem columnRef?_eq_some_iff {expression : Expr}
    {qualifier : Option String} {name : String} :
    columnRef? expression = some (qualifier, name) ↔
      expression = .column qualifier name := by
  cases expression <;> simp [columnRef?]

/-- One proof-friendly implementation of the symmetric SQL comparison shape.
The left column keeps priority when both operands are columns, matching the
previous pattern order and producing the same rejection at `literal right`. -/
def comparisonPredicate (schema : Core.Schema)
    (forward reverse : Nat → Core.Value → Core.Predicate)
    (left right : Expr) : Except String Core.Predicate :=
  match columnRef? left with
  | some (_, name) => do
      let index ← column schema name
      return forward index (← comparisonLiteral schema index right)
  | none => match columnRef? right with
    | some (_, name) => do
        let index ← column schema name
        return reverse index (← comparisonLiteral schema index left)
    | none => unsupported "predicate expression"

def predicate (schema : Core.Schema) : Expr → Except String Core.Predicate
  | .binary .eq left right =>
      comparisonPredicate schema .equal .equal left right
  | .binary .ne left right =>
      comparisonPredicate schema .notEqual .notEqual left right
  | .binary .lt left right =>
      comparisonPredicate schema (.compare .less) (.compare .greater) left right
  | .binary .le left right =>
      comparisonPredicate schema (.compare .lessEqual) (.compare .greaterEqual)
        left right
  | .binary .gt left right =>
      comparisonPredicate schema (.compare .greater) (.compare .less) left right
  | .binary .ge left right =>
      comparisonPredicate schema (.compare .greaterEqual) (.compare .lessEqual)
        left right
  | .isNull (.column _ name) false => .isNull <$> column schema name
  | .isNull (.column _ name) true => .not <$> (.isNull <$> column schema name)
  | .unary .not expression => .not <$> predicate schema expression
  | .binary .and left right =>
      .and <$> predicate schema left <*> predicate schema right
  | .binary .or left right =>
      .or <$> predicate schema left <*> predicate schema right
  | _ => unsupported "predicate expression"

def projectionColumn (schema : Core.Schema) : ResultColumn → Except String (List Nat)
  | { expr := .star none, .. } => .ok schema.visibleColumnIndices
  | { expr := .column _ name, .. } => return [← column schema name]
  | _ => unsupported "projection expression"

def projection (schema : Core.Schema) :
    List ResultColumn → Except String (List Nat)
  | [] => .ok []
  | result :: results =>
      return (← projectionColumn schema result) ++ (← projection schema results)

def orderBy (schema : Core.Schema) :
    List OrderTerm → Except String (List (Nat × Bool))
  | [] => .ok []
  | term :: terms => do
      let ctx : CoreExpr.Context := { schema, sourceName := schema.name }
      match ctx.bindNames term.expr with
      | .column _ name => do
          let index ← column schema name
          let rest ← orderBy schema terms
          unless term.nullsFirst.all (· == !term.descending) do
            unsupported "non-default NULL ordering"
          return (index, term.descending) :: rest
      | _ => unsupported "ORDER BY expression"

def resolvedOrdering (schema : Core.Schema) (source : TableRef) (select : Select) :
    Except String (List OrderTerm) :=
  CoreOrder.resolve { schema, sourceName := source.alias.getD source.name }
    select.columns.toList select.orderBy.toList

def directOrdering (schema : Core.Schema) (source : TableRef) (select : Select) :
    Except String (List (Nat × Bool)) := do
  orderBy schema (← resolvedOrdering schema source select)

def countTarget? (schema : Core.Schema) :
    List ResultColumn → Except String (Option Core.CountTarget)
  | [{ expr := .call name arguments star, .. }] =>
      if canonical name != "count" then .ok none
      else if star && arguments.isEmpty then .ok (some .star)
      else match arguments.toList, star with
        | [.column qualifier name], false =>
            if qualifier.isSome then .ok none
            else return some (.column (← column schema name))
        | _, _ => .ok none
  | _ => .ok none

def sumColumn? (schema : Core.Schema) :
    List ResultColumn → Except String (Option Nat)
  | [{ expr := .call name arguments false, .. }] =>
      match arguments.toList with
      | [.column qualifier columnName] =>
          if qualifier.isSome then .ok none
          else if canonical name == "sum" then return some (← column schema columnName)
          else .ok none
      | _ => .ok none
  | _ => .ok none

def extremeColumn? (schema : Core.Schema) :
    List ResultColumn → Except String (Option (Bool × Nat))
  | [{ expr := .call name arguments false, .. }] =>
      match arguments.toList with
      | [.column qualifier columnName] =>
          if qualifier.isSome then .ok none
          else if canonical name == "min" then return some (true, ← column schema columnName)
          else if canonical name == "max" then return some (false, ← column schema columnName)
          else .ok none
      | _ => .ok none
  | _ => .ok none

def groupColumns (schema : Core.Schema) : List Expr → Except String (List Nat)
  | [] => .ok []
  | expression :: expressions => do
      let ctx : CoreExpr.Context := { schema, sourceName := schema.name }
      match ctx.bindNames expression with
      | .column _ name => return (← column schema name) :: (← groupColumns schema expressions)
      | _ => unsupported "GROUP BY expression"

def boundGroupOutput (schema : Core.Schema) (groups : List Nat) :
    ResultColumn → Except String Core.GroupOutput
  | { expr := .column _ name, .. } => do
      let columnIndex ← column schema name
      match groups.findIdx? (· = columnIndex) with
      | some position => .ok (.key position)
      | none => .error s!"non-aggregate column is not in GROUP BY: {name}"
  | { expr := .call name arguments true, .. } =>
      if canonical name == "count" && arguments.isEmpty then .ok .countStar
      else unsupported "aggregate expression"
  | { expr := .call name arguments false, .. } =>
      match arguments.toList with
      | [.column _ columnName] =>
          if canonical name == "count" then
            .countColumn <$> column schema columnName
          else if canonical name == "sum" then
            .sumColumn <$> column schema columnName
          else if canonical name == "avg" then
            .averageColumn <$> column schema columnName
          else if canonical name == "total" then
            .totalColumn <$> column schema columnName
          else if canonical name == "min" then
            .minColumn <$> column schema columnName
          else if canonical name == "max" then
            .maxColumn <$> column schema columnName
          else unsupported "aggregate expression"
      | _ => unsupported "group projection expression"
  | _ => unsupported "group projection expression"

def groupOutput (schema : Core.Schema) (groups : List Nat) (result : ResultColumn) :
    Except String Core.GroupOutput :=
  let ctx : CoreExpr.Context := { schema, sourceName := schema.name }
  boundGroupOutput schema groups { result with expr := ctx.bindNames result.expr }

def groupOutputs (schema : Core.Schema) (groups : List Nat) :
    List ResultColumn → Except String (List Core.GroupOutput)
  | [] => .ok []
  | result :: results =>
      return (← groupOutput schema groups result) ::
        (← groupOutputs schema groups results)

/-- SQLite's aTabColMap keeps the first ordinary target; ipkColumn is
reassigned at every rowid/INTEGER PRIMARY KEY alias, keeping the last one. -/
def insertValueIndex (rowidColumn target : Nat) (indices : List Nat) : Option Nat :=
  if target == rowidColumn then
    ((indices.zipIdx.filter (fun entry => entry.1 == target)).getLast?).map (·.2)
  else indices.findIdx? (· == target)

theorem insertValueIndex_rowid (rowidColumn : Nat) (indices : List Nat) :
    insertValueIndex rowidColumn rowidColumn indices =
      ((indices.zipIdx.filter (fun entry => entry.1 == rowidColumn)).getLast?).map (·.2) := by
  simp [insertValueIndex]

theorem insertValueIndex_ordinary (rowidColumn target : Nat) (indices : List Nat)
    (different : target ≠ rowidColumn) :
    insertValueIndex rowidColumn target indices = indices.findIdx? (· == target) := by
  simp [insertValueIndex, different]

def rowValuesTyped (schema : Core.Schema) (insertColumns : Option (Array String))
    (expressions : Array Expr) (defaults : List (Option CoreReturning.Cell) := []) :
    Except String (List CoreReturning.Cell) := do
  let defaultAt := fun (index : Nat) (target : Core.Column) =>
    CoreReturning.defaultFromRegister target (defaults[index]?.getD none)
  -- Repeated targets keep the first ordinary value and the last rowid value.
  -- SQLite still binds discarded expressions and functions before assignment.
  unless expressions.all SQLite.Scalar.admitted do
    for expression in expressions do
      if let some message := SQLite.Scalar.resolutionError (fun _ _ => false) expression then throw message
    unsupported "INSERT expression"
  if expressions.isEmpty then
    let _ ← insertColumns.mapM (fun names => names.toList.mapM (column schema))
    return ← schema.columns.mapIdxM defaultAt
  match insertColumns with
  | none =>
      unless expressions.size = schema.visibleColumns.length do
        throw s!"table {schema.name} has {schema.visibleColumns.length} columns but {expressions.size} values were supplied"
      let visibleValues ← expressions.toList.mapM CoreReturning.literal
      let pairs := schema.visibleColumnIndices.zip visibleValues
      schema.columns.mapIdxM fun index target =>
        match pairs.find? (fun pair => pair.1 == index) with
        | some pair => .ok (pair.2.writeAffinity target.affinity)
        | none => defaultAt index target
  | some names =>
      unless names.size = expressions.size do
        throw "INSERT column/value count mismatch"
      let indices ← names.toList.mapM (column schema)
      schema.columns.mapIdxM fun targetIndex target =>
        match insertValueIndex schema.primaryKey targetIndex indices with
        | some index => CoreReturning.columnLiteral target expressions[index]!
        | none => defaultAt targetIndex target

def rowValues (schema : Core.Schema) (insertColumns : Option (Array String))
    (expressions : Array Expr) : Except String (List Core.Value) :=
  (List.map (·.value)) <$> rowValuesTyped schema insertColumns expressions

/-- Evaluate every source field before duplicate target columns are selected.
Multi-VALUES uses a source row in SQLite, so even discarded fields can fail. -/
def evaluateInsertExpressions (expressions : Array Expr) : Except String (Array Expr) := do
  let evaluated ← expressions.toList.mapM literal
  let values ← evaluated.mapM CoreExpr.value
  return (values.map (fun value => Expr.literal value)).toArray

theorem evaluateInsertExpressions_evaluated (expressions result : Array Expr)
    (success : evaluateInsertExpressions expressions = .ok result) :
    ∃ values, expressions.toList.mapM literal = .ok values := by
  cases evaluated : expressions.toList.mapM literal with
  | error message => simp [evaluateInsertExpressions, evaluated, bind, Except.bind] at success
  | ok values => exact ⟨values, rfl⟩

/-- Keep single-VALUES lazy selection, but materialize a complete source row
for multi-VALUES before the ordinary first-column/last-rowid mapping. Validate
arity, target names and expression admission before evaluating any value. -/
def inputRowValuesTyped (schema : Core.Schema) (columns : Option (Array String))
    (evaluateAll : Bool) (expressions : Array Expr) (defaults : List (Option CoreReturning.Cell) := []) : Except String (List CoreReturning.Cell) := do
  if !evaluateAll then return ← rowValuesTyped schema columns expressions defaults
  unless expressions.all SQLite.Scalar.admitted do
    for expression in expressions do
      if let some message := SQLite.Scalar.resolutionError (fun _ _ => false) expression then throw message
    unsupported "INSERT expression"
  match columns with
  | none =>
      unless expressions.size = schema.visibleColumns.length do throw "INSERT column/value count mismatch"
  | some names =>
      unless names.size = expressions.size do throw "INSERT column/value count mismatch"
      discard <| names.toList.mapM (column schema)
  rowValuesTyped schema columns (← evaluateInsertExpressions expressions) defaults

def inputRowValues (schema : Core.Schema) (columns : Option (Array String))
    (evaluateAll : Bool) (expressions : Array Expr) : Except String (List Core.Value) :=
  (List.map (·.value)) <$> inputRowValuesTyped schema columns evaluateAll expressions

@[simp] theorem inputRowValues_single (schema : Core.Schema)
    (columns : Option (Array String)) (expressions : Array Expr) :
    inputRowValues schema columns false expressions = rowValues schema columns expressions := by
  simp [inputRowValues, inputRowValuesTyped, rowValues]

def executeCommand (state : Core.State) (command : Core.Command) :
    Except String (Core.State × List Core.Result) := do
  let (next, result) ← Core.execute state command
  return (next, [result])

theorem executeCommand_eq_core (state : Core.State) (command : Core.Command) :
    executeCommand state command =
      (fun outcome => (outcome.1, [outcome.2])) <$>
        Core.execute state command := by
  rfl

def insertRows (state : Core.State) (table : String)
    (schema : Core.Schema) (columns : Option (Array String)) (replacing : Bool)
    (inputs : List (Array Expr)) (evaluateAll : Bool := false) :
    Except String (Core.State × List Core.Result) :=
  match inputs with
  | [] => .ok (state, [])
  | expressions :: rows => do
      let values ← inputRowValues schema columns evaluateAll expressions
      let command : Core.Command :=
        if replacing then .replace table values else .insert table values
      let (next, result) ← Core.execute state command
      let (finalState, results) ← insertRows next table schema columns replacing rows evaluateAll
      return (finalState, result :: results)

def executeIgnoredInsert (state : Core.State) (table : String) (stored : Core.Table)
    (values : List Core.Value) : Except String (Core.State × Core.Result) := do
  if ← CoreInsertIgnore.shouldInsert stored values then Core.execute state (.insert table values)
  else return (state, {})

theorem executeIgnoredInsert_skips (state : Core.State) (table : String) (stored : Core.Table)
    (values : List Core.Value) (skip : CoreInsertIgnore.shouldInsert stored values = .ok false) :
    executeIgnoredInsert state table stored values = .ok (state, {}) := by
  simp [executeIgnoredInsert, skip, bind, Except.bind, pure, Except.pure]

/-- Recheck conflicts after each successful row. A skipped row contributes no
change and does not reserve a rowid; ordinary expression failures still abort. -/
def ignoreInsertRows (state : Core.State) (table : String) (schema : Core.Schema)
    (columns : Option (Array String)) (inputs : List (Array Expr)) (evaluateAll : Bool := false) :
    Except String (Core.State × List Core.Result) :=
  match inputs with
  | [] => .ok (state, [])
  | expressions :: rows => do
      let values ← inputRowValues schema columns evaluateAll expressions
      let stored ← match state.database.findTable? table with
        | some stored => pure stored
        | none => throw s!"no such table: {table}"
      let (next, result) ← executeIgnoredInsert state table stored values
      let (finalState, results) ← ignoreInsertRows next table schema columns rows evaluateAll
      return (finalState, result :: results)

theorem insertRows_singleton (state : Core.State) (table : String)
    (schema : Core.Schema) (columns : Option (Array String))
    (replacing : Bool) (expressions : Array Expr) (values : List Core.Value)
    (translated : rowValues schema columns expressions = .ok values) :
    insertRows state table schema columns replacing [expressions] =
      executeCommand state
        (if replacing then .replace table values else .insert table values) := by
  cases replacing with
  | false =>
      simp only [insertRows, inputRowValues_single, translated, Bool.false_eq_true, if_false,
        executeCommand, bind, Functor.map, Except.bind, pure]
  | true =>
      simp only [insertRows, inputRowValues_single, translated, if_pos rfl, executeCommand,
        bind, Functor.map, Except.bind, pure]

/-- Execute a sequence of already translated Core commands, retaining the
per-row result list used by SQL multi-row INSERT. -/
def runCoreCommands : Core.State → List Core.Command →
    Except String (Core.State × List Core.Result)
  | state, [] => .ok (state, [])
  | state, command :: commands => do
      let (next, result) ← Core.execute state command
      let (finalState, results) ← runCoreCommands next commands
      return (finalState, result :: results)

/-- The schema planner can skip a row or emit a checked deletion/insertion
trace. The SQL change count records only the accepted candidate. -/
def executeSchemaRow (state : Core.State) (table : String) (values : List Core.Value)
    (old : Option Core.Integer) : Except String (Core.State × Core.Result) := do
  let stored ← match state.database.findTable? table with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  let prepared ← CoreDefaultConflict.plan stored values old
  match prepared with
  | none => return (state, {})
  | some (_, trace) =>
      let (next, _) ← runCoreCommands state trace
      return (next, { changes := 1 })

theorem executeSchemaRow_skips (state : Core.State) (table : String) (stored : Core.Table)
    (values : List Core.Value) (old : Option Core.Integer)
    (found : state.database.findTable? table = some stored)
    (skip : CoreDefaultConflict.plan stored values old = .ok none) :
    executeSchemaRow state table values old = .ok (state, {}) := by
  simp [executeSchemaRow, found, skip, bind, Except.bind, pure, Except.pure]

/-- Apply the schema's default constraint policies to each current candidate. -/
def schemaInsertRows (state : Core.State) (table : String) (schema : Core.Schema)
    (columns : Option (Array String)) (inputs : List (Array Expr)) (evaluateAll : Bool := false) :
    Except String (Core.State × List Core.Result) :=
  match inputs with
  | [] => .ok (state, [])
  | expressions :: rows => do
      let values ← inputRowValues schema columns evaluateAll expressions
      let (next, result) ← executeSchemaRow state table values none
      let (finalState, results) ← schemaInsertRows next table schema columns rows evaluateAll
      return (finalState, result :: results)

theorem runCoreCommands_append (state : Core.State)
    (left right : List Core.Command) :
    runCoreCommands state (left ++ right) =
      match runCoreCommands state left with
      | .error message => .error message
      | .ok (middle, leftResults) =>
          match runCoreCommands middle right with
          | .error message => .error message
          | .ok (next, rightResults) =>
              .ok (next, leftResults ++ rightResults) := by
  induction left generalizing state with
  | nil =>
      cases outcome : runCoreCommands state right with
      | error message => simp [runCoreCommands, outcome]
      | ok pair =>
          rcases pair with ⟨next, results⟩
          simp [runCoreCommands, outcome]
  | cons command commands induction =>
      simp only [List.cons_append, runCoreCommands]
      cases head : Core.execute state command with
      | error message =>
          simp [head, bind, Functor.map, Except.bind]
      | ok outcome =>
          rcases outcome with ⟨middle, result⟩
          simp only [head, bind, Functor.map, Except.bind]
          rw [induction middle]
          cases prefixRun : runCoreCommands middle commands with
          | error message =>
              simp [prefixRun, bind, Functor.map, Except.bind]
          | ok outcome =>
              rcases outcome with ⟨afterPrefix, prefixResults⟩
              cases suffix : runCoreCommands afterPrefix right with
              | error message =>
                  simp [prefixRun, suffix, bind, Functor.map, Except.bind,
                    pure, Except.pure, pure]
              | ok outcome =>
                  rcases outcome with ⟨next, suffixResults⟩
                  simp [prefixRun, suffix, List.append_assoc, bind, Functor.map,
                    Except.bind, pure, Except.pure, pure]

end CoreSQL

end SQLeanite
