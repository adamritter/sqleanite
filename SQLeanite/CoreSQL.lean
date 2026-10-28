import SQLeanite.SQLite.CtasCatalog
import SQLeanite.CoreSchemaTranslate
import SQLeanite.CoreJoinUsing
import SQLeanite.CoreOuterJoin
import SQLeanite.CoreSavepoint
import SQLeanite.CoreAutoIncrement
import SQLeanite.CoreEngine
import SQLeanite.CoreNames
import SQLeanite.CoreCreateTableAs
import SQLeanite.CoreSchemaPragma
import SQLeanite.CoreHeaderPragma
import SQLeanite.CoreSchemaDrop
import SQLeanite.CoreSchemaRename
import SQLeanite.CoreSchemaAdd
import SQLeanite.CoreSchemaDropColumn
import SQLeanite.CoreOptimizerBridge
import SQLeanite.CoreTokenGrammar
import SQLeanite.SQLSurface
import SQLeanite.CoreExpr
import SQLeanite.CoreOrder
import SQLeanite.CoreAggregate
import SQLeanite.CoreAggregateOrder
import SQLeanite.CoreAggregateHaving
import SQLeanite.CoreCompound
import SQLeanite.CoreCompoundTail
import SQLeanite.CoreCollatedGroup
import SQLeanite.CoreGrouped
import SQLeanite.CoreReturning
import SQLeanite.CoreLastInsert
import SQLeanite.CoreInsertPrepare
import SQLeanite.CoreDefaultConflict
import SQLeanite.CoreNullConflict
import SQLeanite.CoreInsertIgnore
import SQLeanite.CoreUpdateIgnore
import SQLeanite.CoreUpdateReplace
import SQLeanite.CoreUpdateRow
import SQLeanite.CoreUpdateScan
import SQLeanite.SQLite.Values
import SQLeanite.SQLite.StaticCondition

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

/-- CREATE INDEX cannot name an implicit rowid alias. A real column with
that spelling is still permitted. -/
def indexColumn (schema : Core.Schema) (name : String) : Except String Nat :=
  match schema.catalogColumns.findIdx? (fun column => canonical column.name == canonical name) with
  | some index => .ok index
  | none => .error s!"no such column: {name}"

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

private def executeCommand (state : Core.State) (command : Core.Command) :
    Except String (Core.State × List Core.Result) := do
  let (next, result) ← Core.execute state command
  return (next, [result])

theorem executeCommand_eq_core (state : Core.State) (command : Core.Command) :
    executeCommand state command =
      (fun outcome => (outcome.1, [outcome.2])) <$>
        Core.execute state command := by
  rfl

private def insertRows (state : Core.State) (table : String)
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

/-- The live recursive INSERT executor is exactly command-trace execution
once every VALUES row has translated. -/
theorem insertRows_eq_runCoreCommands (state : Core.State) (table : String)
    (schema : Core.Schema) (columns : Option (Array String))
    (replacing evaluateAll : Bool) : ∀ (rows : List (Array Expr))
      (values : List (List Core.Value)),
      rows.mapM (inputRowValues schema columns evaluateAll) = .ok values →
      insertRows state table schema columns replacing rows evaluateAll =
        runCoreCommands state (values.map fun row =>
          if replacing then .replace table row else .insert table row)
  | [], values, translated => by
      have empty : values = [] := by simpa using Except.ok.inj translated
      subst values
      rfl
  | expressions :: rows, values, translated => by
      cases head : inputRowValues schema columns evaluateAll expressions with
      | error message =>
          simp [List.mapM_cons, head, bind, Functor.map, Except.bind,
            pure, Except.pure, pure] at translated
      | ok value =>
          cases tail : rows.mapM (inputRowValues schema columns evaluateAll) with
          | error message =>
              simp [List.mapM_cons, head, tail, bind, Functor.map, Except.bind,
                pure, Except.pure, pure] at translated
          | ok remaining =>
              have valuesEqual : values = value :: remaining := by
                simp [List.mapM_cons, head, tail, bind, Functor.map,
                  Except.bind, pure, Except.pure, pure] at translated
                exact translated.symm
              subst values
              simp only [insertRows, head, List.map_cons, runCoreCommands]
              let command : Core.Command :=
                if replacing then .replace table value else .insert table value
              cases execution : Core.execute state command with
              | error message =>
                  simp [command, execution, bind, Functor.map, Except.bind]
              | ok outcome =>
                  rcases outcome with ⟨next, result⟩
                  have induction := insertRows_eq_runCoreCommands next table
                    schema columns replacing evaluateAll rows remaining tail
                  simp [command, execution, induction, bind, Functor.map,
                    Except.bind, pure, Except.pure, pure]

def updateAssignments (schema : Core.Schema) :
    List (String × Expr) → Except String (List (Nat × Core.Value))
  | [] => .ok []
  | assignment :: assignments => do
      let index ← column schema assignment.1
      if index = schema.primaryKey || index = schema.declaredPrimaryKey then
        throw "updating the PRIMARY KEY is outside the verified MVP"
      let remaining ← updateAssignments schema assignments
      if remaining.any (fun candidate => candidate.1 == index) then
        throw s!"duplicate UPDATE assignment: {assignment.1}"
      let target ← match schema.columns[index]? with
        | some target => .ok target
        | none => .error "UPDATE column is out of range"
      let value ← columnLiteral target assignment.2
      let ctx : CoreExpr.Context := { schema, sourceName := schema.name }
      if ctx.hasBooleanColumn assignment.2 then unsupported "row-dependent boolean keyword assignment"
      return (index, value) :: remaining

/-- Resolve every UPDATE name even when the row set is empty. SQLite uses
only the last assignment to a repeated target; earlier expressions are still
bound, but are not evaluated. Key changes use a separate delete/insert trace
that rechecks the rowid, declared key and explicit indexes after each row. -/
def expressionAssignmentsWith (allowKeys : Bool) (ctx : CoreExpr.Context) : List (String × Expr) →
    Except String (List (Nat × Expr))
  | [] => .ok []
  | (name, expression) :: rest => do
      let index ← column ctx.schema name
      ctx.validate expression
      let remaining ← expressionAssignmentsWith allowKeys ctx rest
      if remaining.any (fun next => next.1 == index) then return remaining
      if (index = ctx.schema.primaryKey || index = ctx.schema.declaredPrimaryKey) && !allowKeys then
        throw "updating the declared PRIMARY KEY is outside this path"
      return (index, expression) :: remaining

def expressionAssignments (ctx : CoreExpr.Context) := expressionAssignmentsWith false ctx

/-- All RHS expressions read the same original row; affinity is applied only
to each completed value. No earlier assignment changes a later RHS binding. -/
def evaluateAssignmentsTyped (ctx : CoreExpr.Context) (row : Core.Row) :
    List (Nat × Expr) → Except String (List (Nat × CoreReturning.Cell))
  | [] => .ok []
  | (index, expression) :: rest => do
      let target ← match ctx.schema.columns[index]? with
        | some target => .ok target
        | none => .error "UPDATE column is out of range"
      let input ← CoreReturning.Cell.fromScalar (← ctx.evalTyped row.values expression)
      let remaining ← evaluateAssignmentsTyped ctx row rest
      return (index, input.writeAffinity target.affinity) :: remaining

def evaluateAssignments (ctx : CoreExpr.Context) (row : Core.Row)
    (assignments : List (Nat × Expr)) : Except String (List (Nat × Core.Value)) :=
  (List.map (fun (index, input) => (index, input.value))) <$> evaluateAssignmentsTyped ctx row assignments

/-- Compile each selected original row to a point update on its stable rowid.
The entire trace is computed before it is run; an error cannot publish a prefix. -/
def rowUpdateCommands (tableName : String) (ctx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (condition : Option Expr) :
    List Core.Row → Except String (List Core.Command)
  | [] => .ok []
  | row :: rows => do
      unless ← ctx.matches row.values condition do
        return ← rowUpdateCommands tableName ctx assignments condition rows
      let updates ← evaluateAssignments ctx row assignments
      let commands ← rowUpdateCommands tableName ctx assignments condition rows
      return .updateWhere tableName updates
        (some (.equal ctx.schema.primaryKey (.integer row.rowid))) :: commands

/-- One logical rowid update compiles to a deletion and an insertion. The
pair count is retained independently of the two Core commands' change counts. -/
structure RekeyBatch where
  commands : List Core.Command
  changes : Nat
  paired : commands.length = 2 * changes

def RekeyBatch.empty : RekeyBatch := ⟨[], 0, rfl⟩

def RekeyBatch.prepend (tableName : String) (primaryKey : Nat) (old : Core.Integer)
    (values : List Core.Value) (tail : RekeyBatch) : RekeyBatch := {
  commands := .deleteWhere tableName (some (.equal primaryKey (.integer old))) ::
    .insert tableName values :: tail.commands
  changes := tail.changes + 1
  paired := by simp only [List.length_cons, tail.paired]; omega }

def rowRekeyBatch (tableName : String) (ctx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (condition : Option Expr) :
    List Core.Row → Except String RekeyBatch
  | [] => .ok .empty
  | row :: rows => do
      unless ← ctx.matches row.values condition do
        return ← rowRekeyBatch tableName ctx assignments condition rows
      let updates ← evaluateAssignments ctx row assignments
      let values := Core.applyAssignments row.values updates
      -- UPDATE rowid=NULL is a type error; INSERT's automatic allocation must
      -- not turn it into a new rowid. Validate the completed row first.
      let _ ← Core.Row.create ctx.schema values
      let tail ← rowRekeyBatch tableName ctx assignments condition rows
      return RekeyBatch.prepend tableName ctx.schema.primaryKey row.rowid values tail

theorem rowRekeyBatch_changes_le (tableName : String) (ctx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (condition : Option Expr) (rows : List Core.Row)
    (batch : RekeyBatch)
    (translated : rowRekeyBatch tableName ctx assignments condition rows = .ok batch) :
    batch.changes ≤ rows.length := by
  induction rows generalizing batch with
  | nil => simp [rowRekeyBatch] at translated; subst batch; simp [RekeyBatch.empty]
  | cons row rows ih =>
      simp only [rowRekeyBatch] at translated
      cases selected : ctx.matches row.values condition with
      | error message => simp [selected, bind, Except.bind] at translated
      | ok keep =>
        cases keep with
        | false =>
          simp [selected, bind, Except.bind] at translated
          exact Nat.le_trans (ih _ translated) (by simp)
        | true =>
          cases updates : evaluateAssignments ctx row assignments with
          | error message => simp [selected, updates, bind, Except.bind] at translated
          | ok values =>
            cases created : Core.Row.create ctx.schema (Core.applyAssignments row.values values) with
            | error message => simp [selected, updates, created, bind, Except.bind] at translated
            | ok patched =>
              cases tail : rowRekeyBatch tableName ctx assignments condition rows with
              | error message => simp [selected, updates, created, tail, bind, Except.bind] at translated
              | ok rest =>
                simp [selected, updates, created, tail, bind, Except.bind, pure, Except.pure] at translated
                subst batch
                simpa [RekeyBatch.prepend] using Nat.succ_le_succ (ih _ tail)

/-- Plan the bounded equality/IN searches needed by expression scans. A
primary-key equality takes precedence over IN membership; otherwise a constant
primary-key IN list (or a sole indexed IN condition) is materialized before the
row loop. This preserves errors in search keys even for empty tables/LIMIT 1.
Other access-plan choices remain with the general scan. -/
def expressionSearch (ctx : CoreExpr.Context) (stored : Core.Table)
    (condition : Option Expr) : Except String (Option Core.Predicate) := do
  let terms := condition.toList.flatMap fun expression =>
    SQLite.Scalar.conditionTerms (SQLite.Scalar.prepare (ctx.bindNames expression))
  let primaryColumn := fun expression => match expression with
    | .column qualifier name => ctx.column? qualifier name == some stored.schema.primaryKey
    | _ => false
  let primaryEquality := terms.find? fun term => match term with
    | .binary .eq a b =>
        (primaryColumn a && SQLite.Scalar.constantExpression b) ||
        (primaryColumn b && SQLite.Scalar.constantExpression a)
    | _ => false
  if let some (.binary .eq left right) := primaryEquality then
    let value := if primaryColumn left then right else left
    return some (.equal stored.schema.primaryKey
      (← comparisonLiteral stored.schema stored.schema.primaryKey value))
  let inColumn := fun term => match term with
    | .inList (.column qualifier name) values false true =>
        if !values.isEmpty && values.all SQLite.Scalar.constantExpression then
          ctx.column? qualifier name
        else none
    | _ => none
  let candidate := (terms.find? fun term => inColumn term == some stored.schema.primaryKey)
    |>.orElse (fun _ => if terms.length == 1 then
      terms.find? fun term => (inColumn term).any fun column =>
        stored.indexes.any fun index => index.column == column
      else none)
  match candidate with
  | some (.inList argument values false true) =>
      let some column := inColumn (Expr.inList argument values false true) | return none
      let affinity := (ctx.affinity argument).getD .blob
      let keys ← values.toList.mapM fun expression => do
        let value ← ctx.eval [] expression
        SQLSurface.value (SQLite.Scalar.applyComparisonAffinity affinity value)
      return keys.foldr (fun value remaining =>
        some (match remaining with
          | none => .equal column value
          | some rest => .or (.equal column value) rest)) none
  | _ => return none

/-- A chosen primary-key equality fixes that column for WHERE's constant
analysis. The actual row still supplies its value and comparison affinity. -/
def expressionSearchContext (ctx : CoreExpr.Context) (search : Option Core.Predicate) :
    CoreExpr.Context :=
  match search with
  | some (.equal column _) =>
      if column == ctx.schema.primaryKey then { ctx with fixedColumns := [column] } else ctx
  | _ => ctx

/-- Constant propagation can make a whole WHERE term independent of the
row loop. Evaluate those terms with the equality key before seeking the table,
even when the search will find no row. Other columns remain unbound here. -/
def expressionSearchReady (ctx : CoreExpr.Context) (search : Option Core.Predicate)
    (condition : Option Expr) : Except String Bool :=
  match search with
  | some (.equal column value) =>
      if ctx.fixedColumns.contains column then
        let row : List Core.Value := (List.range ctx.schema.columns.length).map fun index =>
          if index == column then value else .null
        ctx.constantMatchesOn row condition
      else .ok true
  | _ => .ok true

def expressionUpdatePlan (tableName : String) (alias : Option String) (stored : Core.Table)
    (assignments : List (String × Expr)) (condition : Option Expr) :
    Except String (List Core.Command) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let bound ← expressionAssignments ctx assignments
  let _ ← condition.mapM ctx.validate
  unless ← ctx.constantMatches condition do return []
  let search ← expressionSearch ctx stored condition
  let ctx := expressionSearchContext ctx search
  unless ← expressionSearchReady ctx search condition do return []
  rowUpdateCommands tableName ctx bound condition (stored.rows.filter (Core.selects search))

def rekeyUpdatePlan (tableName : String) (alias : Option String) (stored : Core.Table)
    (assignments : List (String × Expr)) (condition : Option Expr) : Except String RekeyBatch := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  let _ ← condition.mapM ctx.validate
  unless ← ctx.constantMatches condition do return .empty
  let search ← expressionSearch ctx stored condition
  let ctx := expressionSearchContext ctx search
  unless ← expressionSearchReady ctx search condition do return .empty
  rowRekeyBatch tableName ctx bound condition (stored.rows.filter (Core.selects search))

/-- Evaluate RHS values against each original input row and check its
constraints against the state left by earlier accepted candidates. The pure
Except boundary still discards the entire statement on ordinary errors. -/
def ignoredUpdateRows (state : Core.State) (tableName : String) (ctx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (condition : Option Expr) :
    List Core.Row → Except String (Core.State × List Core.Result)
  | [] => .ok (state, [])
  | row :: rows => do
      unless ← ctx.matches row.values condition do
        return ← ignoredUpdateRows state tableName ctx assignments condition rows
      let updates ← evaluateAssignments ctx row assignments
      let values := Core.applyAssignments row.values updates
      let (next, result) ← CoreUpdateIgnore.row state tableName ctx.schema row.rowid values
      let (finalState, results) ← ignoredUpdateRows next tableName ctx assignments condition rows
      return (finalState, result :: results)

def executeIgnoredUpdate (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (assignments : List (String × Expr)) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  let _ ← condition.mapM ctx.validate
  unless ← ctx.constantMatches condition do return (state, [{}])
  let search ← expressionSearch ctx stored condition
  let ctx := expressionSearchContext ctx search
  unless ← expressionSearchReady ctx search condition do return (state, [{}])
  let rows ← CoreUpdateScan.order ctx stored bound condition (stored.rows.filter (Core.selects search))
  let (next, results) ← ignoredUpdateRows state tableName ctx bound condition rows
  return (next, [{ changes := (results.map (·.changes)).sum }])

def schemaUpdateRows (state : Core.State) (tableName : String) (ctx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (condition : Option Expr) :
    List Core.Row → Except String (Core.State × List Core.Result)
  | [] => .ok (state, [])
  | row :: rows => do
      unless ← ctx.matches row.values condition do
        return ← schemaUpdateRows state tableName ctx assignments condition rows
      let updates ← evaluateAssignments ctx row assignments
      let values := Core.applyAssignments row.values updates
      let (next, result) ← executeSchemaRow state tableName values (some row.rowid)
      let (finalState, results) ← schemaUpdateRows next tableName ctx assignments condition rows
      return (finalState, result :: results)

def executeSchemaScanUpdate (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (assignments : List (String × Expr)) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  CoreNullConflict.validate stored.schema (bound.map Prod.fst) none
  let _ ← condition.mapM ctx.validate
  unless ← ctx.constantMatches condition do return (state, [{}])
  let search ← expressionSearch ctx stored condition
  let ctx := expressionSearchContext ctx search
  unless ← expressionSearchReady ctx search condition do return (state, [{}])
  let rows ← CoreUpdateScan.order ctx stored bound condition (stored.rows.filter (Core.selects search))
  let (next, results) ← schemaUpdateRows state tableName ctx bound condition rows
  return (next, [{ changes := (results.map (·.changes)).sum }])

def executeRekeyUpdate (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (assignments : List (String × Expr)) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  let batch ← rekeyUpdatePlan tableName alias stored assignments condition
  let (next, _) ← runCoreCommands state batch.commands
  return (next, [{ changes := batch.changes }])

theorem executeRekeyUpdate_eq_runCoreCommands
    (state : Core.State) (tableName : String) (alias : Option String) (stored : Core.Table)
    (assignments : List (String × Expr)) (condition : Option Expr) (batch : RekeyBatch)
    (translated : rekeyUpdatePlan tableName alias stored assignments condition = .ok batch) :
    executeRekeyUpdate state tableName alias stored assignments condition =
      (fun outcome => (outcome.1, [{ changes := batch.changes }])) <$>
        runCoreCommands state batch.commands := by
  simp only [executeRekeyUpdate, translated, bind, Except.bind]
  cases executed : runCoreCommands state batch.commands with
  | error message => rfl
  | ok outcome => rfl

def executeExpressionUpdate (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (assignments : List (String × Expr)) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  let commands ← expressionUpdatePlan tableName alias stored assignments condition
  let (next, results) ← runCoreCommands state commands
  return (next, [{ changes := (results.map (·.changes)).sum }])

/-- The SQL fallback executes exactly its precomputed Core trace, preserving
Core constraint checking and the statement-level Except failure boundary. -/
theorem executeExpressionUpdate_eq_runCoreCommands
    (state : Core.State) (tableName : String) (alias : Option String) (stored : Core.Table)
    (assignments : List (String × Expr)) (condition : Option Expr) (commands : List Core.Command)
    (translated : expressionUpdatePlan tableName alias stored assignments condition = .ok commands) :
    executeExpressionUpdate state tableName alias stored assignments condition =
      (fun outcome => (outcome.1, [{ changes := (outcome.2.map (·.changes)).sum }])) <$>
        runCoreCommands state commands := by
  simp only [executeExpressionUpdate, translated, bind, Except.bind]
  cases executed : runCoreCommands state commands with
  | error message => rfl
  | ok outcome => rfl

theorem rowUpdateCommands_length_le (tableName : String) (ctx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (condition : Option Expr) (rows : List Core.Row)
    (commands : List Core.Command)
    (translated : rowUpdateCommands tableName ctx assignments condition rows = .ok commands) :
    commands.length ≤ rows.length := by
  induction rows generalizing commands with
  | nil => simp [rowUpdateCommands] at translated; subst commands; simp
  | cons row rows ih =>
      simp only [rowUpdateCommands] at translated
      cases selected : ctx.matches row.values condition with
      | error message => simp [selected, bind, Except.bind] at translated
      | ok keep =>
        cases keep with
        | false =>
          simp [selected, bind, Except.bind] at translated
          exact Nat.le_trans (ih _ translated) (by simp)
        | true =>
          cases updates : evaluateAssignments ctx row assignments with
          | error message => simp [selected, updates, bind, Except.bind] at translated
          | ok values =>
            cases tail : rowUpdateCommands tableName ctx assignments condition rows with
            | error message => simp [selected, updates, tail, bind, Except.bind] at translated
            | ok rest =>
              simp [selected, updates, tail, bind, Except.bind, pure, Except.pure] at translated
              subst commands
              simpa using Nat.succ_le_succ (ih _ tail)

/-- Bind and evaluate DELETE predicates against the original statement
snapshot before running any Core mutation. A late expression error therefore
cannot publish a prefix of the selected deletions. -/
def rowDeleteCommands (tableName : String) (ctx : CoreExpr.Context)
    (condition : Option Expr) : List Core.Row → Except String (List Core.Command)
  | [] => .ok []
  | row :: rows => do
      let selected ← ctx.matches row.values condition
      let commands ← rowDeleteCommands tableName ctx condition rows
      if selected then
        return .deleteWhere tableName
          (some (.equal ctx.schema.primaryKey (.integer row.rowid))) :: commands
      else return commands

def expressionDeletePlan (tableName : String) (alias : Option String) (stored : Core.Table)
    (condition : Option Expr) : Except String (List Core.Command) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let _ ← condition.mapM ctx.validate
  unless ← ctx.constantMatches condition do return []
  let search ← expressionSearch ctx stored condition
  let ctx := expressionSearchContext ctx search
  unless ← expressionSearchReady ctx search condition do return []
  rowDeleteCommands tableName ctx condition (stored.rows.filter (Core.selects search))

/-- SQLite disables multi-row one-pass UPDATE when REPLACE can delete other
rows. Selected rowids are frozen first, but their values are re-read immediately
before each update. A missing row skips RHS evaluation. -/
def replacedUpdateRows (state : Core.State) (tableName : String) (ctx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) :
    List Core.Integer → Except String (Core.State × List Core.Result)
  | [] => .ok (state, [])
  | rowid :: rowids => do
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {tableName}"
      match stored.findRowid? rowid with
      | none => replacedUpdateRows state tableName ctx assignments rowids
      | some row => do
          let updates ← evaluateAssignments ctx row assignments
          let trace ← CoreUpdateReplace.plan stored rowid (Core.applyAssignments row.values updates)
          let (next, _) ← runCoreCommands state trace
          let (finalState, results) ← replacedUpdateRows next tableName ctx assignments rowids
          return (finalState, { changes := 1 } :: results)

theorem replacedUpdateRows_missing (state : Core.State) (tableName : String)
    (ctx : CoreExpr.Context) (assignments : List (Nat × Expr)) (stored : Core.Table)
    (rowid : Core.Integer) (rowids : List Core.Integer)
    (found : state.database.findTable? tableName = some stored)
    (missing : stored.findRowid? rowid = none) :
    replacedUpdateRows state tableName ctx assignments (rowid :: rowids) =
      replacedUpdateRows state tableName ctx assignments rowids := by
  simp [replacedUpdateRows, found, missing, bind, Except.bind, pure, Except.pure]

def executeReplacedUpdate (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (assignments : List (String × Expr)) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  CoreNullConflict.validate stored.schema (bound.map Prod.fst) (some .replace)
  let trace ← expressionDeletePlan tableName alias stored condition
  let rowids ← CoreUpdateReplace.pending tableName stored.schema.primaryKey trace
  let (next, results) ← replacedUpdateRows state tableName ctx bound rowids
  return (next, [{ changes := (results.map (·.changes)).sum }])

def schemaReplacementRows (state : Core.State) (tableName : String) (ctx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) :
    List Core.Integer → Except String (Core.State × List Core.Result)
  | [] => .ok (state, [])
  | rowid :: rowids => do
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {tableName}"
      match stored.findRowid? rowid with
      | none => schemaReplacementRows state tableName ctx assignments rowids
      | some row => do
          let updates ← evaluateAssignments ctx row assignments
          let (next, result) ← executeSchemaRow state tableName (Core.applyAssignments row.values updates) (some rowid)
          let (finalState, results) ← schemaReplacementRows next tableName ctx assignments rowids
          return (finalState, result :: results)

def executeSchemaUpdate (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (assignments : List (String × Expr)) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  if CoreDefaultConflict.primaryPolicy stored.schema != .replace then
    return ← executeSchemaScanUpdate state tableName alias stored assignments condition
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  CoreNullConflict.validate stored.schema (bound.map Prod.fst) none
  let trace ← expressionDeletePlan tableName alias stored condition
  let rowids ← CoreUpdateReplace.pending tableName stored.schema.primaryKey trace
  let (next, results) ← schemaReplacementRows state tableName ctx bound rowids
  return (next, [{ changes := (results.map (·.changes)).sum }])

/-- Source compilers can prepare a complete physical candidate while keeping
its typed registers and the actual UPDATE footprint. Ordinary Core callers
omit the preparation pass and retain their original command semantics. -/
structure RowInput where
  cells : List CoreReturning.Cell
  assigned : Option (List Nat) := none
  converted : List Nat := []

/-- Preserve the source distinction between an omitted target list and an
explicit list even when both lower to the same physical column positions. -/
structure InsertTargets where
  columns : Option (Array String)
  implicitWidth : Option Nat := none

structure RowPreparation where
  row : Core.State → Core.Table → ConflictAction → RowInput → Except String (Option RowInput)
  targets : Option (Array String) → Except String InsertTargets := fun columns => .ok { columns }

def prepareInsertTargets (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) (preparation : Option RowPreparation) :
    Except String InsertTargets := do
  let targets ← match preparation with
    | none => pure ({ columns } : InsertTargets)
    | some prepare => prepare.targets columns
  match source with
  | .inl rows =>
      if targets.implicitWidth.isSome && rows.size == 1 && rows[0]!.isEmpty then
        return { targets with columns := none }
      return targets
  | .inr _ => return targets

theorem prepareInsertTargets_ordinary (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) :
    prepareInsertTargets columns source none = .ok { columns } := by
  cases source <;> rfl

/-- RETURNING forces the two-phase UPDATE path even for IGNORE. Values are
read from the current pending row; its original name binds RETURNING while the
UPDATE alias remains the source for RHS and WHERE expressions. -/
def updateReturningRow (state : Core.State) (tableName : String) (ctx outputCtx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (conflict : ConflictAction) (projection : List Expr)
    (rowid : Core.Integer) (preparation : Option RowPreparation := none) : Except String (Core.State × Option (List Core.Value)) := do
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {tableName}"
  let some row := stored.findRowid? rowid | return (state, none)
  let updates ← evaluateAssignmentsTyped ctx row assignments
  let cells := updates.foldl (fun values (index, input) => values.set index input)
    (row.values.map CoreReturning.Cell.plain)
  let some input ← (match preparation with
    | none => pure (some ({ cells, assigned := some (assignments.map Prod.fst), converted := List.range stored.schema.columns.length } : RowInput))
    | some prepare => prepare.row state stored conflict { cells, assigned := some (assignments.map Prod.fst), converted := List.range stored.schema.columns.length }) | return (state, none)
  let cells := input.cells
  let assigned := input.assigned.getD (assignments.map Prod.fst)
  let prepared ← if conflict == .default || conflict == .replace || conflict == .abort then
      CoreReturning.prepareValues ctx.schema cells true
        (if conflict == .replace then some .replace else if conflict == .abort then some .abort else none)
    else pure (some cells)
  let some cells := prepared | return (state, none)
  let values := cells.map (·.value)
  let outcome ← if stored.hasChecks then
      CoreUpdateRow.apply state stored rowid values assigned conflict
    else if conflict == .default then
      executeSchemaRow state tableName values (some rowid)
    else if conflict == .ignore then
      CoreUpdateIgnore.row state tableName ctx.schema rowid values
    else if conflict == .replace then do
      let trace ← CoreUpdateReplace.plan stored rowid values
      let (next, _) ← runCoreCommands state trace
      pure (next, { changes := 1 })
    else do
      let _ ← Core.Row.create ctx.schema values
      let (removed, _) ← Core.execute state (.deleteWhere tableName
        (some (.equal ctx.schema.primaryKey (.integer rowid))))
      Core.execute removed (.insert tableName values)
  let outcome := if outcome.2.changes == 0 then outcome else
    match values[ctx.schema.primaryKey]? with
    | some (.integer rowid) =>
        (outcome.1.recordForeignWrite tableName rowid (some assigned), outcome.2)
    | _ => outcome
  CoreReturning.updatedOutput outputCtx cells projection outcome

theorem updateReturningRow_missing (state : Core.State) (tableName : String)
    (ctx outputCtx : CoreExpr.Context) (assignments : List (Nat × Expr)) (conflict : ConflictAction)
    (projection : List Expr) (rowid : Core.Integer) (stored : Core.Table)
    (found : state.database.findTable? tableName = some stored) (missing : stored.findRowid? rowid = none) :
    updateReturningRow state tableName ctx outputCtx assignments conflict projection rowid = .ok (state, none) := by
  simp [updateReturningRow, found, missing, bind, Except.bind, pure, Except.pure]

def updateReturningRows (state : Core.State) (tableName : String) (ctx outputCtx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (conflict : ConflictAction) (projection : List Expr)
    (rowids : List Core.Integer) (preparation : Option RowPreparation := none) :
    Except String (Core.State × List (List Core.Value)) :=
  match rowids with
  | [] => .ok (state, [])
  | rowid :: rowids => do
      let (next, output) ← updateReturningRow state tableName ctx outputCtx assignments conflict projection rowid preparation
      let (finalState, outputs) ← updateReturningRows next tableName ctx outputCtx assignments conflict projection rowids preparation
      return (finalState, output.toList ++ outputs)

theorem updateReturningRows_length_le (state : Core.State) (tableName : String)
    (ctx outputCtx : CoreExpr.Context) (assignments : List (Nat × Expr)) (conflict : ConflictAction)
    (projection : List Expr) (rowids : List Core.Integer) (next : Core.State) (outputs : List (List Core.Value))
    (success : updateReturningRows state tableName ctx outputCtx assignments conflict projection rowids = .ok (next, outputs)) :
    outputs.length ≤ rowids.length := by
  induction rowids generalizing state next outputs with
  | nil =>
      simp [updateReturningRows] at success
      rcases success with ⟨_, rfl⟩
      simp
  | cons rowid rowids ih =>
      cases head : updateReturningRow state tableName ctx outputCtx assignments conflict projection rowid with
      | error message => simp [updateReturningRows, head, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨middle, output⟩
          cases tail : updateReturningRows middle tableName ctx outputCtx assignments conflict projection rowids with
          | error message => simp [updateReturningRows, head, tail, bind, Except.bind] at success
          | ok pair =>
              rcases pair with ⟨finalState, more⟩
              simp [updateReturningRows, head, tail, bind, Except.bind, pure, Except.pure] at success
              rcases success with ⟨_, rfl⟩
              have bound := ih middle finalState more tail
              cases output <;> simp_all <;> omega

def executeUpdateReturning (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (assignments : List (String × Expr)) (condition : Option Expr)
    (conflict : ConflictAction) (returning : Array ResultColumn) (preparation : Option RowPreparation := none) :
    Except String (Core.State × List Core.Result) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let outputCtx : CoreExpr.Context := { schema := stored.schema, sourceName := tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  if conflict == .default || conflict == .replace then
    CoreNullConflict.validate stored.schema (bound.map Prod.fst) (if conflict == .replace then some .replace else none)
  let projection ← CoreReturning.prepare outputCtx returning.toList
  let trace ← expressionDeletePlan tableName alias stored condition
  let rowids ← CoreUpdateReplace.pending tableName stored.schema.primaryKey trace
  let (next, outputs) ← updateReturningRows state tableName ctx outputCtx bound conflict projection rowids preparation
  return (next, [{ rows := outputs, changes := outputs.length }])

def executeExpressionDelete (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  let commands ← expressionDeletePlan tableName alias stored condition
  let (next, results) ← runCoreCommands state commands
  return (next, [{ changes := (results.map (·.changes)).sum }])

/-- Preserve the original selected rows for DELETE RETURNING. All output is
computed before Core mutation/publication; an expression error cannot commit a
prefix of the deletions or emit a partial RETURNING result. -/
def executeDeleteReturning (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (condition : Option Expr) (columns : Array ResultColumn) :
    Except String (Core.State × List Core.Result) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := tableName }
  let expressions ← CoreReturning.prepare ctx columns.toList
  let commands ← expressionDeletePlan tableName alias stored condition
  let rows ← CoreReturning.deletionOutput stored ctx expressions commands
  let (next, results) ← runCoreCommands state commands
  return (next, [{ rows, changes := (results.map (·.changes)).sum }])

theorem executeExpressionDelete_eq_runCoreCommands
    (state : Core.State) (tableName : String) (alias : Option String) (stored : Core.Table)
    (condition : Option Expr) (commands : List Core.Command)
    (translated : expressionDeletePlan tableName alias stored condition = .ok commands) :
    executeExpressionDelete state tableName alias stored condition =
      (fun outcome => (outcome.1, [{ changes := (outcome.2.map (·.changes)).sum }])) <$>
        runCoreCommands state commands := by
  simp only [executeExpressionDelete, translated, bind, Except.bind]
  cases executed : runCoreCommands state commands with
  | error message => rfl
  | ok outcome => rfl

theorem rowDeleteCommands_length_le (tableName : String) (ctx : CoreExpr.Context)
    (condition : Option Expr) (rows : List Core.Row) (commands : List Core.Command)
    (translated : rowDeleteCommands tableName ctx condition rows = .ok commands) :
    commands.length ≤ rows.length := by
  induction rows generalizing commands with
  | nil => simp [rowDeleteCommands] at translated; subst commands; simp
  | cons row rows ih =>
    simp only [rowDeleteCommands] at translated
    cases selected : ctx.matches row.values condition with
    | error message => simp [selected, bind, Except.bind] at translated
    | ok keep =>
      cases tail : rowDeleteCommands tableName ctx condition rows with
      | error message => simp [selected, tail, bind, Except.bind] at translated
      | ok rest =>
        have bound := ih _ tail
        cases keep <;>
          simp [selected, tail, bind, Except.bind, pure, Except.pure] at translated <;>
          subst commands <;> simp only [List.length_cons] <;> omega

structure JoinContext where
  leftTable : String
  rightTable : String
  leftName : String
  rightName : String
  leftSchema : Core.Schema
  rightSchema : Core.Schema
  shared : List CoreJoinUsing.Column := []
  preferRightShared : Bool := false
  coalesceShared : Bool := false

def joinColumn (context : JoinContext) (qualifier : Option String) (name : String) :
    Except String CoreJoin.ColumnRef := do
  let columnName := canonical name
  match qualifier.map canonical with
  | some owner =>
      if owner == context.leftName then
        return ⟨.left, ← column context.leftSchema columnName⟩
      else if owner == context.rightName then
        return ⟨.right, ← column context.rightSchema columnName⟩
      else throw s!"no such table or alias: {owner}"
  | none =>
      let sources : List CoreExpr.Context := [
        { schema := context.leftSchema, sourceName := context.leftName },
        { schema := context.rightSchema, sourceName := context.rightName }]
      match CoreJoinUsing.nameCandidates sources none columnName with
      | [(0, index)] => .ok ⟨.left, index⟩
      | [(1, index)] => .ok ⟨.right, index⟩
      | [(0, li), (1, ri)] =>
          if CoreJoinUsing.merges context.shared name li ri then
            .ok (if context.preferRightShared then ⟨.right, ri⟩ else ⟨.left, li⟩)
          else .error s!"ambiguous column name: {name}"
      | [] => .error s!"no such column: {name}"
      | _ => .error s!"ambiguous column name: {name}"

/-- FULL USING resolves an unqualified shared name to a nullable coalesce.
Qualified references still address their original source cells. -/
def joinNamedOperand (context : JoinContext) (qualifier : Option String) (name : String) :
    Except String CoreJoin.Operand := do
  let reference ← joinColumn context qualifier name
  if context.coalesceShared && qualifier.isNone then
    if let some shared := context.shared.find? (fun shared => shared.name == name.toLower) then
      return .mergedColumn none shared.left shared.right
  return .column reference

def joinHasColumn (context : JoinContext) (name : String) : Bool :=
  (findColumn? context.leftSchema name).isSome || (findColumn? context.rightSchema name).isSome

def joinBindNames (context : JoinContext) (expression : Expr) : Expr :=
  SQLite.Scalar.bindNames (joinHasColumn context) expression

/-- Unary plus and COLLATE preserve a column's value. Their affinity and
comparison-collation effects are handled separately from source binding. -/
def joinColumnAtomFuel? : Nat → Expr → Option (Option String × String)
  | 0, _ => none
  | fuel + 1, expression => match expression with
    | .column qualifier name => some (qualifier, name)
    | .unary .plus expression | .collate expression _ => joinColumnAtomFuel? fuel expression
    | .call name arguments false =>
        (SQLite.Probability.input? name arguments).bind (joinColumnAtomFuel? fuel)
    | _ => none

def joinColumnAtom? (expression : Expr) : Option (Option String × String) :=
  joinColumnAtomFuel? expression.height expression

def joinOperand (context : JoinContext) (expression : Expr) : Except String CoreJoin.Operand :=
  let bound := joinBindNames context expression
  match joinColumnAtom? bound with
  | some (qualifier, name) => joinNamedOperand context qualifier name
  | none => .literal <$> literal bound

def joinColumnDefinition (context : JoinContext) (reference : CoreJoin.ColumnRef) :
    Except String Core.Column :=
  let schema := match reference.side with
    | .left => context.leftSchema
    | .right => context.rightSchema
  match schema.columns[reference.column]? with
  | some column => .ok column
  | none => .error "join column is out of range"

def joinOperandAffinity (context : JoinContext) (expression : Expr)
    (operand : CoreJoin.Operand) : Except String (Option SQLite.Affinity) :=
  let unaffined := match SQLite.ExprCollation.strip expression with
    | .unary .plus _ => true
    | .call name _ _ => SQLite.Probability.recognizesName name
    | _ => false
  if unaffined then .ok none
  else match operand with
    | .column reference | .coercedColumn _ reference =>
        do return some (← joinColumnDefinition context reference).affinity
    | .literal _ => .ok (SQLite.Scalar.expressionAffinity expression)
    | .mergedColumn _ left _ =>
        do return some (← joinColumnDefinition context ⟨.left, left⟩).affinity

theorem joinOperandAffinity_plus (context : JoinContext) (expression : Expr)
    (operand : CoreJoin.Operand) : joinOperandAffinity context (.unary .plus expression) operand = .ok none := rfl

def joinOperandCoerce (context : JoinContext) (aff : SQLite.Affinity) :
    CoreJoin.Operand → Except String CoreJoin.Operand
  | .literal value => .ok (.literal (SQLite.PhysicalAffinity.comparison aff value))
  | operand@(.column reference) => do
      let target ← joinColumnDefinition context reference
      if aff == .blob || aff.comparison == target.affinity.comparison then return operand
      return .coercedColumn aff reference
  | .mergedColumn prior left right =>
      .ok (.mergedColumn (if aff == .blob then prior else some aff) left right)
  | .coercedColumn _ _ => unsupported "repeated join operand coercion"

def joinComparison (context : JoinContext)
    (operation : CoreJoin.Operand → CoreJoin.Operand → CoreJoin.Predicate)
    (left right : Expr) : Except String CoreJoin.Predicate := do
  let kind ← SQLite.ExprCollation.require (SQLite.ExprCollation.binaryKind? left right)
  let a ← joinOperand context left
  let b ← joinOperand context right
  let aff := SQLite.Scalar.comparisonAffinity
    (← joinOperandAffinity context left a) (← joinOperandAffinity context right b)
  return CoreJoin.Predicate.withCollation kind
    (operation (← joinOperandCoerce context aff a) (← joinOperandCoerce context aff b))

/-- USING applies ordinary left-to-right equality affinity to each declared
shared column. The result is an ON predicate, before LEFT null-extension. -/
def joinUsingPredicate (context : JoinContext) : Except String (Option CoreJoin.Predicate) :=
  context.shared.foldlM (fun prior column => do
    let left : CoreJoin.Operand := .column ⟨.left, column.left⟩
    let right : CoreJoin.Operand := .column ⟨.right, column.right⟩
    let a ← joinColumnDefinition context ⟨.left, column.left⟩
    let b ← joinColumnDefinition context ⟨.right, column.right⟩
    let aff := SQLite.Scalar.comparisonAffinity (some a.affinity) (some b.affinity)
    let comparison : CoreJoin.Predicate := .equal
      (← joinOperandCoerce context aff left) (← joinOperandCoerce context aff right)
    return some ((prior.map (fun predicate => .and predicate comparison)).getD comparison)) none

/-- The unshadowed TRUE/FALSE keyword on the right of IS selects truth
conversion. Other operands use ordinary comparison affinity with NULL safety. -/
def joinIsComparison (context : JoinContext) (negated : Bool) (left right : Expr) :
    Except String CoreJoin.Predicate := do
  let predicate ← match SQLite.Scalar.isTruthKeyword? right with
    | some expected => do
        let operand ← joinOperand context left
        pure (CoreJoin.Predicate.isTruth operand expected)
    | none => joinComparison context CoreJoin.Predicate.isEqual left right
  return if negated then .not predicate else predicate

def joinOperandList (context : JoinContext) : List Expr → Except String (List CoreJoin.Operand)
  | [] => .ok []
  | expression :: rest => List.cons <$> joinOperand context expression <*> joinOperandList context rest

/-- IN-list comparison ignores right-operand affinity and collation. Parser
preparation separately handles empty lists and a single constant choice. -/
def joinInList (context : JoinContext) (argument : Expr) (values : Array Expr)
    (negated applyLeftAffinity : Bool) : Except String CoreJoin.Predicate := do
  let left ← joinOperand context argument
  let right ← joinOperandList context values.toList
  let kind ← SQLite.ExprCollation.require (SQLite.ExprCollation.kind? argument)
  let affinity ← if applyLeftAffinity then
      (fun found => found.getD .blob) <$> joinOperandAffinity context argument left
    else pure .blob
  let left ← joinOperandCoerce context affinity left
  let right ← right.mapM (joinOperandCoerce context affinity)
  let predicate := CoreJoin.Predicate.membership kind left right
  return if negated then .not predicate else predicate

def joinPredicateRaw (context : JoinContext) : Expr →
    Except String CoreJoin.Predicate
  | .inList argument values negated affinity => joinInList context argument values negated affinity
  | .binary .is left right => joinIsComparison context false left right
  | .binary .isNot left right => joinIsComparison context true left right
  | .binary .eq left right =>
      joinComparison context .equal left right
  | .binary .ne left right =>
      joinComparison context .notEqual left right
  | .binary .lt left right =>
      joinComparison context (.compare .less) left right
  | .binary .le left right =>
      joinComparison context (.compare .lessEqual) left right
  | .binary .gt left right =>
      joinComparison context (.compare .greater) left right
  | .binary .ge left right =>
      joinComparison context (.compare .greaterEqual) left right
  | .isNull operand false => .isNull <$> joinOperand context operand
  | .isNull operand true => .not <$> (.isNull <$> joinOperand context operand)
  | .unary .not expression => .not <$> joinPredicateRaw context expression
  | .binary .and left right =>
      .and <$> joinPredicateRaw context left <*> joinPredicateRaw context right
  | .binary .or left right =>
      .or <$> joinPredicateRaw context left <*> joinPredicateRaw context right
  | expression => .truthy <$> joinOperand context expression

/-- All names/functions resolve before code generation. Each top-level AND
term is generated separately, even when an earlier false term skips its value. -/
def joinStaticAdmitted (context : JoinContext) (prepared : Expr) (outer : Bool := false) : Bool :=
  !(prepared.any (fun expression => match expression with
      | .column qualifier name => !(joinColumn context qualifier name).isOk
      | _ => SQLite.StaticCondition.resolutionForbidden expression)) &&
    (SQLite.Scalar.conditionTerms prepared).all (fun term => SQLite.StaticCondition.codegenAdmitted term outer)

/-- Name binding precedes parser preparation. A statically decided condition
still validates every resolved name and every required generated operation. -/
def joinPredicate (context : JoinContext) (expression : Expr) (outer : Bool := false) : Except String CoreJoin.Predicate := do
  let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
  match SQLite.StaticCondition.classify outer prepared with
  | none => joinPredicateRaw context prepared
  | some truth =>
      unless joinStaticAdmitted context prepared outer do unsupported "unbound or invalid static join condition"
      return CoreJoin.Predicate.constant truth

def joinSideColumns (side : CoreJoin.Side) (count : Nat) :
    List CoreJoin.ColumnRef :=
  (List.range count).map fun index => ⟨side, index⟩

def joinVisibleColumns (side : CoreJoin.Side) (schema : Core.Schema) :
    List CoreJoin.ColumnRef :=
  schema.visibleColumnIndices.map fun index => ⟨side, index⟩

/-- Literal/unary atoms are total before row evaluation. Boolean keywords
are constants only after source-column name binding has left them unbound. -/
def joinLiteralExpression : Expr → Bool
  | .literal .. => true
  | .unary _ expression => joinLiteralExpression expression
  | expression => (SQLite.Scalar.booleanKeyword? expression).isSome

/-- Expanded left stars keep their original positions/names but RIGHT USING
reads the merged value from the right input, including qualified left stars. -/
def joinMergedStar (context : JoinContext) (reference : CoreJoin.ColumnRef) : CoreJoin.ColumnRef :=
  if context.preferRightShared && reference.side == .left then
    match context.shared.find? (fun column => column.left == reference.column) with
    | some column => ⟨.right, column.right⟩
    | none => reference
  else reference

theorem joinMergedStar_right (context : JoinContext) (index : Nat) (shared : CoreJoinUsing.Column)
    (prefer : context.preferRightShared = true)
    (found : context.shared.find? (fun column => column.left == index) = some shared) :
    joinMergedStar context ⟨.left, index⟩ = ⟨.right, shared.right⟩ := by
  simp [joinMergedStar, prefer, found]

def joinStarOperand (context : JoinContext) (reference : CoreJoin.ColumnRef) : CoreJoin.Operand :=
  if context.coalesceShared && reference.side == .left then
    match context.shared.find? (fun shared => shared.left == reference.column) with
    | some shared => .mergedColumn none shared.left shared.right
    | none => .column reference
  else .column (joinMergedStar context reference)

def joinResultExpr (context : JoinContext) : Expr → Except String (List CoreJoin.Operand)
  | .column qualifier name => return [← joinNamedOperand context qualifier name]
  | .star none =>
      .ok ((joinVisibleColumns .left context.leftSchema ++
        (joinVisibleColumns .right context.rightSchema).filter
          (fun reference => !CoreJoinUsing.suppressesRight context.shared reference.column)).map
            (joinStarOperand context))
  | .star (some qualifier) =>
      let owner := canonical qualifier
      if owner == context.leftName then
        .ok ((joinVisibleColumns .left context.leftSchema).map
          (joinStarOperand context))
      else if owner == context.rightName then
        .ok ((joinVisibleColumns .right context.rightSchema).map CoreJoin.Operand.column)
      else .error s!"no such table or alias: {qualifier}"
  | expression => do
      unless joinLiteralExpression expression do unsupported "join projection"
      return [.literal (← literal expression)]

def joinResultColumn (context : JoinContext) (column : ResultColumn) :
    Except String (List CoreJoin.Operand) :=
  joinResultExpr context (joinBindNames context column.expr)

def joinProjection (context : JoinContext) : List ResultColumn →
    Except String (List CoreJoin.Operand)
  | [] => .ok []
  | result :: results =>
      return (← joinResultColumn context result) ++ (← joinProjection context results)

/-- Only explicit aliases and expanded stars provide ORDER BY result names.
A plain selected source column retains ordinary ambiguity checks. -/
def joinOrderName (context : JoinContext) (column : ResultColumn)
    (operand : CoreJoin.Operand) : Option String :=
  match column.expr, operand with
  | .star _, .column reference =>
      let schema := if reference.side == .left then context.leftSchema else context.rightSchema
      (schema.columns[reference.column]?).map (·.name)
  | .star _, .mergedColumn _ left _ => (context.leftSchema.columns[left]?).map (·.name)
  | .star _, _ => none
  | _, _ => column.alias

def joinOrderColumns (context : JoinContext) : List ResultColumn →
    Except String (List (CoreJoin.Operand × Option String))
  | [] => .ok []
  | column :: columns => do
      let references ← joinResultColumn context column
      return references.map (fun reference => (reference, joinOrderName context column reference)) ++
        (← joinOrderColumns context columns)

theorem joinOrderColumns_projection (context : JoinContext) (columns : List ResultColumn) :
    (joinOrderColumns context columns).map (List.map Prod.fst) = joinProjection context columns := by
  induction columns with
  | nil => rfl
  | cons column columns ih =>
      cases head : joinResultColumn context column with
      | error message => simp [joinOrderColumns, joinProjection, head, bind, Except.bind, Except.map]
      | ok references =>
          cases tail : joinOrderColumns context columns with
          | error message =>
              simp [tail, Except.map] at ih
              simp [joinOrderColumns, joinProjection, head, tail, ← ih, bind, Except.bind, Except.map]
          | ok named =>
              simp [tail, Except.map] at ih
              simp [joinOrderColumns, joinProjection, head, tail, ← ih, bind, Except.bind,
                pure, Except.pure, Except.map, List.map_append, List.map_map, Function.comp_def]

/-- Unary operations on literals stay constant and cannot fail during sorting.
Integer ordinal recognition runs before this test. -/
def joinOrderConstant : Expr → Bool
  | .literal .. => true
  | .unary _ expression => joinOrderConstant expression
  | _ => false

def joinOrderOutputReference : CoreJoin.Operand → Except String (Option CoreJoin.ColumnRef)
  | .column reference => .ok (some reference)
  | .literal _ => .ok none
  | .coercedColumn .. | .mergedColumn .. => unsupported "computed join output ordering"

def joinOrderReference (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (expression : Expr) :
    Except String (Option CoreJoin.ColumnRef) := do
  let expression := SQLite.Scalar.prepare (CoreOrder.keyExpression expression)
  if let some name := CoreOrder.bareName? expression then
    if let some output := columns.find? (fun output => output.2.any (fun alias => canonical alias == canonical name)) then
      return ← joinOrderOutputReference output.1
  if let some position := CoreOrder.ordinal? expression then
    unless 1 ≤ position && position.toNat ≤ columns.length do
      throw "ORDER BY position is outside the result columns"
    let some output := columns[position.toNat - 1]? | throw "ORDER BY position is out of range"
    return ← joinOrderOutputReference output.1
  if joinOrderConstant expression then return none
  if let some name := SQLite.Scalar.quotedIdentifier? expression then
    return some (← joinColumn context none name)
  if let some truth := SQLite.Scalar.booleanKeyword? expression then
    let name := SQLite.Scalar.booleanName truth
    if (findColumn? context.leftSchema name).isSome || (findColumn? context.rightSchema name).isSome then
      return some (← joinColumn context none name)
    return none
  match expression with
  | .column qualifier name => return some (← joinColumn context qualifier name)
  | _ => unsupported "join ORDER BY expression"

def joinOrderBy (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) : List OrderTerm →
    Except String (List CoreJoin.OrderTerm)
  | [] => .ok []
  | term :: terms => do
      let specification ← CoreOrder.specification term
      let reference ← joinOrderReference context columns term.expr
      let rest ← joinOrderBy context columns terms
      match reference with
      | none => return rest
      | some reference =>
          return {
            reference
            descending := specification.descending
            nullsFirst := some specification.nullsFirst
            collation := specification.collation } :: rest

/-- A rowid equality conjunct makes each surviving pair unique on either
side. It can satisfy later ORDER terms without an inner table sort. -/
def joinHasRowidEquality (left right : Core.Schema) : CoreJoin.Predicate → Bool
  | .and first second => joinHasRowidEquality left right first ||
      joinHasRowidEquality left right second
  | predicate => decide (predicate = CoreJoin.rowidOn left.primaryKey right.primaryKey ∨
      predicate = .equal (.column ⟨.right, right.primaryKey⟩) (.column ⟨.left, left.primaryKey⟩))

/-- A leading rowid ORDER term can determine table traversal. INNER joins
may exchange their sources; CROSS and LEFT joins retain the left outer loop.
Terms of the outer row are constant within an inner scan. A leading inner
rowid term can reverse that scan; other terms use a subsequent block sorter. -/
def joinDistinctScanOrder (left right : Core.Schema) (mayExchange oneToOne : Bool)
    (terms : List (CoreJoin.ColumnRef × Bool)) : List (CoreJoin.ColumnRef × Bool) :=
  match terms with
  | (reference, descending) :: rest =>
      let outerSchema := if reference.side == .left then left else right
      let innerSchema := if reference.side == .left then right else left
      let innerSide := if reference.side == .left then CoreJoin.Side.right else .left
      let inner := rest.find? (fun term => term.1.side == innerSide)
      let fullyOrdered := oneToOne || inner.all (fun term => term.1.column == innerSchema.primaryKey)
      if reference.column == outerSchema.primaryKey &&
          (reference.side == .left || (mayExchange && fullyOrdered)) then
        let innerDescending := inner.any fun term =>
          term.1.column == innerSchema.primaryKey && term.2
        [(reference, descending), (⟨innerSide, innerSchema.primaryKey⟩, innerDescending)]
      else []
  | [] => []

/-- A rowid equality can make the left table the point-lookup inner side.
Coercion of the right operand does not change which source drives that scan. -/
def joinProbesLeftRowid (left : Core.Schema) : CoreJoin.Predicate → Bool
  | .and first second => joinProbesLeftRowid left first || joinProbesLeftRowid left second
  | .equal (.column ⟨.left, index⟩) (.column ⟨.right, _⟩)
  | .equal (.column ⟨.left, index⟩) (.coercedColumn _ ⟨.right, _⟩)
  | .equal (.column ⟨.right, _⟩) (.column ⟨.left, index⟩)
  | .equal (.coercedColumn _ ⟨.right, _⟩) (.column ⟨.left, index⟩) => index == left.primaryKey
  | _ => false

def joinLookupScanOrder (left right : Core.Schema) (mayExchange : Bool)
    (on where_ : Option CoreJoin.Predicate) (terms : List CoreJoin.OrderTerm) :
    List (CoreJoin.ColumnRef × Bool) :=
  if mayExchange &&
      !(on.any (joinHasRowidEquality left right) || where_.any (joinHasRowidEquality left right)) &&
      (on.any (joinProbesLeftRowid left) || where_.any (joinProbesLeftRowid left)) then
    let descending := terms.head?.any fun term =>
      term.reference.side == .right && term.reference.column == right.primaryKey && term.descending
    [(⟨.right, right.primaryKey⟩, descending), (⟨.left, left.primaryKey⟩, false)]
  else []

/-- SQL compound operations use numeric comparison keys; output rows retain
SQLite's selected original storage classes. -/
def combineRows (operation : CompoundOp) (left right : List (List Core.Value)) :
    List (List Core.Value) := CoreCompound.combine operation left right

/-- Membership is stated over SQL keys, not raw representations: INTEGER 1
and REAL 1.0 name the same set member. -/
theorem mem_combineRows (operation : CompoundOp) (left right : List (List Core.Value))
    (key : List Core.Value) :
    key ∈ (combineRows operation left right).map Core.distinctRowKey ↔
      match operation with
      | .unionAll | .unionDistinct => key ∈ left.map Core.distinctRowKey ∨ key ∈ right.map Core.distinctRowKey
      | .intersect => key ∈ left.map Core.distinctRowKey ∧ key ∈ right.map Core.distinctRowKey
      | .except => key ∈ left.map Core.distinctRowKey ∧ key ∉ right.map Core.distinctRowKey :=
  CoreCompound.combine_keys operation left right key

theorem combineRows_nodup (operation : CompoundOp)
    (notAll : operation ≠ .unionAll) (left right : List (List Core.Value)) :
    (combineRows operation left right).Nodup :=
  List.Pairwise.of_map Core.distinctRowKey (fun _ _ h equal => h (congrArg _ equal))
    (CoreCompound.combine_keys_nodup operation left right notAll)

def RowsHaveWidth (width : Nat) (rows : List (List Core.Value)) : Prop :=
  ∀ row ∈ rows, row.length = width

theorem combineRows_width (operation : CompoundOp) (width : Nat)
    {left right : List (List Core.Value)}
    (leftWidth : RowsHaveWidth width left)
    (rightWidth : RowsHaveWidth width right) :
    RowsHaveWidth width (combineRows operation left right) := by
  intro row member
  rcases List.mem_append.mp (CoreCompound.combine_subset operation left right member) with member | member
  · exact leftWidth row member
  · exact rightWidth row member

theorem combineRows_denotes (operation : CompoundOp) (left right : List (List Core.Value)) :
    RelationalAlgebra.ofList ((combineRows operation left right).map Core.distinctRowKey) =
      CoreCompound.denotation operation
        (RelationalAlgebra.ofList (left.map Core.distinctRowKey))
        (RelationalAlgebra.ofList (right.map Core.distinctRowKey)) :=
  CoreCompound.combine_denotes operation left right

structure SelectExecution where
  state : Core.State
  result : Core.Result
  width : Nat

def joinContext (leftSource rightSource : TableRef) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String JoinContext := do
  return {
    leftTable, rightTable
    leftName := canonical (leftSource.alias.getD leftSource.name)
    rightName := canonical (rightSource.alias.getD rightSource.name)
    leftSchema, rightSchema
    shared := ← CoreJoinUsing.columns leftSchema rightSchema rightSource
    preferRightShared := rightSource.rightJoin && !rightSource.leftJoin
    coalesceShared := rightSource.rightJoin && rightSource.leftJoin }

/-- BETWEEN remains one predicate during fixed-column preparation. Its
virtual range bounds are exposed only to cursor-constraint selection. -/
def joinSearchRangeTerms (terms : List Expr) : List Expr :=
  terms.flatMap fun term => match SQLite.ExprCollation.strip term with
    | .call "__sqlean_between" arguments false =>
        match arguments.toList with
        | [argument, lower, upper] => [.binary .ge argument lower, .binary .le argument upper]
        | _ => [term]
    | _ => [term]

theorem joinSearchRangeTerms_between (argument lower upper : Expr) :
    joinSearchRangeTerms [.call "__sqlean_between" #[argument, lower, upper] false] =
      [.binary .ge argument lower, .binary .le argument upper] := rfl

/-- Computed cursor keys cannot be erased by an empty-pair adapter. A bare
column is required on the inner side; unary plus disqualifies it as in SQLite. -/
def joinComputedCursorKey (context : JoinContext) (expression : Expr) : Bool :=
  let expression := SQLite.Scalar.prepare (joinBindNames context expression)
  let target := fun expression => match SQLite.ExprCollation.strip expression with
    | .column qualifier name => (joinColumn context qualifier name).toOption.any (fun ref => ref.side == .right)
    | _ => false
  let value := fun expression => !(joinOperand context expression).isOk &&
    !expression.any (fun node => match node with
      | .column qualifier name => !(joinColumn context qualifier name).toOption.any (fun ref => ref.side == .left)
      | _ => false)
  (joinSearchRangeTerms (SQLite.Scalar.conditionTerms expression)).any fun term => match SQLite.ExprCollation.strip term with
    | .binary operation left right =>
        [.eq, .is, .lt, .le, .gt, .ge].contains operation &&
          ((target left && value right) || (target right && value left))
    | .inList column values false _ => target column && values.any value
    | _ => false

/-- Constant rowid membership can drive the first source loop. The general
cursor path owns its ordering rather than a left-major Cartesian product. -/
def joinConstantRowidMembership (context : JoinContext) (expression : Expr) : Bool :=
  (SQLite.Scalar.conditionTerms (SQLite.Scalar.prepare (joinBindNames context expression))).any fun term =>
    match SQLite.ExprCollation.strip term with
    | .inList column values false _ =>
        match SQLite.ExprCollation.strip column with
        | .column qualifier name =>
            (joinColumn context qualifier name).toOption.any (fun ref =>
              ref.column == (if ref.side == .left then context.leftSchema else context.rightSchema).primaryKey) &&
              values.all SQLite.Scalar.constantExpression
        | _ => false
    | _ => false

/-- Index affinity is determined by the declared columns, independently of
the stored row values. USING can use only the compatible side's transient
index when numeric comparison rules exclude the other side. -/
def joinUsingIndexEligible (context : JoinContext) (side : CoreJoin.Side) : Bool :=
  context.shared.any fun shared =>
    let column := if side == .left then shared.left else shared.right
    let schema := if side == .left then context.leftSchema else context.rightSchema
    column != schema.primaryKey &&
      (match context.leftSchema.columns[shared.left]?, context.rightSchema.columns[shared.right]? with
        | some left, some right =>
            let indexed := if side == .left then left.affinity else right.affinity
            let comparison := SQLite.Scalar.comparisonAffinity (some left.affinity) (some right.affinity)
            comparison == .blob || (comparison == .text && indexed == .text) ||
              (SQLite.Scalar.numericAffinity comparison && SQLite.Scalar.numericAffinity indexed)
        | _, _ => false)

theorem joinUsingIndexEligible_without_shared (context : JoinContext) (side : CoreJoin.Side)
    (empty : context.shared = []) : joinUsingIndexEligible context side = false := by
  simp [joinUsingIndexEligible, empty]

/-- Translate the supported two-source SQL shape independently of a materialized
database.  Both the ordinary engine and cold page-directed execution use this
single interpretation, preventing the fast path from acquiring subtly
different alias, projection, or predicate semantics. -/
def joinQueryBound (select : Select) (rightSource : TableRef) (context : JoinContext) :
    Except String CoreJoin.Query := do
  if context.leftName == context.rightName then
    throw "join sources require distinct names or aliases"
  if (rightSource.leftJoin || rightSource.rightJoin) && rightSource.joinOn.any (joinComputedCursorKey context) then
    return ← unsupported "outer condition requires executable cursor planning"
  if !rightSource.leftJoin && !rightSource.rightJoin && !rightSource.crossJoin &&
      rightSource.joinOn.any (joinConstantRowidMembership context) then
    return ← unsupported "constant rowid membership requires cursor planning"
  if !rightSource.leftJoin && !rightSource.rightJoin && !rightSource.crossJoin &&
      !context.shared.any (fun column => column.right == context.rightSchema.primaryKey) &&
      joinUsingIndexEligible context .left && !joinUsingIndexEligible context .right then
    return ← unsupported "USING affinity requires executable cursor planning"
  let explicitOn ← rightSource.joinOn.mapM (fun expression => joinPredicate context expression (rightSource.leftJoin || rightSource.rightJoin))
  let sharedOn ← joinUsingPredicate context
  let on := match explicitOn, sharedOn with
    | none, predicate | predicate, none => predicate
    | some left, some right => some (CoreJoin.Predicate.and left right)
  let where_ ← select.where_.mapM (joinPredicate context)
  let orderColumns ← joinOrderColumns context select.columns.toList
  let orderBy ← joinOrderBy context orderColumns select.orderBy.toList
  let mayExchange := !rightSource.leftJoin && !rightSource.rightJoin && !rightSource.crossJoin
  let lookupScanOrder := joinLookupScanOrder context.leftSchema context.rightSchema mayExchange on where_ orderBy
  return {
    columns := ← joinProjection context select.columns.toList
    on
    kind := if rightSource.leftJoin || rightSource.rightJoin then .left else .inner
    rightWidth := context.rightSchema.columns.length
    where_
    orderBy
    limit := select.limit
    offset := select.offset
    distinct := select.distinct
    lookupScanOrder
    distinctScanOrder := joinDistinctScanOrder context.leftSchema context.rightSchema
      mayExchange
      (on.any (joinHasRowidEquality context.leftSchema context.rightSchema) ||
        where_.any (joinHasRowidEquality context.leftSchema context.rightSchema))
      (orderBy.map (fun term => (term.reference, term.descending))) }

def joinAliasesNeeded (select : Select) (left right : Core.Schema) : Bool :=
  let hasColumn := fun name => (findColumn? left name).isSome || (findColumn? right name).isSome
  let needed := CoreOrder.needsAliasesWith hasColumn select.columns.toList
  select.sources.toList.any (fun source => source.joinOn.any needed) || select.where_.any needed

def joinQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query := do
  if joinAliasesNeeded select leftSchema rightSchema then unsupported "unresolved joined result alias"
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless leftSource.schema.isNone && leftSource.functionArgs.isNone && leftSource.subquerySql.isNone && rightSource.schema.isNone && rightSource.functionArgs.isNone && rightSource.subquerySql.isNone &&
      leftSource.joinOn.isNone && !rightSource.rightJoin do
    throw "unsupported general verified-MVP SQL: only two-table INNER/CROSS/comma/LEFT JOIN"
  unless select.groupBy.isEmpty && select.having.isNone do
    throw "unsupported general verified-MVP SQL: join SELECT shape"
  unless canonical leftSource.name = canonical leftTable &&
      canonical rightSource.name = canonical rightTable do
    throw "join source/schema mismatch"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  joinQueryBound select rightSource context

/-- LIMIT zero still resolves the original predicates and validates every
operation that SQLite would generate, but emits no predicate value evaluation.
Projection, ordering and source checks retain the ordinary join translator. -/
def joinZeroLayout (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query := do
  if joinAliasesNeeded select leftSchema rightSchema then unsupported "unresolved joined result alias"
  unless select.limit == some 0 do unsupported "zero-limit join requires LIMIT 0"
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  for expression in rightSource.joinOn.toList do
    let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
    unless joinStaticAdmitted context prepared rightSource.leftJoin do
      unsupported "unbound or invalid zero-limit join ON"
  for expression in select.where_.toList do
    let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
    unless joinStaticAdmitted context prepared do
      unsupported "unbound or invalid zero-limit join WHERE"
  joinQuery { select with sources := #[leftSource, { rightSource with joinOn := none }], where_ := none }
    leftTable rightTable leftSchema rightSchema

def joinZeroQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query :=
  (fun query => { query with limit := some 0 }) <$>
    joinZeroLayout select leftTable rightTable leftSchema rightSchema

theorem joinZeroQuery_limit (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (query : CoreJoin.Query)
    (success : joinZeroQuery select leftTable rightTable leftSchema rightSchema = .ok query) :
    query.limit = some 0 := by
  cases translated : joinZeroLayout select leftTable rightTable leftSchema rightSchema with
  | error message => simp [joinZeroQuery, translated, Functor.map, Except.map] at success
  | ok layout =>
      simp [joinZeroQuery, translated, Functor.map, Except.map] at success
      subst query
      rfl

def joinQueryWithZero (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query :=
  match joinQuery select leftTable rightTable leftSchema rightSchema with
  | .ok query => .ok query
  | .error message =>
      if select.limit == some 0 then joinZeroQuery select leftTable rightTable leftSchema rightSchema
      else .error message

theorem joinQueryWithZero_existing (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (query : CoreJoin.Query)
    (success : joinQuery select leftTable rightTable leftSchema rightSchema = .ok query) :
    joinQueryWithZero select leftTable rightTable leftSchema rightSchema = .ok query := by
  simp [joinQueryWithZero, success]

/-- An outer ON expression has no cursor to initialize when the left
input is empty. Resolution/code-generation checks still use the original ON;
WHERE and every other query component retain ordinary translation. -/
def joinEmptyOnQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query := do
  if select.where_.isSome then return ← unsupported "empty outer ON with WHERE requires cursor planning"
  if joinAliasesNeeded select leftSchema rightSchema then unsupported "unresolved joined result alias"
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless rightSource.leftJoin && (leftRows.isEmpty || rightRows.isEmpty) do
    unsupported "outer ON requires an empty input"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  if !leftRows.isEmpty && rightSource.joinOn.any (joinComputedCursorKey context) then
    unsupported "empty inner cursor still evaluates its search key"
  for expression in rightSource.joinOn.toList do
    let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
    unless joinStaticAdmitted context prepared true do
      unsupported "unbound or invalid empty-input outer ON"
  joinQueryWithZero { select with sources := #[leftSource, { rightSource with joinOn := none }] }
    leftTable rightTable leftSchema rightSchema

theorem joinEmptyOnQuery_where_failure (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (left right : List Core.Row)
    (present : select.where_.isSome = true) :
    (joinEmptyOnQuery select leftTable rightTable leftSchema rightSchema left right).isOk = false := by
  simp [joinEmptyOnQuery, present, unsupported, bind, Except.bind, Except.isOk]
  rfl

def joinQueryForRows (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query :=
  match joinQueryWithZero select leftTable rightTable leftSchema rightSchema with
  | .ok query => .ok query
  | .error message =>
      match joinEmptyOnQuery select leftTable rightTable leftSchema rightSchema leftRows rightRows with
      | .ok query => .ok query
      | .error _ => .error message

theorem joinQueryForRows_existing (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) (query : CoreJoin.Query)
    (success : joinQuery select leftTable rightTable leftSchema rightSchema = .ok query) :
    joinQueryForRows select leftTable rightTable leftSchema rightSchema leftRows rightRows = .ok query := by
  simp [joinQueryForRows, joinQueryWithZero, success]

/-- These leading wrappers preserve values. Their collation and CTAS affinity
metadata are read from the original expression separately. -/
def joinValueBaseFuel : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression => match expression with
    | .unary .plus argument | .collate argument _ => joinValueBaseFuel fuel argument
    | .call name arguments false => match SQLite.Probability.input? name arguments with
      | some argument => joinValueBaseFuel fuel argument
      | none => expression
    | _ => expression

def joinWrappedColumns (context : JoinContext) (columns : List ResultColumn) :
    Except String (List ResultColumn × List (Option String)) := do
  let parts ← columns.mapM fun column => do
    let bound := joinBindNames context column.expr
    let base := joinValueBaseFuel bound.height bound
    let references ← joinResultExpr context base
    let name := match bound with
      | .star _ => some "binary"
      | _ => SQLite.ExprCollation.effectiveName bound
    pure ({ column with expr := base }, List.replicate references.length name)
  return (parts.map Prod.fst, (parts.map Prod.snd).flatten)

/-- Top-level aliases/positions inherit their selected result's collation;
source expressions retain their own metadata. -/
def joinOrderOutputPosition? (columns : List (CoreJoin.Operand × Option String))
    (expression : Expr) : Option Nat :=
  let expression := SQLite.Scalar.prepare (CoreOrder.keyExpression expression)
  match (CoreOrder.bareName? expression).bind (fun name =>
      columns.findIdx? (fun output => output.2.any (fun alias => canonical alias == canonical name))) with
  | some position => some position
  | none => (CoreOrder.ordinal? expression).bind fun position =>
      if 1 ≤ position && position.toNat ≤ columns.length then some (position.toNat - 1) else none

def joinWrappedOrderReference (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (expression : Expr) :
    Except String (Option CoreJoin.ColumnRef) :=
  match joinOrderReference context columns expression with
  | .ok reference => .ok reference
  | .error message => do
      let key := SQLite.Scalar.prepare (CoreOrder.keyExpression expression)
      if (CoreOrder.ordinal? key).isSome then throw message
      let bound := joinBindNames context key
      let base := joinValueBaseFuel bound.height bound
      if base.any SQLite.StaticCondition.resolutionForbidden then throw message
      let reference ← joinOperand context base
      joinOrderOutputReference reference

def joinWrappedOrderBy (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (names : List (Option String))
    (terms : List OrderTerm) : Except String (List CoreJoin.OrderTerm) := do
  let terms ← terms.mapM fun term => do
    let selected := (joinOrderOutputPosition? columns term.expr).bind (fun position => names[position]?.getD none)
    let kind ← SQLite.ExprCollation.require (SQLite.ExprCollation.ofName
      ((SQLite.ExprCollation.name term.expr).orElse (fun _ => selected)))
    let reference ← joinWrappedOrderReference context columns term.expr
    pure (reference.map fun reference => ({
      reference := reference
      descending := term.descending
      nullsFirst := some (term.nullsFirst.getD (!term.descending))
      collation := kind } : CoreJoin.OrderTerm))
  return terms.filterMap id

/-- Normalize only value-preserving projection wrappers, then reuse the same
join predicates, source validation and row windows. Original output collations
control DISTINCT, alias/ordinal ordering and later compound metadata. -/
def joinWrappedQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query := do
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  let (columns, names) ← joinWrappedColumns context select.columns.toList
  let orderColumns ← joinOrderColumns context columns
  let orderBy ← joinWrappedOrderBy context orderColumns names select.orderBy.toList
  let kinds ← if select.distinct then names.mapM (fun name => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName name))
    else pure []
  let query ← joinQueryForRows { select with columns := columns.toArray, orderBy := #[] }
    leftTable rightTable leftSchema rightSchema leftRows rightRows
  let mayExchange := !rightSource.leftJoin && !rightSource.crossJoin
  return { query with
    orderBy
    distinctCollations := if kinds.all (· == .binary) then [] else kinds
    lookupScanOrder := joinLookupScanOrder leftSchema rightSchema mayExchange query.on query.where_ orderBy
    distinctScanOrder := joinDistinctScanOrder leftSchema rightSchema mayExchange
      (query.on.any (joinHasRowidEquality leftSchema rightSchema) ||
        query.where_.any (joinHasRowidEquality leftSchema rightSchema))
      (orderBy.map (fun term => (term.reference, term.descending))) }

def joinQueryComplete (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query :=
  match joinQueryForRows select leftTable rightTable leftSchema rightSchema leftRows rightRows with
  | .ok query => .ok query
  | .error message =>
      match joinWrappedQuery select leftTable rightTable leftSchema rightSchema leftRows rightRows with
      | .ok query => .ok query
      | .error _ => .error message

theorem joinQueryComplete_existing (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) (query : CoreJoin.Query)
    (success : joinQuery select leftTable rightTable leftSchema rightSchema = .ok query) :
    joinQueryComplete select leftTable rightTable leftSchema rightSchema leftRows rightRows = .ok query := by
  simp [joinQueryComplete, joinQueryForRows, joinQueryWithZero, success]

/-- The bound interpreter is also used by RIGHT shared-name queries, where
unqualified merged columns resolve to the right schema. Empty/zero-LIMIT
predicates retain the same preparation checks as the ordinary join path. -/
def joinRightBoundForRows (select : Select) (source : TableRef) (context : JoinContext)
    (leftRows rightRows : List Core.Row) : Except String CoreJoin.Query :=
  match joinQueryBound select source context with
  | .ok query => .ok query
  | .error message => do
      let zero := select.limit == some 0
      if !zero && select.where_.isSome then return ← throw message
      unless zero || leftRows.isEmpty || rightRows.isEmpty do throw message
      if !zero && source.joinOn.any (joinComputedCursorKey context) then throw message
      for expression in source.joinOn.toList do
        let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
        unless joinStaticAdmitted context prepared true do throw message
      if zero then
        for expression in select.where_.toList do
          let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
          unless joinStaticAdmitted context prepared do throw message
      match joinQueryBound { select with where_ := if zero then none else select.where_ }
          { source with joinOn := none } context with
      | .ok query => .ok query
      | .error _ => .error message

/-- WHERE may remove the outer side and expose early ON evaluation. A failed
translation with WHERE must reach the general planner, not erase ON merely
because a source is empty. LIMIT zero retains its independent admission path. -/
theorem joinRightBoundForRows_where_failure (select : Select) (source : TableRef)
    (context : JoinContext) (left right : List Core.Row) (message : String)
    (failed : joinQueryBound select source context = .error message)
    (nonzero : (select.limit == some 0) = false) (present : select.where_.isSome = true) :
    joinRightBoundForRows select source context left right = .error message := by
  simp [joinRightBoundForRows, failed, nonzero, present]
  rfl

/-- FULL merged output operands need their actual coalesced value for sorting.
The original source reference remains available for ordinary column terms. -/
def joinFullOrderValue (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (expression : Expr) :
    Except String (Option CoreJoin.Operand) := do
  let key := SQLite.Scalar.prepare (CoreOrder.keyExpression expression)
  if let some name := CoreOrder.bareName? key then
    if let some output := columns.find? (fun output => output.2.any (fun alias => canonical alias == canonical name)) then
      return some output.1
  if let some position := CoreOrder.ordinal? key then
    unless 1 ≤ position && position.toNat ≤ columns.length do
      throw "ORDER BY position is outside the result columns"
    let some output := columns[position.toNat - 1]? | throw "ORDER BY position is out of range"
    return some output.1
  if joinOrderConstant key then return none
  let bound := joinBindNames context key
  let base := joinValueBaseFuel bound.height bound
  if base.any SQLite.StaticCondition.resolutionForbidden then unsupported "FULL JOIN order resolution"
  let operand ← joinOperand context base
  return some operand

def joinFullOrderBy (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (names : List (Option String))
    (terms : List OrderTerm) : Except String (List CoreJoin.OrderTerm) := do
  let terms ← terms.mapM fun term => do
    let selected := (joinOrderOutputPosition? columns term.expr).bind (fun position => names[position]?.getD none)
    let kind ← SQLite.ExprCollation.require (SQLite.ExprCollation.ofName
      ((SQLite.ExprCollation.name term.expr).orElse (fun _ => selected)))
    let value ← joinFullOrderValue context columns term.expr
    match value with
    | none | some (.literal _) => pure none
    | some operand =>
        let reference ← match operand with
          | .column reference => pure reference
          | .mergedColumn none left _ => pure ⟨.left, left⟩
          | _ => unsupported "FULL JOIN coerced output ordering"
        pure (some ({
          reference
          descending := term.descending
          nullsFirst := some (term.nullsFirst.getD (!term.descending))
          collation := kind
          valueOperand := some operand } : CoreJoin.OrderTerm))
  return terms.filterMap id

def joinRightQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query := do
  if joinAliasesNeeded select leftSchema rightSchema then unsupported "unresolved joined result alias"
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless rightSource.rightJoin && leftSource.schema.isNone && leftSource.functionArgs.isNone && leftSource.subquerySql.isNone && rightSource.schema.isNone && rightSource.functionArgs.isNone && rightSource.subquerySql.isNone &&
      leftSource.joinOn.isNone && select.groupBy.isEmpty && select.having.isNone do
    unsupported "RIGHT/FULL join source shape"
  unless canonical leftSource.name = canonical leftTable && canonical rightSource.name = canonical rightTable do
    throw "join source/schema mismatch"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  let (columns, names) ← joinWrappedColumns context select.columns.toList
  let orderColumns ← joinOrderColumns context columns
  let orderBy ← if context.coalesceShared then joinFullOrderBy context orderColumns names select.orderBy.toList
    else joinWrappedOrderBy context orderColumns names select.orderBy.toList
  let kinds ← if select.distinct then names.mapM (fun name => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName name))
    else pure []
  let query ← joinRightBoundForRows { select with columns := columns.toArray, orderBy := #[] }
    rightSource context leftRows rightRows
  return { query with orderBy, distinctCollations := if kinds.all (· == .binary) then [] else kinds }

/-- Retry unresolved ON/WHERE aliases against the original result expressions.
The established interpreter gets first refusal; aliases never shadow a source
name, and an inserted result expression is not recursively treated as aliases. -/
def joinAliasQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query :=
  let translate := if select.sources[1]?.any (fun source => source.rightJoin) then joinRightQuery else joinQueryComplete
  match translate select leftTable rightTable leftSchema rightSchema leftRows rightRows with
  | .ok query => .ok query
  | .error message => do
      let (leftSource, rightSource) ← match select.sources.toList with
        | [left, right] => .ok (left, right)
        | _ => .error message
      let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
      let needs := CoreOrder.needsAliasesWith (joinHasColumn context) select.columns.toList
      unless rightSource.joinOn.any needs || select.where_.any needs do throw message
      let resolve := CoreOrder.resolveAliasesWith (joinHasColumn context) select.columns.toList
      let (on, deferred) := match rightSource.joinOn with
        | none => (none, none)
        | some expression => CoreOrder.resolveJoinOnAliases (joinHasColumn context) select.columns.toList expression
      let source := { rightSource with joinOn := on }
      let ordering := select.orderBy.map fun term =>
        { term with expr := CoreOrder.resolveOrderAliasesWith (joinHasColumn context) select.columns.toList term.expr }
      let resolved := { select with
        sources := #[leftSource, source]
        where_ := CoreOrder.combineAliasConditions (select.where_.map resolve) deferred
        orderBy := ordering
        columns := select.columns.map (fun column => { column with alias := none }) }
      translate resolved leftTable rightTable leftSchema rightSchema leftRows rightRows

theorem joinAliasQuery_existing (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) (query : CoreJoin.Query)
    (ordinary : select.sources[1]?.any (fun source => source.rightJoin) = false)
    (success : joinQueryComplete select leftTable rightTable leftSchema rightSchema leftRows rightRows = .ok query) :
    joinAliasQuery select leftTable rightTable leftSchema rightSchema leftRows rightRows = .ok query := by
  simp [joinAliasQuery, ordinary, success]

def rightJoinResult (state : Core.State) (select : Select)
    (leftSource rightSource : TableRef) : Except String (Core.Result × Nat) := do
  let leftTable := resolveTableName state leftSource.name
  let rightTable := resolveTableName state rightSource.name
  let some left := state.database.findTable? leftTable | throw s!"no such table: {leftSource.name}"
  let some right := state.database.findTable? rightTable | throw s!"no such table: {rightSource.name}"
  let query ← joinAliasQuery select leftTable rightTable left.schema right.schema left.rows right.rows
  let query := CoreOptimizerBridge.optimizeJoin leftTable rightTable query
  let rows := CoreOuterJoin.eval rightSource.leftJoin left.schema.columns.length query left.rows right.rows
  return ({ rows }, query.columns.length)

def executeRightJoin (state : Core.State) (select : Select)
    (leftSource rightSource : TableRef) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> rightJoinResult state select leftSource rightSource

theorem executeRightJoin_preserves_state {state : Core.State} {select : Select}
    {leftSource rightSource : TableRef} {execution : SelectExecution}
    (success : executeRightJoin state select leftSource rightSource = .ok execution) :
    execution.state = state := by
  unfold executeRightJoin at success
  cases result : rightJoinResult state select leftSource rightSource with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

def executeJoin (state : Core.State) (select : Select) :
    Except String SelectExecution := do
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  if rightSource.rightJoin then return ← executeRightJoin state select leftSource rightSource
  unless leftSource.schema.isNone && leftSource.functionArgs.isNone && leftSource.subquerySql.isNone && rightSource.schema.isNone && rightSource.functionArgs.isNone && rightSource.subquerySql.isNone &&
      leftSource.joinOn.isNone && !rightSource.rightJoin do
    throw "unsupported general verified-MVP SQL: only two-table INNER/CROSS/comma/LEFT JOIN"
  unless select.groupBy.isEmpty && select.having.isNone do
    throw "unsupported general verified-MVP SQL: join SELECT shape"
  let leftTable := resolveTableName state leftSource.name
  let rightTable := resolveTableName state rightSource.name
  let left ← match state.database.findTable? leftTable with
    | some table => .ok table
    | none => .error s!"no such table: {leftSource.name}"
  let right ← match state.database.findTable? rightTable with
    | some table => .ok table
    | none => .error s!"no such table: {rightSource.name}"
  let query ← joinAliasQuery select leftTable rightTable left.schema right.schema left.rows right.rows
  let query := CoreOptimizerBridge.optimizeJoin leftTable rightTable query
  let (next, result) ← Core.execute state (.join leftTable rightTable query)
  return ⟨next, result, query.columns.length⟩

/-- A SELECT without FROM has one implicit zero-column input row. Validate
all expressions before evaluating WHERE, LIMIT, and then the result row;
unselected expressions must not raise evaluation errors. -/
def scalarConstantRow (select : Select) : Except String (Option (List Core.Value)) := do
  unless select.sources.isEmpty && select.valueRows.isNone &&
      select.groupBy.isEmpty && select.having.isNone do
    unsupported "constant SELECT shape"
  for expression in select.columns.toList.map (·.expr) ++ select.where_.toList do
    if let some message := SQLite.Scalar.resolutionError (fun _ _ => false) expression then throw message
    let prepared := SQLite.Scalar.prepare expression
    if let some message := SQLite.Scalar.functionError prepared.height prepared then throw message
  unless select.columns.all (fun column => SQLite.Scalar.admitted column.expr) &&
      select.where_.all SQLite.Scalar.admitted do
    unsupported "constant SELECT expression"
  let ctx : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  if select.distinct then
    CoreExpr.validateDistinct (select.columns.toList.map (·.expr))
  -- SQLite validates aggregate calls in a source-free scalar ORDER BY but
  -- does not turn the scalar SELECT into an aggregate query or evaluate them.
  let _ ← CoreAggregateOrder.prepare ctx select.columns.toList select.orderBy.toList
  if select.limit == some 0 then return none
  if let some condition := select.where_ then
    unless ← SQLite.Scalar.testWhere condition do return none
  if select.offset > 0 then return none
  return some (← select.columns.toList.mapM (fun column => literal column.expr))

/-- A source-free aggregate consumes the SELECT's single implicit empty row,
unless WHERE rejects it. It still emits one aggregate row for empty input. -/
def constantRow (select : Select) : Except String (Option (List Core.Value)) := do
  let aliasContext : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  let select := { select with where_ := select.where_.map (CoreOrder.resolveAliases aliasContext select.columns.toList) }
  if !select.groupBy.isEmpty then
    unless select.sources.isEmpty && select.valueRows.isNone do unsupported "constant grouped SELECT shape"
    let ctx : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
    let (rows, _) ← CoreGrouped.run ctx select [[]]
    match rows with
    | [] => return none
    | [row] => return some row
    | _ => throw "source-free GROUP BY produced more than one group"
  unless select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) do
    return ← scalarConstantRow select
  unless select.sources.isEmpty && select.valueRows.isNone &&
      select.groupBy.isEmpty do
    unsupported "constant aggregate SELECT shape"
  let ctx : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  if select.distinct then
    CoreExpr.validateDistinct (select.columns.toList.map (fun c => ctx.bindNames c.expr))
  let prepared ← CoreAggregateHaving.prepare ctx select.columns.toList select.orderBy.toList select.having
  unless prepared.results.terms.all (fun term => term.argument.all SQLite.Scalar.admitted) &&
      select.where_.all SQLite.Scalar.admitted do
    unsupported "unbound constant aggregate expression"
  if select.limit == some 0 then return none
  let enabled ← match select.where_ with
    | none => pure true
    | some condition => SQLite.Scalar.testWhere condition
  let values ← prepared.results.accumulate ctx (if enabled then [[]] else [])
  unless ← prepared.matches ctx values [] do return none
  if select.offset > 0 then return none
  return some (← prepared.finish ctx values [])

def executeConstantSelect (state : Core.State) (select : Select) :
    Except String SelectExecution :=
  (fun row => { state, result := { rows := row.toList }, width := select.columns.size }) <$>
    constantRow select

theorem executeConstantSelect_preserves_state {state : Core.State} {select : Select}
    {execution : SelectExecution} (success : executeConstantSelect state select = .ok execution) :
    execution.state = state := by
  unfold executeConstantSelect at success
  cases row : constantRow select with
  | error message => simp [row, Functor.map, Except.map] at success
  | ok value =>
      simp [row, Functor.map, Except.map] at success
      cases success
      rfl

theorem executeConstantSelect_at_most_one_row {state : Core.State} {select : Select}
    {execution : SelectExecution} (success : executeConstantSelect state select = .ok execution) :
    execution.result.rows.length ≤ 1 := by
  unfold executeConstantSelect at success
  cases row : constantRow select with
  | error message => simp [row, Functor.map, Except.map] at success
  | ok value =>
      simp [row, Functor.map, Except.map] at success
      cases success
      cases value <;> simp

/-- A scalar read can fail after emitting a typed row prefix. Preparation
and sorting failures have no published prefix. -/
structure ScalarReadReport where
  result : Core.Result := {}
  width : Nat := 0
  error : Option String := none

def ScalarReadReport.toExcept (report : ScalarReadReport) : Except String (Core.Result × Nat) :=
  match report.error with
  | none => .ok (report.result, report.width)
  | some message => .error message

/-- Fallback for row-dependent WHERE expressions. Source rows still come from
Core.execute. A primary-key order determines scan direction; other orderings
sort surviving outputs. LIMIT is applied during an ordered scan or after a
sort, and all names are bound before either path can skip evaluation. -/
def filteredSelectReadPrepared (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String ScalarReadReport := do
  unless select.groupBy.isEmpty do unsupported "row-expression grouped WHERE"
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
  let expressions ← ctx.projection select.columns.toList
  if select.distinct then CoreExpr.validateDistinct expressions
  let _ ← select.where_.mapM ctx.validate
  let terms ← resolvedOrdering stored.schema source select
  let _ ← terms.mapM (CoreOrder.validateTerm ctx)
  let ordering := terms.head?.toList.flatMap fun term =>
    match ctx.bindNames (CoreOrder.keyExpression term.expr) with
    | .column qualifier name => (ctx.column? qualifier name).toList.map (·, term.descending)
    | _ => []
  if select.limit != some 0 then
    unless ← ctx.constantMatches select.where_ do return { width := expressions.length }
  let search ← if select.limit == some 0 then pure none
    else expressionSearch ctx stored select.where_
  let ctx := expressionSearchContext ctx search
  if select.limit != some 0 then
    unless ← expressionSearchReady ctx search select.where_ do return { width := expressions.length }
  let singleRow := search.any (fun predicate => match predicate with
    | .equal index _ => index == stored.schema.primaryKey
    | _ => false)
  let orderedScan := terms.isEmpty || singleRow ||
    (terms.head?.any (fun term => match ctx.bindNames (CoreOrder.keyExpression term.expr) with
      | .column qualifier name => ctx.column? qualifier name == some stored.schema.primaryKey
      | _ => false))
  let query : Core.Query := {
    columns := List.range stored.schema.columns.length
    predicate := search
    orderBy := if orderedScan then ordering else [] }
  let (_, result) ← Core.execute state (.query (resolveTableName state source.name) query)
  let projected ← if orderedScan then
      pure (ctx.scanWindowObserved select.where_ expressions select.distinct result.rows select.offset select.limit [])
    else do
      let rows ← CoreOrder.scan ctx select.where_ expressions terms select.distinct result.rows select.offset select.limit
      pure ({ rows } : CoreExpr.ScanReport)
  return {
    result := { result with rows := projected.rows.map (·.output) }
    width := expressions.length
    error := projected.error }


def filteredSelectReadReport (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : ScalarReadReport :=
  match filteredSelectReadPrepared state select source stored with
  | .ok report => report
  | .error message => { error := some message }

def filteredSelectResult (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String (Core.Result × Nat) :=
  (filteredSelectReadReport state select source stored).toExcept


def executeFilteredSelect (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> filteredSelectResult state select source stored

theorem executeFilteredSelect_preserves_state {state : Core.State} {select : Select}
    {source : TableRef} {stored : Core.Table} {execution : SelectExecution}
    (success : executeFilteredSelect state select source stored = .ok execution) :
    execution.state = state := by
  unfold executeFilteredSelect at success
  cases result : filteredSelectResult state select source stored with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

/-- Direct Core queries sort before projection. When DISTINCT is ordered by
an unprojected source column, source representatives must be retained before
sorting; route those queries through the expression scan instead. -/
def queryNeedsRepresentatives (distinct : Bool) (columns : List Nat)
    (ordering : List (Nat × Bool)) : Bool :=
  distinct && !(ordering.all fun term => columns.contains term.1)

/-- Aggregate arguments bind before empty-input/LIMIT shortcuts. WHERE and
aggregate steps interleave over Core rows before the result is finalized. -/
def aggregateSelectResult (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String (Core.Result × Nat) := do
  unless select.groupBy.isEmpty do
    unsupported "aggregate grouping"
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
  let select := { select with where_ := select.where_.map (CoreOrder.resolveAliases ctx select.columns.toList) }
  if select.distinct then
    CoreExpr.validateDistinct (select.columns.toList.map (fun c => ctx.bindNames c.expr))
  let prepared ← CoreAggregateHaving.prepare ctx select.columns.toList select.orderBy.toList select.having
  let _ ← select.where_.mapM ctx.validate
  if select.limit == some 0 then return ({}, prepared.results.expressions.length)
  let enabled ← ctx.constantMatches select.where_
  let search ← if enabled then expressionSearch ctx stored select.where_ else pure none
  let ctx := expressionSearchContext ctx search
  let enabled ← if enabled then expressionSearchReady ctx search select.where_ else pure false
  let rows ← if !enabled then pure [] else do
    let (_, result) ← Core.execute state (.query (resolveTableName state source.name)
      { columns := List.range stored.schema.columns.length, predicate := search })
    pure result.rows
  let (values, inputs) ← prepared.results.accumulateSelected ctx select.where_ rows
  let values := values.val
  let representative ← CoreAggregateHaving.representative ctx prepared.results.terms inputs
  let selected ← prepared.matches ctx values representative
  let rows ← if !selected || select.offset > 0 then pure []
    else do pure [← prepared.finish ctx values representative]
  return ({ rows }, prepared.results.expressions.length)

def executeAggregateSelect (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> aggregateSelectResult state select source stored

theorem executeAggregateSelect_preserves_state {state : Core.State} {select : Select}
    {source : TableRef} {stored : Core.Table} {execution : SelectExecution}
    (success : executeAggregateSelect state select source stored = .ok execution) :
    execution.state = state := by
  unfold executeAggregateSelect at success
  cases result : aggregateSelectResult state select source stored with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

/-- The ordinary grouped Core path remains authoritative for its BINARY
column shape. This path adds explicit collation metadata to the same outputs. -/
def collatedGroupResult (select : Select) (source : TableRef) (stored : Core.Table) :
    Except String (Core.Result × Nat) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
  let (rows, width) ← CoreGrouped.run ctx select (stored.rows.map (·.values))
  return ({ rows }, width)

def executeCollatedGroup (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> collatedGroupResult select source stored

theorem executeCollatedGroup_preserves_state {state : Core.State} {select : Select}
    {source : TableRef} {stored : Core.Table} {execution : SelectExecution}
    (success : executeCollatedGroup state select source stored = .ok execution) :
    execution.state = state := by
  unfold executeCollatedGroup at success
  cases result : collatedGroupResult select source stored with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

/-- Scalar and aggregate projections share bound Core source rows. A recognized
aggregate anywhere in a result expression selects the aggregate evaluator;
aggregate arguments and scalar output templates bind before evaluation. -/
def executeExpressionSelect (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) (_wherePredicate : Option Core.Predicate) :
    Except String SelectExecution :=
  if !select.groupBy.isEmpty then executeCollatedGroup state select source stored
  else if select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) then
    executeAggregateSelect state select source stored
  else executeFilteredSelect state select source stored

/-- Direct Core commands require source-bound names without pending result-alias
substitution. Expression routes resolve WHERE aliases before scalar validation;
page-directed reads must decline the same unresolved alias shape. -/
def selectNamesBound (schema : Core.Schema) (source : TableRef) (select : Select) : Bool :=
  let ctx : CoreExpr.Context := { schema, sourceName := source.alias.getD source.name }
  !(select.where_.any (CoreOrder.needsAliases ctx select.columns.toList)) &&
    select.columns.all (fun result => ctx.namesBound result.expr) &&
    select.where_.all ctx.namesBound && select.groupBy.all ctx.namesBound &&
    select.having.all ctx.namesBound &&
    ((resolvedOrdering schema source select).toOption.any (fun terms => terms.all (fun term => ctx.namesBound term.expr)))

/-- Preserve a concrete resolver diagnostic when the optimized name-bound
route declines a SELECT. Alias rewriting remains in the ordinary SQL planner. -/
def selectResolutionError (schema : Core.Schema) (source : TableRef) (select : Select) : Option String :=
  let ctx : CoreExpr.Context := { schema, sourceName := source.alias.getD source.name }
  let ordering := ((resolvedOrdering schema source select).toOption.getD []).map (·.expr)
  let expressions := select.columns.toList.map (·.expr) ++ select.where_.toList ++
    select.groupBy.toList ++ select.having.toList ++ ordering
  (expressions.findSome? (SQLite.Scalar.resolutionError (fun q n => (ctx.column? q n).isSome))).orElse fun _ =>
    match resolvedOrdering schema source select with
    | .error message => some message
    | .ok _ => none

@[simp] theorem selectNamesBound_compounds (schema : Core.Schema) (source : TableRef)
    (select : Select) (compounds : Array (CompoundOp × Select)) :
    selectNamesBound schema source { select with compounds } =
      selectNamesBound schema source select := rfl

/-- Writes bind names before deciding whether a predicate/assignment is a
constant Core command or needs row-expression evaluation. -/
def writeNamesBound (schema : Core.Schema) (table : String) (alias : Option String)
    (assignments : Array (String × Expr)) (condition : Option Expr) : Bool :=
  let ctx : CoreExpr.Context := { schema, sourceName := alias.getD table }
  assignments.all (fun assignment => ctx.namesBound assignment.2) && condition.all ctx.namesBound

/-- A VALUES coroutine computes each yielded row before its parent applies
OFFSET. Its initial affinity-bearing direct SELECT rows and a one-row VALUES
core retain scalar SELECT's skip rule. LIMIT bounds the coroutine's yields. -/
def valuesResult (select : Select) : Except String (Core.Result × Nat) := do
  let some rows := select.valueRows | unsupported "VALUES rows"
  let some first := rows[0]? | throw "VALUES requires at least one row"
  unless !first.isEmpty && first.size ≤ SQLite.Limits.maxColumns do
    throw "invalid VALUES column count"
  unless select.sources.isEmpty && select.where_.isNone && select.groupBy.isEmpty &&
      select.having.isNone && select.orderBy.isEmpty && !select.distinct do
    unsupported "VALUES shape"
  for row in rows do
    unless row.size == first.size do throw "all VALUES must have the same number of terms"
  if rows.size == 1 then
    let row ← constantRow { select with valueRows := none }
    return ({ rows := row.toList }, first.size)
  for row in rows do
    unless row.all SQLite.Scalar.admitted do unsupported "VALUES expression"
  if select.limit == some 0 then return ({}, first.size)
  let selected := match select.limit with
    | none => rows.toList
    | some count => rows.toList.take (count + select.offset)
  let skipped := min select.offset (SQLite.Values.directCount rows.toList)
  let values ← (selected.drop skipped).mapM (fun row => row.toList.mapM literal)
  return ({ rows := values.drop (select.offset - skipped) }, first.size)

def executeValues (state : Core.State) (select : Select) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> valuesResult select

theorem executeValues_preserves_state {state : Core.State} {select : Select}
    {execution : SelectExecution} (success : executeValues state select = .ok execution) :
    execution.state = state := by
  unfold executeValues at success
  cases result : valuesResult select with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

def executeSelectBase (state : Core.State) (select : Select) :
    Except String SelectExecution :=
  if select.sources.size = 2 then executeJoin state select
  else if select.sources.isEmpty then
    if select.valueRows.isSome then executeValues state select
    else executeConstantSelect state select
  else do
    unless select.sources.size = 1 do
      throw "unsupported general verified-MVP SQL: SELECT shape"
    let source ← match select.sources[0]? with
      | some source => .ok source
      | none => .error "SELECT has no source table"
    unless source.schema.isNone && source.functionArgs.isNone && source.subquerySql.isNone && source.joinOn.isNone do
      throw "unsupported general verified-MVP SQL: SELECT source"
    let tableName := resolveTableName state source.name
    let stored ← match state.database.findTable? tableName with
      | some stored => .ok stored
      | none => .error s!"no such table: {source.name}"
    if select.having.isSome then
      if !select.groupBy.isEmpty then return ← executeCollatedGroup state select source stored
      unless select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) do
        unsupported "HAVING requires a supported aggregate query"
      return ← executeAggregateSelect state select source stored
    unless selectNamesBound stored.schema source select do
      if !select.groupBy.isEmpty then return ← executeCollatedGroup state select source stored
      let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
      if select.where_.any (CoreOrder.needsAliases ctx select.columns.toList) then
        unless selectNamesBound stored.schema source { select with where_ := none } do
          if let some message := selectResolutionError stored.schema source { select with where_ := none } then throw message
          unsupported "unbound SELECT result or ordering name"
        let resolved := { select with where_ := select.where_.map (CoreOrder.resolveAliases ctx select.columns.toList) }
        return ← executeExpressionSelect state resolved source stored none
      if let some message := selectResolutionError stored.schema source select then throw message
      unsupported "unbound SELECT name"
    match select.where_.mapM (predicate stored.schema) with
    | .error _ => executeExpressionSelect state select source stored none
    | .ok wherePredicate => do
      if !select.groupBy.isEmpty then
        if select.distinct || !select.orderBy.isEmpty || select.limit.isSome || select.offset != 0 then
          executeCollatedGroup state select source stored
        else
          match groupColumns stored.schema select.groupBy.toList with
          | .error _ => executeCollatedGroup state select source stored
          | .ok groups =>
              match groupOutputs stored.schema groups select.columns.toList with
              | .error _ => executeCollatedGroup state select source stored
              | .ok outputs => do
                  let query : Core.GroupQuery := { groupBy := groups, outputs, predicate := wherePredicate }
                  let (next, result) ← Core.execute state (.group tableName query)
                  return ⟨next, result, query.outputs.length⟩
      else
        match ← countTarget? stored.schema select.columns.toList,
            ← sumColumn? stored.schema select.columns.toList,
            ← extremeColumn? stored.schema select.columns.toList with
        | some target, none, none =>
          if select.distinct || !select.orderBy.isEmpty || select.limit.isSome || select.offset != 0 then
            executeAggregateSelect state select source stored
          else
            let (next, result) ← Core.execute state (.count tableName target wherePredicate)
            return ⟨next, result, 1⟩
        | none, some column, none =>
          if select.distinct || !select.orderBy.isEmpty || select.limit.isSome || select.offset != 0 then
            executeAggregateSelect state select source stored
          else
            let (next, result) ← Core.execute state (.sum tableName column wherePredicate)
            return ⟨next, result, 1⟩
        | none, none, some (minimum, column) =>
          if select.distinct || !select.orderBy.isEmpty || select.limit.isSome || select.offset != 0 then
            executeAggregateSelect state select source stored
          else
            let (next, result) ← Core.execute state
              (.extreme tableName minimum column wherePredicate)
            return ⟨next, result, 1⟩
        | none, none, none =>
          match projection stored.schema select.columns.toList with
          | .error _ => executeExpressionSelect state select source stored wherePredicate
          | .ok columns =>
            match directOrdering stored.schema source select with
            | .error _ => executeFilteredSelect state select source stored
            | .ok ordering => do
              if select.offset != 0 || queryNeedsRepresentatives select.distinct columns ordering then
                executeFilteredSelect state select source stored
              else
                let query : Core.Query := {
                  columns
                  predicate := wherePredicate
                  orderBy := ordering
                  limit := select.limit
                  distinct := select.distinct }
                let (next, result) ← Core.execute state (.query tableName query)
                return ⟨next, result, query.columns.length⟩
        | _, _, _ => unsupported "ambiguous aggregate projection"

/-- Recognize the non-aggregate single-table SELECT shape used by the
persisted-index adapter. Returning `none` is only an optimization miss: normal
Core execution remains authoritative for every statement. -/
def simpleQuery? (state : Core.State) (select : Select) :
    Option (String × Core.Query) := do
  if select.compounds.isEmpty && select.sources.size = 1 &&
      select.groupBy.isEmpty && select.having.isNone && select.offset = 0 then
    let source ← select.sources[0]?
    if source.schema.isNone && source.functionArgs.isNone && source.subquerySql.isNone && source.joinOn.isNone then
      let tableName := resolveTableName state source.name
      let stored ← state.database.findTable? tableName
      unless selectNamesBound stored.schema source select do none
      let wherePredicate ← (select.where_.mapM (predicate stored.schema)).toOption
      let count ← (countTarget? stored.schema select.columns.toList).toOption
      let sum ← (sumColumn? stored.schema select.columns.toList).toOption
      let extreme ← (extremeColumn? stored.schema select.columns.toList).toOption
      if count.isNone && sum.isNone && extreme.isNone then
        let columns ← (projection stored.schema select.columns.toList).toOption
        let ordering ← (directOrdering stored.schema source select).toOption
        if queryNeedsRepresentatives select.distinct columns ordering then none
        else some (tableName, {
          columns
          predicate := wherePredicate
          orderBy := ordering
          limit := select.limit
          distinct := select.distinct })
      else none
    else none
  else none

/-- Explicit result collations are the only reason the currently supported
BINARY schemas need a different compound comparator. Predicate collations do
not affect the result-column collation. -/
def resultCollationFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, select =>
      select.columns.any (fun column => (SQLite.ExprCollation.name column.expr).isSome) ||
        (select.sources.isEmpty && select.valueRows.any (fun rows => rows.any (fun row =>
          row.any (fun expression => (SQLite.ExprCollation.name expression).isSome)))) ||
        select.compounds.any (fun arm => resultCollationFuel fuel arm.2)

def requiresCompoundCollation (select : Select) : Bool :=
  !select.compounds.isEmpty && resultCollationFuel select.compoundHeight select

/-- These expression identities are internal bound slots, not SQL names.
FULL's merged column is distinct from either source and from an explicit
coalesce() call, as in SQLite's expression comparison. -/
def joinCompoundOperand : CoreJoin.Operand → Expr
  | .column reference | .coercedColumn _ reference =>
      .column (some (if reference.side == .left then "left" else "right")) (toString reference.column)
  | .mergedColumn _ left right => .column (some "merged") s!"{left}:{right}"
  | .literal value => .literal (match value with
      | .null => .null
      | .integer i => .integer i.value
      | .realBits bits => .real (Float.ofBits (UInt64.ofNat bits.val))
      | .blob payload => .blob payload.bytes.toArray
      | .text payload => match String.fromUTF8? (ByteArray.mk payload.bytes.toArray) with
          | some text => .text text
          | none => .textBytes payload.bytes.toArray)

theorem joinCompoundOperand_sides (left right : Nat) :
    joinCompoundOperand (.column ⟨.left, left⟩) ≠
      joinCompoundOperand (.column ⟨.right, right⟩) := by
  simp [joinCompoundOperand]

theorem joinCompoundOperand_merged (left right index : Nat) :
    joinCompoundOperand (.mergedColumn none left right) ≠
      joinCompoundOperand (.column ⟨.left, index⟩) := by
  simp [joinCompoundOperand]

/-- Bind every reference before comparing ASTs. Unknown and ambiguous source
names fail; qualifiers cannot accidentally name an internal result slot. -/
def joinCompoundBindFuel (context : JoinContext) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, expression => do
      let bind := joinCompoundBindFuel context fuel
      match expression with
      | .column qualifier name =>
          match joinNamedOperand context qualifier name with
          | .ok operand => some (joinCompoundOperand operand)
          | .error _ => none
      | .literal .. => some expression
      | .unary op arg => return .unary op (← bind arg)
      | .binary op left right => return .binary op (← bind left) (← bind right)
      | .call name args star => return .call name (← args.mapM bind) star
      | .isNull arg negated => return .isNull (← bind arg) negated
      | .inList arg values negated affinity =>
          return .inList (← bind arg) (← values.mapM bind) negated affinity
      | .collate arg name => return .collate (← bind arg) name
      | .case_ base branches otherwise =>
          return .case_ (← base.mapM bind)
            (← branches.mapM fun (condition, result) => do return (← bind condition, ← bind result))
            (← otherwise.mapM bind)
      | _ => none

def joinCompoundBind (context : JoinContext) (expression : Expr) : Option Expr :=
  let expression := SQLite.Scalar.prepare (joinBindNames context expression)
  joinCompoundBindFuel context expression.height expression

def joinCompoundStarReferences (context : JoinContext) (qualifier : Option String) :
    Except String (List CoreJoin.ColumnRef) :=
  match qualifier with
  | none => .ok (joinVisibleColumns .left context.leftSchema ++
      (joinVisibleColumns .right context.rightSchema).filter
        (fun reference => !CoreJoinUsing.suppressesRight context.shared reference.column))
  | some qualifier =>
      if canonical qualifier == context.leftName then
        .ok (joinVisibleColumns .left context.leftSchema)
      else if canonical qualifier == context.rightName then
        .ok (joinVisibleColumns .right context.rightSchema)
      else .error s!"no such table or alias: {qualifier}"

def joinCompoundStarColumns (context : JoinContext) (qualifier : Option String) :
    Except String (List ResultColumn) := do
  let references ← joinCompoundStarReferences context qualifier
  return references.map fun reference =>
    let schema := if reference.side == .left then context.leftSchema else context.rightSchema
    { expr := joinCompoundOperand (joinStarOperand context reference)
      alias := (schema.columns[reference.column]?).map (·.name) }

/-- Every expanded star has exactly the live join projection's bound values,
in the same positions; output labels do not change these identities. -/
theorem joinCompoundStarColumns_projection (context : JoinContext) (qualifier : Option String) :
    (joinCompoundStarColumns context qualifier).map (List.map (·.expr)) =
      (joinResultExpr context (.star qualifier)).map (List.map joinCompoundOperand) := by
  cases qualifier with
  | none => simp [joinCompoundStarColumns, joinCompoundStarReferences, joinResultExpr,
      bind, Except.bind, Except.map, pure, Except.pure, List.map_map, Function.comp_def]
  | some qualifier =>
      by_cases left : canonical qualifier == context.leftName
      · simp [joinCompoundStarColumns, joinCompoundStarReferences, joinResultExpr, left,
          bind, Except.bind, Except.map, pure, Except.pure, List.map_map, Function.comp_def]
      · by_cases right : canonical qualifier == context.rightName
        · simp [joinCompoundStarColumns, joinCompoundStarReferences, joinResultExpr, left, right,
            bind, Except.bind, Except.map, pure, Except.pure, List.map_map, Function.comp_def,
            joinVisibleColumns, joinStarOperand, joinMergedStar]
        · simp [joinCompoundStarColumns, joinCompoundStarReferences, joinResultExpr, left, right,
            bind, Except.bind, Except.map]

def joinCompoundColumns (context : JoinContext) : List ResultColumn → Except String (List ResultColumn)
  | [] => .ok []
  | column :: columns => do
      let head ← match column.expr with
        | .star qualifier => joinCompoundStarColumns context qualifier
        | expression => do
            let some bound := joinCompoundBind context expression
              | throw "unbound joined result expression"
            pure [{ column with expr := bound }]
      return head ++ (← joinCompoundColumns context columns)


def joinScalarInputs (context : JoinContext) : List CoreJoin.Operand :=
  (joinSideColumns .left context.leftSchema.columns.length ++
    joinSideColumns .right context.rightSchema.columns.length).map .column ++
  context.shared.map (fun shared => .mergedColumn none shared.left shared.right)

def joinScalarSlot (index : Nat) : Expr := .column none s!"__joined_{index}"

def joinScalarOperand (context : JoinContext) (operand : CoreJoin.Operand) : Option Expr :=
  (joinScalarInputs context).findIdx? (· == operand) |>.map joinScalarSlot

def joinScalarBindFuel (context : JoinContext) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, expression => do
      let bind := joinScalarBindFuel context fuel
      match expression with
      | .column qualifier name =>
          joinScalarOperand context (← (joinNamedOperand context qualifier name).toOption)
      | .literal .. => some expression
      | .unary op arg => return .unary op (← bind arg)
      | .binary op left right => return .binary op (← bind left) (← bind right)
      | .call name args star => return .call name (← args.mapM bind) star
      | .isNull arg negated => return .isNull (← bind arg) negated
      | .inList arg values negated affinity =>
          return .inList (← bind arg) (← values.mapM bind) negated affinity
      | .collate arg name => return .collate (← bind arg) name
      | .case_ base branches otherwise =>
          return .case_ (← base.mapM bind)
            (← branches.mapM fun (condition, result) => do return (← bind condition, ← bind result))
            (← otherwise.mapM bind)
      | _ => none

def joinScalarBind (context : JoinContext) (expression : Expr) : Except String Expr := do
  let expression := SQLite.Scalar.prepare (joinBindNames context expression)
  let some result := joinScalarBindFuel context expression.height expression
    | throw "unbound or unsupported joined expression"
  return result

/-- The expression context has no stored table or newly allocated rowids.
Every input value is a bound source operand with its original affinity. -/
def joinScalarContext (context : JoinContext) : Except String CoreExpr.Context := do
  let columns ← (joinScalarInputs context).mapIdxM fun index operand => do
    let source ← match operand with
      | .column reference => joinColumnDefinition context reference
      | .mergedColumn _ left _ => joinColumnDefinition context ⟨.left, left⟩
      | _ => throw "invalid joined expression input"
    return ({ name := s!"__joined_{index}", declaredType := CoreCreateTableAs.declaredType source.affinity } : Core.Column)
  return { schema := { name := "__joined", columns, primaryKey := columns.length }, sourceName := "__joined" }

def joinScalarResults (context : JoinContext) : List ResultColumn → Except String (List ResultColumn)
  | [] => .ok []
  | column :: columns => do
      let head ← match column.expr with
        | .star qualifier => do
            let references ← joinCompoundStarReferences context qualifier
            references.mapM fun reference => do
              let some expr := joinScalarOperand context (joinStarOperand context reference)
                | throw "invalid joined star input"
              let definition ← joinColumnDefinition context reference
              return ({ expr, alias := some definition.name } : ResultColumn)
        | expression => do
            let bound ← joinScalarBind context expression
            pure [{ column with expr := bound }]
      return head ++ (← joinScalarResults context columns)

def joinScalarOrderExpression (context : JoinContext) (original expanded : List ResultColumn) :
    Expr → Except String Expr
  | .collate expression name => return .collate (← joinScalarOrderExpression context original expanded expression) name
  | expression => do
      if let some result := (CoreOrder.bareName? expression).bind (CoreOrder.aliasExpression? expanded) then
        return result
      joinScalarBind context (CoreOrder.resolveAliasesWith (joinHasColumn context) original expression)

structure JoinScalarPrepared where
  context : CoreExpr.Context
  select : Select
  on : Option CoreJoin.Predicate
  onExpression : Option Expr := none
  nullableRight : Bool := false
  nullableLeft : Bool := false

def joinScalarPrepare (context : JoinContext) (select : Select) (rightSource : TableRef) :
    Except String JoinScalarPrepared := do
  let ctx ← joinScalarContext context
  let columns ← joinScalarResults context select.columns.toList
  unless !columns.isEmpty && columns.length ≤ SQLite.Limits.maxColumns do
    throw "invalid SELECT result column count"
  let resolve := CoreOrder.resolveAliasesWith (joinHasColumn context) select.columns.toList
  let (on, deferred) := match rightSource.joinOn with
    | none => (none, none)
    | some expression => CoreOrder.resolveJoinOnAliases (joinHasColumn context) select.columns.toList expression
  let (on, onExpression) ← match on with
    | none => pure (none, none)
    | some expression => match joinPredicate context expression (rightSource.leftJoin || rightSource.rightJoin) with
      | .ok predicate => pure (some predicate, none)
      | .error _ => do
          let bound ← joinScalarBind context expression
          unless joinStaticAdmitted context (SQLite.Scalar.prepare (joinBindNames context expression))
              (rightSource.leftJoin || rightSource.rightJoin) do
            throw "unbound or invalid joined ON expression"
          pure (none, some bound)
  let shared ← joinUsingPredicate context
  let on := match on, shared with
    | none, other | other, none => other
    | some left, some right => some (.and left right)
  let where_ ← (CoreOrder.combineAliasConditions (select.where_.map resolve) deferred).mapM (joinScalarBind context)
  let order ← select.orderBy.mapM fun term => do
    return { term with expr := ← joinScalarOrderExpression context select.columns.toList columns term.expr }
  let groups ← select.groupBy.mapM (fun expression => joinScalarBind context (resolve expression))
  let having ← select.having.mapM (fun expression => joinScalarBind context (resolve expression))
  return {
    context := ctx
    on := on
    onExpression := onExpression
    nullableRight := rightSource.leftJoin
    nullableLeft := rightSource.rightJoin
    select := { select with
      columns := (columns.map (fun column => { column with alias := none })).toArray
      sources := #[]
      where_, orderBy := order, groupBy := groups, having } }

def joinScalarRows (context : JoinContext) (source : TableRef) (on : Option CoreJoin.Predicate)
    (left right : List Core.Row) : List CoreJoin.JoinedRow :=
  if source.rightJoin then
    CoreOuterJoin.joinedRows source.leftJoin context.leftSchema.columns.length context.rightSchema.columns.length on left right
  else if source.leftJoin then CoreJoin.leftOuterRows on context.rightSchema.columns.length left right
  else CoreJoin.matchingRows on none (CoreJoin.crossRows left right)

def joinScalarMatches (context : JoinContext) (prepared : JoinScalarPrepared) (outer : Bool)
    (row : CoreJoin.JoinedRow) : Except String Bool := do
  unless CoreJoin.selects prepared.on row do return false
  let some expression := prepared.onExpression | return true
  let input := CoreJoin.projectRow (joinScalarInputs context) row
  if !outer then return ← prepared.context.matches input (some expression)
  let decision := SQLite.StaticCondition.conditionDecision (SQLite.Scalar.conditionTerms expression)
  decision.testWith (fun atom wanted =>
    SQLite.Scalar.testEvaluatedFuel (prepared.context.eval input)
      prepared.context.affinity false atom.height wanted atom) true

/-- Match bookkeeping is completed before WHERE filtering. Dynamic ON values
are evaluated once for each visited pair and can return an expression error. -/
def joinScalarRowsM (context : JoinContext) (prepared : JoinScalarPrepared) (source : TableRef)
    (left right : List Core.Row) (exchanged : Bool := false) : Except String (List CoreJoin.JoinedRow) := do
  if exchanged && !source.leftJoin && !source.rightJoin then
    return ← (right.flatMap (fun r => left.map (fun l => (l, r)))).filterM
      (joinScalarMatches context prepared false)
  if prepared.onExpression.isNone then return joinScalarRows context source prepared.on left right
  let (initial, matched) ← left.foldlM (fun (prior, matched) l => do
    let found ← right.zipIdx.filterM (fun (r, _) => joinScalarMatches context prepared
      (source.leftJoin || source.rightJoin) (l, r))
    let output := if found.isEmpty && source.leftJoin then
        [(l, CoreJoin.nullRow context.rightSchema.columns.length)]
      else found.map (fun (r, _) => (l, r))
    pure (prior ++ output, matched ++ found.map Prod.snd)) ([], [])
  let remaining := if source.rightJoin then
      (right.zipIdx.filter (fun (_, index) => !matched.contains index)).map
        (fun (r, _) => (CoreJoin.nullRow context.leftSchema.columns.length, r))
    else []
  return initial ++ remaining

def joinScalarAggregate (ctx : CoreExpr.Context) (select : Select) (rows : List (List Core.Value)) :
    Except String (Core.Result × Nat) := do
  if select.distinct then CoreExpr.validateDistinct (select.columns.toList.map (·.expr))
  let prepared ← CoreAggregateHaving.prepare ctx select.columns.toList select.orderBy.toList select.having
  let _ ← select.where_.mapM ctx.validate
  if select.limit == some 0 then return ({}, prepared.results.expressions.length)
  let enabled ← ctx.constantMatches select.where_
  let (values, inputs) ← prepared.results.accumulateSelected ctx select.where_
    (if enabled then rows else [])
  let values := values.val
  let representative ← CoreAggregateHaving.representative ctx prepared.results.terms inputs
  let selected ← prepared.matches ctx values representative
  let output ← if !selected || select.offset > 0 then pure []
    else do pure [← prepared.finish ctx values representative]
  return ({ rows := output }, prepared.results.expressions.length)

def joinScalarRun (context : JoinContext) (prepared : JoinScalarPrepared)
    (rows : List CoreJoin.JoinedRow) (orderedInput : Bool := false) : Except String (Core.Result × Nat) := do
  let ctx := prepared.context
  let select := prepared.select
  let inputs := rows.map (CoreJoin.projectRow (joinScalarInputs context))
  if !select.groupBy.isEmpty then
    let (rows, width) ← CoreGrouped.run ctx select inputs
    return ({ rows }, width)
  if select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) then
    return ← joinScalarAggregate ctx select inputs
  unless select.having.isNone do unsupported "HAVING requires an aggregate"
  let expressions ← ctx.projection select.columns.toList
  if select.distinct then CoreExpr.validateDistinct expressions
  let _ ← select.where_.mapM ctx.validate
  let terms ← CoreOrder.resolve ctx select.columns.toList select.orderBy.toList
  let _ ← terms.mapM (CoreOrder.validateTerm ctx)
  if select.limit == some 0 then return ({}, expressions.length)
  unless ← ctx.constantMatches select.where_ do return ({}, expressions.length)
  let projected ← if terms.isEmpty || orderedInput then
      ctx.scanWindow select.where_ expressions select.distinct inputs select.offset select.limit []
    else CoreOrder.scan ctx select.where_ expressions terms select.distinct inputs select.offset select.limit
  return ({ rows := projected.map (·.output) }, expressions.length)

def joinScalarReference (context : JoinContext) (prepared : JoinScalarPrepared)
    (expression : Expr) : Option CoreJoin.ColumnRef := do
  let .column qualifier name := SQLite.ExprCollation.strip expression | none
  let index ← prepared.context.column? qualifier name
  let .column reference ← (joinScalarInputs context)[index]? | none
  return reference

def joinScalarOnlySide (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (expression : Expr) : Bool :=
  !expression.any (fun expression => match expression with
    | .column .. => !(joinScalarReference context prepared expression).any (fun ref => ref.side == side)
    | _ => false)

/-- Conservative counterpart of expr.c:impliesNotNullRow. Ordinary functions,
IS, CASE and nested null tests do not establish a non-null source row. -/
def joinScalarNullWalk (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      let walk := joinScalarNullWalk context prepared side fuel
      match expression with
      | .column .. => (joinScalarReference context prepared expression).any (fun ref => ref.side == side)
      | .collate arg _ | .unary _ arg => walk arg
      | .binary .and left right | .binary .or left right => walk left && walk right
      | .binary op left right =>
          ![.is, .isNot, .like, .glob, .match, .arrow, .arrowText].contains op && (walk left || walk right)
      | .inList arg values _ _ => !values.isEmpty && walk arg
      | .call "__sqlean_between" arguments false =>
          match arguments.toList with
          | [argument, lower, upper] => walk argument || (walk lower && walk upper)
          | _ => false
      | .call name args _ =>
          (SQLite.Scalar.scalarFunctionName name).startsWith "cast_" && args.size == 1 &&
            args.toList.any walk
      | _ => false

/-- expr.c:sqlite3ExprImpliesNonNullRow peels a root NOT NULL test, then
recursively visits the left arms of an AND chain. Its final right arm uses the
ordinary walker, which prunes nested null tests. Preserve that preparation order. -/
def joinScalarNullRejectsVisit (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Nat → Bool → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, peel, expression =>
      let inspect := joinScalarNullRejectsVisit context prepared side fuel
      match expression with
      | .collate arg _ => if peel then inspect true arg else
          joinScalarNullWalk context prepared side (fuel + 1) expression
      | .call name args false =>
          match if peel then SQLite.Probability.input? name args else none with
          | some arg => inspect true arg
          | none => joinScalarNullWalk context prepared side (fuel + 1) expression
      | .binary .and left right => inspect true left || inspect false right
      | .isNull arg true => peel && joinScalarNullWalk context prepared side fuel arg
      | _ => joinScalarNullWalk context prepared side (fuel + 1) expression

def joinScalarNullRejects (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (fuel : Nat) (expression : Expr) : Bool :=
  joinScalarNullRejectsVisit context prepared side fuel true expression

theorem joinScalarNullRejectsVisit_unpeeled_notNull (context : JoinContext)
    (prepared : JoinScalarPrepared) (side : CoreJoin.Side) (fuel : Nat) (arg : Expr) :
    joinScalarNullRejectsVisit context prepared side (fuel + 1) false (.isNull arg true) = false := rfl

/-- Both alternatives must reject a missing source before an OR expression
can establish a non-null source. This is a syntactic optimizer property. -/
theorem joinScalarNullWalk_or (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (fuel : Nat) (left right : Expr) :
    joinScalarNullWalk context prepared side (fuel + 1) (.binary .or left right) =
      (joinScalarNullWalk context prepared side fuel left &&
        joinScalarNullWalk context prepared side fuel right) := rfl

/-- An AND's left branch gets the root null-test rule; its final right branch
uses the unpeeled walk. ON terms are excluded by the caller. -/
theorem joinScalarNullRejects_and (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (fuel : Nat) (left right : Expr) :
    joinScalarNullRejects context prepared side (fuel + 1) (.binary .and left right) =
      (joinScalarNullRejects context prepared side fuel left ||
        joinScalarNullRejectsVisit context prepared side fuel false right) := rfl

def joinScalarProbesRowid (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      let inspect := joinScalarProbesRowid context prepared side fuel
      match expression with
      | .collate arg _ => inspect arg
      | .binary .and left right => inspect left || inspect right
      | .binary .eq left right =>
          let other := if side == .left then CoreJoin.Side.right else .left
          let schema := if side == .left then context.leftSchema else context.rightSchema
          let probes := fun column value =>
            (joinScalarReference context prepared column).any (fun ref => ref.side == side && ref.column == schema.primaryKey) &&
              joinScalarOnlySide context prepared other value
          probes left right || probes right left
      | _ => false

/-- An equality lookup on a non-rowid inner column can use a transient index.
Its rowid suffix is not treated as an ordered table scan by SQLite's planner. -/
def joinScalarAutomaticProbe (context : JoinContext) (prepared : JoinScalarPrepared) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      let inspect := joinScalarAutomaticProbe context prepared fuel
      match expression with
      | .collate arg _ => inspect arg
      | .binary .and left right => inspect left || inspect right
      | .binary .eq left right =>
          let probes := fun column value =>
            (joinScalarReference context prepared column).any (fun ref =>
              ref.side == .right && ref.column != context.rightSchema.primaryKey) &&
              joinScalarOnlySide context prepared .left value
          probes left right || probes right left
      | _ => false

/-- Only WHERE can remove an outer side. A condition that admits a missing
source leaves that side's unmatched-row bookkeeping in place. -/
def joinScalarReducedSource (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) : TableRef :=
  { source with
    leftJoin := source.leftJoin && !prepared.select.where_.any
      (fun expr => joinScalarNullRejects context prepared .right expr.height expr)
    rightJoin := source.rightJoin && !prepared.select.where_.any
      (fun expr => joinScalarNullRejects context prepared .left expr.height expr) }

theorem joinScalarReducedSource_no_new_outer (context : JoinContext)
    (prepared : JoinScalarPrepared) (source : TableRef) :
    ((joinScalarReducedSource context prepared source).leftJoin = true → source.leftJoin = true) ∧
    ((joinScalarReducedSource context prepared source).rightJoin = true → source.rightJoin = true) := by
  constructor <;> intro kept <;>
    simp only [joinScalarReducedSource, Bool.and_eq_true] at kept <;> exact kept.1

/-- Both the physical rowid and declared NOT NULL payload columns carry
non-null metadata before outer-row extension. -/
def joinScalarColumnNotNull (context : JoinContext) (ref : CoreJoin.ColumnRef) : Bool :=
  let schema := if ref.side == .left then context.leftSchema else context.rightSchema
  ref.column == schema.primaryKey || (schema.columns[ref.column]?).any (·.notNull)

/-- Original outer-source nullability overrides a column's declaration while
expressions are prepared, even if a later WHERE condition reduces the join. -/
def joinScalarOriginallyNullable (context : JoinContext) (prepared : JoinScalarPrepared)
    (ref : CoreJoin.ColumnRef) : Bool :=
  (if ref.side == .left then prepared.nullableLeft else prepared.nullableRight) ||
    !joinScalarColumnNotNull context ref

theorem joinScalarOriginallyNullable_outer (context : JoinContext) (prepared : JoinScalarPrepared)
    (ref : CoreJoin.ColumnRef)
    (outer : (if ref.side == .left then prepared.nullableLeft else prepared.nullableRight) = true) :
    joinScalarOriginallyNullable context prepared ref = true := by
  unfold joinScalarOriginallyNullable
  rw [outer]
  simp

/-- A present source row preserves its non-null column constraints. SQLite
can eliminate a conjunct asking such a column to be NULL before either cursor.
An outer side that may be absent does not provide this fact. -/
def joinScalarKnownEmpty (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) : Bool :=
  (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).any fun term =>
    match SQLite.ExprCollation.strip term with
    | .isNull argument false => (joinScalarReference context prepared argument).any fun ref =>
        joinScalarColumnNotNull context ref &&
          (if ref.side == .left then !source.rightJoin else !source.leftJoin)
    | _ => false

/-- A selected cursor constraint retains the original comparison operands so
lookup filtering uses the same affinity and collation as its SQL condition. -/
structure JoinSearchKey where
  column : Expr
  value : Expr
  operation : BinaryOp := .eq

inductive JoinSearchAccess where
  | scan
  | point (key : JoinSearchKey)
  | membership (column : Expr) (values : List Expr)
  | range (start finish : Option JoinSearchKey)
  | automatic (keys : List JoinSearchKey)

structure JoinFixedColumn where
  index : Nat
  origin : Nat
  expression : Expr
  affinity : SQLite.Affinity

/-- A point seek or a one-element constant IN loop visits at most one row. -/
def JoinSearchAccess.singleton : JoinSearchAccess → Bool
  | .point _ | .membership _ [_] => true
  | _ => false

structure JoinSearchPlan where
  access : JoinSearchAccess := .scan
  early : List Expr := []
  fixed : List JoinFixedColumn := []
  innerWhere : List Expr := []

structure JoinSearchResult where
  rows : List (Core.Row × Nat)
  halt : Bool := false

def joinSearchOpposite : CoreJoin.Side → CoreJoin.Side
  | .left => .right
  | .right => .left

def joinSearchSwap : BinaryOp → BinaryOp
  | .lt => .gt | .le => .ge | .gt => .lt | .ge => .le | op => op

def joinSearchKey? (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (expression : Expr) : Option JoinSearchKey := do
  let .binary operation left right := SQLite.ExprCollation.strip expression | none
  unless [.eq, .is, .lt, .le, .gt, .ge].contains operation do none
  if operation == .is && (SQLite.Scalar.isTruthKeyword? right).isSome then none
  let candidate := fun column value operation => do
    let ref ← joinScalarReference context prepared column
    unless ref.side == side && joinScalarOnlySide context prepared (joinSearchOpposite side) value do none
    return ({ column, value, operation } : JoinSearchKey)
  candidate left right operation <|> candidate right left (joinSearchSwap operation)

/-- whereexpr.c keeps an indexed original left operand in place. When both
operands are columns, the swapped constraint is appended as a virtual term.
The expression analyzer visits original terms from right to left. -/
def joinSearchKeyOrder (keys : List (Bool × JoinSearchKey)) : List JoinSearchKey :=
  ((keys.filter (fun item => !item.1)) ++ (keys.filter Prod.fst).reverse).map Prod.snd

theorem joinSearchKeyOrder_perm (keys : List (Bool × JoinSearchKey)) :
    (joinSearchKeyOrder keys).Perm (keys.map Prod.snd) := by
  have partition : (keys.filter (fun item => !item.1) ++ keys.filter Prod.fst).Perm keys := by
    simpa only [Bool.not_not] using List.filter_append_perm (fun item : Bool × JoinSearchKey => !item.1) keys
  exact ((List.reverse_perm (keys.filter Prod.fst)).append_left
    (keys.filter (fun item => !item.1)) |>.trans partition).map Prod.snd

def joinSearchKeys (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (terms : List Expr) : List JoinSearchKey :=
  joinSearchKeyOrder ((joinSearchRangeTerms terms).filterMap fun term => do
    let key ← joinSearchKey? context prepared side term
    let virtual := match SQLite.ExprCollation.strip term with
      | .binary _ left right => (joinScalarReference context prepared left).isSome &&
          (joinScalarReference context prepared right).any (fun ref => ref.side == side)
      | _ => false
    return (virtual, key))

/-- where.c:sqlite3WhereFindTerm prefers a constant RHS, then the first usable
constraint in SQL term order. This selection does not inspect row values. -/
def joinSearchChoose (prepared : JoinScalarPrepared) (keys : List JoinSearchKey) : Option JoinSearchKey :=
  keys.find? (fun key => prepared.context.constantExpression key.value) <|> keys.head?

def joinSearchIndexAffinity (prepared : JoinScalarPrepared) (key : JoinSearchKey) : Bool :=
  let affinity := (prepared.context.affinity key.column).getD .blob
  let comparison := SQLite.Scalar.comparisonAffinity (prepared.context.affinity key.column)
    (prepared.context.affinity key.value)
  comparison == .blob || (comparison == .text && affinity == .text) ||
    (SQLite.Scalar.numericAffinity comparison && SQLite.Scalar.numericAffinity affinity)

/-- USING/NATURAL equality can drive an automatic index only when its
comparison affinity is compatible with the indexed side. Rowid equalities
are handled as point probes, independently of this flag. -/
def joinUsingAutomaticProbe (context : JoinContext) (_prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Bool := joinUsingIndexEligible context side

def joinSearchConstantRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (on : Option Expr) : Option JoinSearchAccess := do
  let schema := if side == .left then context.leftSchema else context.rightSchema
  let terms := on.map SQLite.Scalar.conditionTerms |>.getD []
  let point := (terms.filterMap (joinSearchKey? context prepared side)).find? fun key =>
    [.eq, .is].contains key.operation && prepared.context.constantExpression key.value &&
      (joinScalarReference context prepared key.column).any (fun ref => ref.column == schema.primaryKey)
  if let some key := point then return .point key
  terms.findSome? fun term => do
    let .inList column values false _ := SQLite.ExprCollation.strip term | none
    let ref ← joinScalarReference context prepared column
    unless ref.side == side && ref.column == schema.primaryKey && values.all prepared.context.constantExpression do none
    return .membership column values.toList

def joinSearchSingletonKey : JoinSearchAccess → Option JoinSearchKey
  | .point key => some key
  | .membership column [value] => some { column, value := .unary .plus value }
  | _ => none

/-- Constant-column preparation retains column affinity. EQ needs a bare
column, a constant RHS without expression affinity and BINARY comparison.
A one-element IN supplies the affinity-free RHS used by scalar preparation. -/
def joinSearchFixesColumn (prepared : JoinScalarPrepared) (key : JoinSearchKey) : Bool :=
  key.operation == .eq && prepared.context.constantExpression key.value &&
    (prepared.context.affinity key.value).isNone &&
    SQLite.ExprCollation.binaryKind? key.column key.value == some .binary &&
    (match key.column with | .column .. => true | _ => false)

def joinSearchRootFixed (context : JoinContext) (prepared : JoinScalarPrepared)
    (root : Option JoinSearchAccess) (on : Option Expr) : Bool :=
  root.any fun access => (joinSearchSingletonKey access).any fun key =>
    (joinScalarReference context prepared key.column).any fun ref =>
      [on, prepared.select.where_].any fun condition =>
        (joinSearchConstantRoot context prepared ref.side condition).any fun candidate =>
          (joinSearchSingletonKey candidate).any (joinSearchFixesColumn prepared)

/-- Keep a constraint's operation and key expression while propagating its
rowid column across a direct rowid equality. -/
def JoinSearchKey.retarget (key : JoinSearchKey) (column : Expr) : JoinSearchKey :=
  { key with column }

theorem JoinSearchKey.retarget_value (key : JoinSearchKey) (column : Expr) :
    (key.retarget column).value = key.value ∧
      (key.retarget column).operation = key.operation := ⟨rfl, rfl⟩

def joinSearchRowidEquality (context : JoinContext) (prepared : JoinScalarPrepared)
    (on : Option Expr) : Bool :=
  (on.map SQLite.Scalar.conditionTerms |>.getD []).any fun term =>
    match SQLite.ExprCollation.strip term with
    | .binary .eq left right =>
        match joinScalarReference context prepared left, joinScalarReference context prepared right with
        | some l, some r => l.side != r.side &&
            l.column == (if l.side == .left then context.leftSchema else context.rightSchema).primaryKey &&
            r.column == (if r.side == .left then context.leftSchema else context.rightSchema).primaryKey
        | _, _ => false
    | _ => false

def joinSearchRangeBound (context : JoinContext) (prepared : JoinScalarPrepared)
    (term : Expr) : Option (CoreJoin.Side × JoinSearchKey) := do
  let key ← joinSearchKey? context prepared .left term <|> joinSearchKey? context prepared .right term
  unless [.lt, .le, .gt, .ge].contains key.operation && prepared.context.constantExpression key.value do none
  let ref ← joinScalarReference context prepared key.column
  unless ref.column == (if ref.side == .left then context.leftSchema else context.rightSchema).primaryKey do none
  return (ref.side, key)

/-- A direct rowid equality carries constant bounds from either source to the
outer cursor. The key value and comparison operator are retained unchanged. -/
def joinSearchRangeRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (on : Option Expr) : Option JoinSearchAccess := do
  let equal := joinSearchRowidEquality context prepared on
  let keys := (joinSearchRangeTerms (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD [])).filterMap fun term => do
    let (origin, key) ← joinSearchRangeBound context prepared term
    unless origin == side || equal do none
    return key
  let lower := joinSearchChoose prepared (keys.filter (fun key => [.gt, .ge].contains key.operation))
  let upper := joinSearchChoose prepared (keys.filter (fun key => [.lt, .le].contains key.operation))
  unless lower.isSome || upper.isSome do none
  let schema := if side == .left then context.leftSchema else context.rightSchema
  let column ← joinScalarOperand context (.column ⟨side, schema.primaryKey⟩)
  return .range (lower.map (·.retarget column)) (upper.map (·.retarget column))

/-- Constant ON bounds can drive the outer cursor when an ORDER BY on
that rowid selects it. WHERE bounds retain their existing priority. -/
def joinSearchIndependentRangeRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (on : Option Expr) : Option JoinSearchAccess := do
  if let some root := joinSearchRangeRoot context prepared side on then return root
  let keys := (joinSearchRangeTerms (on.map SQLite.Scalar.conditionTerms |>.getD [])).filterMap fun term => do
    let (origin, key) ← joinSearchRangeBound context prepared term
    unless origin == side do none
    return key
  let lower := joinSearchChoose prepared (keys.filter (fun key => [.gt, .ge].contains key.operation))
  let upper := joinSearchChoose prepared (keys.filter (fun key => [.lt, .le].contains key.operation))
  unless lower.isSome || upper.isSome do none
  return .range lower upper

/-- Unindexed null tests on an originally nullable source reduce its estimated
output. where.c:whereLoopOutputAdjust decrements LogEst for each such term.
Keep the two-source null-test score independent of actual stored row values. -/
def joinSearchNullFilterCount (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Nat :=
  ((prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter fun term =>
    match SQLite.ExprCollation.strip term with
    | .isNull arg _ => (joinScalarReference context prepared arg).any (fun ref =>
        ref.side == side && joinScalarOriginallyNullable context prepared ref)
    | _ => false).length

def joinSearchRetainedRightNullFilter (context : JoinContext) (prepared : JoinScalarPrepared) : Bool :=
  joinSearchNullFilterCount context prepared .right != 0

/-- For the unordered two-source range/point shape, the derived right range
drives the left point lookup. Extra left filters retain the left-driven plan. -/
def joinSearchTransitiveRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (on : Option Expr) : Option JoinSearchAccess := do
  unless joinSearchRowidEquality context prepared on do none
  let onTerms := on.map SQLite.Scalar.conditionTerms |>.getD []
  if onTerms.any (fun term => joinScalarOnlySide context prepared .left term &&
      !prepared.context.constantExpression term) &&
      !joinSearchRetainedRightNullFilter context prepared then none
  let whereTerms := joinSearchRangeTerms (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD [])
  let compatibleNullTest := fun term => match SQLite.ExprCollation.strip term with
    | .isNull arg true => (joinScalarReference context prepared arg).any (fun ref =>
        ref.side == .right || !joinScalarOriginallyNullable context prepared ref)
    | _ => false
  unless whereTerms.all (fun term => prepared.context.constantExpression term ||
      compatibleNullTest term ||
      (joinSearchRangeBound context prepared term).any (fun bound => bound.1 == .left)) do none
  joinSearchRangeRoot context prepared .right on

/-- In an unordered rowid-equality join, a retained right-side null
filter gives that scan a lower row estimate. A rowid null test originating on
the nullable side survives early expression preparation, even after reduction.
This covers this two-source plan shape, not the general statistics solver. -/
def joinSearchNullFilterRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (on : Option Expr) : Option JoinSearchAccess := do
  unless joinSearchRowidEquality context prepared on do none
  let onTerms := on.map SQLite.Scalar.conditionTerms |>.getD []
  if onTerms.any (fun term => joinScalarOnlySide context prepared .left term &&
      !prepared.context.constantExpression term) then none
  let terms := prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []
  let test := fun term => match SQLite.ExprCollation.strip term with
    | .isNull arg _ => joinScalarReference context prepared arg
    | _ => none
  unless terms.all (fun term => prepared.context.constantExpression term ||
      (test term).any (fun ref => ref.side == .right || !joinScalarOriginallyNullable context prepared ref)) do none
  unless terms.any (fun term => (test term).any (fun ref => ref.side == .right &&
      joinScalarOriginallyNullable context prepared ref)) do none
  return .scan

/-- An unfixed rowid equality can carry a singleton bound to the opposite
cursor. A fixed left operand also generates the swapped constant constraint.
Source-local left filters retain the left-driven singleton plan. -/
def joinSearchDerivedRightRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (leftRoot : Option JoinSearchAccess) (on : Option Expr) : Option JoinSearchAccess := do
  let root ← leftRoot
  let key ← joinSearchSingletonKey root
  let terms := on.map SQLite.Scalar.conditionTerms |>.getD []
  let rootTerm := fun term => (joinSearchKey? context prepared .left term).any fun candidate =>
    [.eq, .is].contains candidate.operation && prepared.context.constantExpression candidate.value &&
      joinScalarReference context prepared candidate.column == joinScalarReference context prepared key.column
  if terms.any (fun term => joinScalarOnlySide context prepared .left term &&
      !prepared.context.constantExpression term && !rootTerm term) then none
  unless joinSearchRowidEquality context prepared on do none
  if joinSearchRootFixed context prepared leftRoot on &&
      joinSearchNullFilterCount context prepared .right ≤ joinSearchNullFilterCount context prepared .left then
    unless terms.any (fun term => match SQLite.ExprCollation.strip term with
      | .binary .eq left right =>
          (joinScalarReference context prepared left).any (fun ref =>
            ref.side == .left && ref.column == context.leftSchema.primaryKey) &&
          (joinScalarReference context prepared right).any (fun ref =>
            ref.side == .right && ref.column == context.rightSchema.primaryKey)
      | _ => false) do none
  let column ← joinScalarOperand context (.column ⟨.right, context.rightSchema.primaryKey⟩)
  return .point (key.retarget column)

/-- Default rowid range estimates reduce LogEst by 20 for one bound and
60 for both bounds (where.c:whereRangeScanEst). Only available opposite-source
bounds participate; this estimate never inspects stored row values. -/
def joinSearchRowidRangeReduction (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (on : Option Expr) : Nat :=
  let schema := if side == .left then context.leftSchema else context.rightSchema
  let keys := joinSearchKeys context prepared side (on.map SQLite.Scalar.conditionTerms |>.getD [])
  let rowid := fun key => (joinScalarReference context prepared key.column).any (fun ref => ref.column == schema.primaryKey)
  let lower := keys.any (fun key => rowid key && [.gt, .ge].contains key.operation)
  let upper := keys.any (fun key => rowid key && [.lt, .le].contains key.operation)
  if lower && upper then 60 else if lower || upper then 20 else 0

/-- In an unordered pair of unindexed scans, source-local residual predicates
lower the source's default row estimate by one LogEst unit each. Keep existing
point/range/automatic choices and probability-hinted plans outside this rule. -/
def joinSearchScanFilterRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (on : Option Expr) : Option JoinSearchAccess := do
  let terms := (on.map SQLite.Scalar.conditionTerms |>.getD []) ++
    (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD [])
  unless terms.all (fun term => !term.any (fun node => match node with
    | .call name _ _ => SQLite.Probability.recognizesName (SQLite.Scalar.scalarFunctionName name)
    | _ => false)) do none
  for side in [CoreJoin.Side.left, .right] do
    let keys := joinSearchKeys context prepared side terms
    let schema := if side == .left then context.leftSchema else context.rightSchema
    unless !keys.any (fun key =>
      (joinScalarReference context prepared key.column).any (fun ref => ref.column == schema.primaryKey) ||
        ([.eq, .is].contains key.operation && joinSearchIndexAffinity prepared key)) do none
  let count := fun side => (terms.filter fun term =>
    !prepared.context.constantExpression term && joinScalarOnlySide context prepared side term &&
      (match SQLite.ExprCollation.strip term with
        | .isNull argument true => !(joinScalarReference context prepared argument).any
            (fun ref => !joinScalarOriginallyNullable context prepared ref)
        | _ => true)).length
  unless count .right > count .left do none
  return .scan

/-- One source traversal plan serves both streaming and materialized results.
A right-driven rowid lookup also determines the order in which a bounded sorter
sees candidates; it must not be changed to a left-driven cross product. -/
structure JoinScalarTraversal where
  exchanged : Bool
  reverseLeft : Bool
  reverseRight : Bool
  ordered : Bool
  root : Option JoinSearchAccess := none

def joinScalarTraversal (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (terms : List OrderTerm) (on : Option Expr) : JoinScalarTraversal :=
  let aggregate := !prepared.select.groupBy.isEmpty ||
    prepared.select.columns.any (fun c => CoreAggregate.containsAggregate c.expr)
  let probesLeft := on.any (fun e => joinScalarProbesRowid context prepared .left e.height e) ||
    context.shared.any (fun column => column.left == context.leftSchema.primaryKey)
  let probesRight := on.any (fun e => joinScalarProbesRowid context prepared .right e.height e) ||
    context.shared.any (fun column => column.right == context.rightSchema.primaryKey)
  let mayExchange := !source.leftJoin && !source.rightJoin && !source.crossJoin
  let sharedLeft := joinUsingAutomaticProbe context prepared .left
  let sharedRight := joinUsingAutomaticProbe context prepared .right
  let leadingRight := terms.head?.any (fun term =>
    (joinScalarReference context prepared term.expr).any (fun ref => ref.side == .right && ref.column == context.rightSchema.primaryKey))
  let rightOnly := on.any (fun expression =>
    !prepared.context.constantExpression expression && joinScalarOnlySide context prepared .right expression)
  let leftRange := joinSearchRowidRangeReduction context prepared .left on
  let rightRange := joinSearchRowidRangeReduction context prepared .right on
  let leadingLeft := terms.head?.any (fun term =>
    (joinScalarReference context prepared term.expr).any (fun ref => ref.side == .left && ref.column == context.leftSchema.primaryKey))
  -- An unbounded outer-rowid ORDER can outweigh a dependent range lookup.
  -- An independent WHERE range on the right still supplies a selective root.
  let rangeExchange := !probesLeft && !probesRight && leftRange > rightRange &&
    (!leadingLeft || prepared.select.limit.isSome ||
      (joinSearchRangeRoot context prepared .right on).isSome)
  let leftRoot := (if mayExchange then joinSearchConstantRoot context prepared .left on else none).orElse
    (fun _ => if !source.rightJoin then
      joinSearchConstantRoot context prepared .left prepared.select.where_ else none)
  let rightRoot := if mayExchange then
      ((joinSearchConstantRoot context prepared .right on).orElse
        (fun _ => joinSearchConstantRoot context prepared .right prepared.select.where_)).orElse
        (fun _ => if terms.isEmpty then
          (joinSearchTransitiveRoot context prepared on).orElse
            (fun _ => (joinSearchNullFilterRoot context prepared on).orElse
              (fun _ => joinSearchScanFilterRoot context prepared on)) else none)
    else none
  let rightRoot := rightRoot.orElse (fun _ =>
    if mayExchange && !probesLeft && !probesRight &&
        (leftRange > 0 || leadingRight || (terms.isEmpty && rightOnly && rightRange == 0 &&
          joinSearchRowidRangeReduction context prepared .right prepared.select.where_ > 20)) &&
        (rangeExchange || !leadingLeft || prepared.select.limit.isSome) then
      joinSearchIndependentRangeRoot context prepared .right on else none)
  let rightRoot := match rightRoot with
    | some (.membership ..) => if leadingLeft && prepared.select.limit.isNone then none else rightRoot
    | _ => rightRoot
  let rightNeedsPoint := match rightRoot with
    | none | some .scan | some (.range ..) => true
    | _ => false
  let derivedRight := if mayExchange && rightNeedsPoint then
      joinSearchDerivedRightRoot context prepared leftRoot on else none
  let rightRoot := derivedRight.orElse (fun _ => rightRoot)
  let filteredRightPoint := leftRoot.any JoinSearchAccess.singleton &&
    rightRoot.any JoinSearchAccess.singleton &&
    joinSearchNullFilterCount context prepared .right > joinSearchNullFilterCount context prepared .left
  let exchanged := mayExchange && (leftRoot.isNone || derivedRight.isSome || filteredRightPoint) &&
    (rightRoot.isSome || (probesLeft && !probesRight) ||
      (sharedLeft && !sharedRight && !probesRight) || rangeExchange)
  let root := if exchanged then rightRoot else leftRoot
  let singleton := root.any JoinSearchAccess.singleton
  let outerSide := if exchanged then CoreJoin.Side.right else .left
  let outerSchema := if exchanged then context.rightSchema else context.leftSchema
  let innerSchema := if exchanged then context.leftSchema else context.rightSchema
  let leadingOuter := !aggregate && terms.head?.any (fun term =>
    (joinScalarReference context prepared term.expr).any
      (fun ref => ref.side == outerSide && ref.column == outerSchema.primaryKey))
  let leadingInner := singleton && !aggregate && terms.head?.any (fun term =>
    (joinScalarReference context prepared term.expr).any
      (fun ref => ref.side != outerSide && ref.column == innerSchema.primaryKey))
  let outerReverse := leadingOuter && terms.head?.any (·.descending)
  let root := root.orElse (fun _ => if !source.leftJoin && !source.rightJoin then
      joinSearchRangeRoot context prepared outerSide on else none)
  let root := match root with
    | some (.range start finish) => if outerReverse then some (.range finish start) else root
    | _ => root
  -- USING/NATURAL share the same index-order restriction as explicit ON;
  -- a shared rowid conjunct supplies a point lookup even with other keys.
  let automatic := !singleton &&
    ((if exchanged then sharedLeft else sharedRight) ||
      (!exchanged && on.any (fun e => joinScalarAutomaticProbe context prepared e.height e)))
  let innerPoint := if exchanged then probesLeft else probesRight
  let outerTermsOnly := terms.all (fun term => (joinScalarReference context prepared term.expr).any
    (fun ref => ref.side == outerSide))
  let prefixOrdered := (leadingOuter || leadingInner) && (innerPoint || !automatic || outerTermsOnly) &&
    terms.all (fun term => (joinScalarReference context prepared term.expr).any
      (fun ref => ref.side == outerSide || ref.column == innerSchema.primaryKey))
  let ordered := prefixOrdered && !source.rightJoin
  let innerReverse := prefixOrdered && (terms.find? (fun term =>
    (joinScalarReference context prepared term.expr).any (fun ref => ref.side != outerSide))).any (·.descending)
  { exchanged
    reverseLeft := if exchanged then innerReverse else outerReverse
    reverseRight := if exchanged then outerReverse else innerReverse
    ordered, root }

/-- select.c:constInsert visits the rightmost equality first. A replacement
has no expression affinity and uses BINARY comparison. Origin indices retain
which column occurrence defines, rather than consumes, the fixed value. -/
def joinFixedColumns (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (source : TableRef) (on : Option Expr) : List JoinFixedColumn := Id.run do
  if source.leftJoin || source.rightJoin then return []
  let terms := on.map SQLite.Scalar.conditionTerms |>.getD []
  let mut result := []
  for (term, origin) in terms.zipIdx.reverse do
    if let some key := joinSearchKey? context prepared side term then
      if key.operation == .eq && prepared.context.constantExpression key.value &&
          (prepared.context.affinity key.value).isNone &&
          SQLite.ExprCollation.binaryKind? key.column key.value == some .binary then
        if let .column qualifier name := key.column then
          if let some index := prepared.context.column? qualifier name then
            unless result.any (fun item => item.index == index) do
              result := result ++ [{
                index := index
                origin := origin
                expression := key.value
                affinity := (prepared.context.affinity key.column).getD .blob }]
  return result

/-- BLOB-affinity fixed columns are substituted only as immediate comparison
operands; the right operand is protected when the left carries TEXT affinity. -/
def joinFixedReady (context : JoinContext) (prepared : JoinScalarPrepared)
    (outer : Option CoreJoin.Side) (fixed : List JoinFixedColumn) (markedBounds : Bool) : Nat → Bool → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, blobAllowed, expression =>
      let ready := joinFixedReady context prepared outer fixed markedBounds fuel false
      match expression with
      | .literal .. => true
      | .column qualifier name =>
          (joinScalarReference context prepared expression).any (fun ref => outer == some ref.side) ||
            (prepared.context.column? qualifier name).any (fun index => fixed.any
              (fun item => item.index == index && (item.affinity != .blob || blobAllowed)))
      | .unary _ argument | .collate argument _ | .isNull argument _ => ready argument
      | .binary operation left right =>
          if [.eq, .lt, .le, .gt, .ge, .is].contains operation then
            joinFixedReady context prepared outer fixed markedBounds fuel true left &&
              joinFixedReady context prepared outer fixed markedBounds fuel (prepared.context.affinity left != some .text) right
          else ready left && ready right
      | .call "__sqlean_between" arguments false =>
          match arguments.toList with
          | [argument, lower, upper] =>
              -- select.c:unsetJoinExpr clears pLeft and function arguments,
              -- but retains original outer markings on a BETWEEN bound list.
              let bound := joinFixedReady context prepared outer
                (if markedBounds then [] else fixed) markedBounds fuel false
              ready argument && bound lower && bound upper
          | _ => false
      | .call _ arguments false => arguments.all ready
      | .inList argument values _ _ => ready argument && values.all ready
      | .case_ base branches otherwise => base.all ready && otherwise.all ready &&
          branches.all (fun (condition, value) => ready condition && ready value)
      | _ => false

/-- Original outer markings prevent constant substitution in the BETWEEN
bound list, while its tested pLeft operand uses the ordinary fixed-column walk. -/
theorem joinFixedReady_between_marked (context : JoinContext) (prepared : JoinScalarPrepared)
    (outer : Option CoreJoin.Side) (fixed : List JoinFixedColumn) (fuel : Nat)
    (argument lower upper : Expr) :
    joinFixedReady context prepared outer fixed true (fuel + 1) false
      (.call "__sqlean_between" #[argument, lower, upper] false) =
      (joinFixedReady context prepared outer fixed true fuel false argument &&
        joinFixedReady context prepared outer [] true fuel false lower &&
        joinFixedReady context prepared outer [] true fuel false upper) := rfl

def joinFixedEarly (context : JoinContext) (prepared : JoinScalarPrepared)
    (outer : CoreJoin.Side) (fixed : List JoinFixedColumn) (on : Option Expr) : List Expr :=
  (on.map SQLite.Scalar.conditionTerms |>.getD []).zipIdx.filterMap fun (term, index) =>
    if fixed.any (fun item => item.origin == index) then none
    else if joinFixedReady context prepared (some outer) fixed
        (prepared.nullableLeft || prepared.nullableRight) term.height false term then some term
    else none

/-- EP_FixedCol keeps the column's affinity and applies that affinity when
loading the constant value. Other source values keep the ordinary lookup. -/
def joinFixedLookup (prepared : JoinScalarPrepared) (input : List Core.Value)
    (fixed : List JoinFixedColumn) (qualifier : Option String) (name : String) : Except String Value := do
  let index := prepared.context.column? qualifier name
  if let some item := fixed.find? (fun item => index == some item.index) then
    let value ← prepared.context.eval input item.expression
    CoreExpr.value (SQLite.PhysicalAffinity.write item.affinity (← SQLSurface.value value))
  else prepared.context.lookup input qualifier name

def joinFixedMatches (prepared : JoinScalarPrepared) (input : List Core.Value)
    (fixed : List JoinFixedColumn) (terms : List Expr) : Except String Bool :=
  let context : CoreExpr.Context := { prepared.context with fixedColumns := fixed.map (fun item => item.index) }
  SQLite.Scalar.testTermsWithConstants (joinFixedLookup prepared input fixed)
    context.affinity context.constantExpression
    (terms.map (fun term => SQLite.Scalar.prepare (context.bindNames term)))


/-- A NOT NULL test on an originally non-null column is removed during
expression preparation, before fixed constants can introduce value evaluation. -/
def joinScalarTrivialNotNull (context : JoinContext) (prepared : JoinScalarPrepared)
    (term : Expr) : Bool :=
  match SQLite.ExprCollation.strip term with
  | .isNull argument true => (joinScalarReference context prepared argument).any
      (fun ref => !joinScalarOriginallyNullable context prepared ref)
  | _ => false

/-- Fixed ON columns can turn WHERE terms into constant predicates. Evaluate
only substitutions allowed by the original affinity walk, before either cursor.
Outer joins retain their original constant-WHERE preparation. -/
def joinFixedConstantMatches (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (on : Option Expr) : Except String Bool :=
  if source.leftJoin || source.rightJoin then
    prepared.context.constantMatches prepared.select.where_
  else
    let fixed := joinFixedColumns context prepared .left source on ++
      joinFixedColumns context prepared .right source on
    let ctx : CoreExpr.Context := { prepared.context with fixedColumns := fixed.map (fun item => item.index) }
    let terms := (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
      (fun term => !joinScalarTrivialNotNull context prepared term && ctx.constantExpression term &&
        joinFixedReady context prepared none fixed false term.height false term)
    joinFixedMatches prepared [] fixed terms

theorem joinFixedConstantMatches_outer (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (on : Option Expr)
    (outer : (source.leftJoin || source.rightJoin) = true) :
    joinFixedConstantMatches context prepared source on =
      prepared.context.constantMatches prepared.select.where_ := by
  unfold joinFixedConstantMatches
  rw [outer]
  rfl


theorem joinFixedLookup_unfixed (prepared : JoinScalarPrepared) (input : List Core.Value)
    (fixed : List JoinFixedColumn) (qualifier : Option String) (name : String)
    (absent : fixed.find? (fun item => prepared.context.column? qualifier name == some item.index) = none) :
    joinFixedLookup prepared input fixed qualifier name = prepared.context.lookup input qualifier name := by
  simp [joinFixedLookup, absent]

/-- A BETWEEN pair consumes one parent predicate in whereLoopOutputAdjust,
whereas independently selected lower/upper terms consume two. Keep the pair
when both bounds can drive the same rowid cursor. Virtual children are appended
while original terms are analyzed right-to-left, including ON after WHERE. -/
def joinSearchBetweenPair (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (terms : List Expr) : Option (JoinSearchKey × JoinSearchKey) :=
  terms.reverse.findSome? fun term => do
    let .call "__sqlean_between" arguments false := SQLite.ExprCollation.strip term | none
    let [argument, lower, upper] := arguments.toList | none
    let ref ← joinScalarReference context prepared argument
    let schema := if side == .left then context.leftSchema else context.rightSchema
    unless ref.side == side && ref.column == schema.primaryKey &&
        joinScalarOnlySide context prepared (joinSearchOpposite side) lower &&
        joinScalarOnlySide context prepared (joinSearchOpposite side) upper do none
    return ({ column := argument, value := lower, operation := .ge },
      { column := argument, value := upper, operation := .le })

def joinSearchPlan (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (traversal : JoinScalarTraversal) (on : Option Expr) : JoinSearchPlan := Id.run do
  let side := if traversal.exchanged then CoreJoin.Side.left else .right
  let schema := if side == .left then context.leftSchema else context.rightSchema
  let outer := joinSearchOpposite side
  let terms := on.map SQLite.Scalar.conditionTerms |>.getD []
  let whereRanges := if source.leftJoin || source.rightJoin then [] else
    (joinSearchRangeTerms (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD [])).filterMap fun term => do
      let key ← joinSearchKey? context prepared side term
      unless [.lt, .le, .gt, .ge].contains key.operation do none
      return key
  let keys := whereRanges ++ joinSearchKeys context prepared side terms
  let rootFixed := joinSearchRootFixed context prepared traversal.root on
  let inherited := if source.leftJoin || source.rightJoin || rootFixed ||
      !joinSearchRowidEquality context prepared on then none else do
    let root ← traversal.root
    let key ← joinSearchSingletonKey root
    let column ← joinScalarOperand context (.column ⟨side, schema.primaryKey⟩)
    return key.retarget column
  let keys := inherited.toList ++ keys
  let rowid := fun key => (joinScalarReference context prepared key.column).any (fun ref => ref.column == schema.primaryKey)
  let equals := keys.filter (fun key => rowid key && [.eq, .is].contains key.operation)
  let fixedOuterColumn := fun key => rootFixed &&
    (traversal.root.bind joinSearchSingletonKey).any (fun root =>
      joinScalarReference context prepared key.value == joinScalarReference context prepared root.column)
  let equals := if !source.leftJoin && !source.rightJoin && !source.crossJoin then
      equals.filter (fun key => !fixedOuterColumn key) ++ equals.filter fixedOuterColumn else equals
  -- With a singleton outer source, a dependent point lookup retains the
  -- independent equality as an additional inner filter. CROSS/outer fences
  -- and an inherited transitive seek keep their existing constraint order.
  let dependent := fun key => !prepared.context.constantExpression key.value && !fixedOuterColumn key
  let equals := if !source.leftJoin && !source.rightJoin && !source.crossJoin &&
      traversal.root.any JoinSearchAccess.singleton && inherited.isNone then
      equals.filter dependent ++ equals.filter (fun key => !dependent key) else equals
  let fixed := joinFixedColumns context prepared side source on
  let early := if source.leftJoin || source.rightJoin then [] else
    joinFixedEarly context prepared outer fixed on
  let innerWhere := if source.leftJoin || source.rightJoin then [] else
    (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
      (fun term => joinScalarOnlySide context prepared side term && !prepared.context.constantExpression term)
  if let some key := equals.head? then
    return { access := .point key, early, fixed, innerWhere }
  let membership := terms.findSome? fun term => do
    let .inList column values false _ := SQLite.ExprCollation.strip term | none
    let ref ← joinScalarReference context prepared column
    unless ref.side == side && ref.column == schema.primaryKey &&
      values.all (joinScalarOnlySide context prepared outer) do none
    return (column, values.toList)
  if let some (column, values) := membership then
    return { access := .membership column values, early, fixed, innerWhere }
  -- With a non-singleton outer cursor, a usable automatic equality index
  -- has the default 20-row estimate, below the default rowid range estimate.
  if !source.rightJoin && !traversal.root.any JoinSearchAccess.singleton then
    let candidates := keys.filter (fun key => !rowid key && [.eq, .is].contains key.operation && joinSearchIndexAffinity prepared key)
    let mut chosen := []
    for key in candidates do
      let ref := joinScalarReference context prepared key.column
      unless chosen.any (fun old => joinScalarReference context prepared old.column == ref) do
        chosen := chosen ++ [key]
    unless chosen.isEmpty do return { access := .automatic chosen, early, fixed, innerWhere }
  let whereTerms := if source.leftJoin || source.rightJoin then [] else
    prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []
  let pair := joinSearchBetweenPair context prepared side (whereTerms ++ terms)
  let lower := (pair.map Prod.fst).orElse (fun _ =>
    joinSearchChoose prepared (keys.filter (fun key => rowid key && [.gt, .ge].contains key.operation)))
  let upper := (pair.map Prod.snd).orElse (fun _ =>
    joinSearchChoose prepared (keys.filter (fun key => rowid key && [.lt, .le].contains key.operation)))
  if lower.isSome || upper.isSome then
    let reverse := if traversal.exchanged then traversal.reverseLeft else traversal.reverseRight
    return { access := .range (if reverse then upper else lower) (if reverse then lower else upper), early, fixed, innerWhere }
  return { early, fixed, innerWhere }

def joinSearchPair (context : JoinContext) (exchanged : Bool) (outer : Core.Row)
    (inner : Option Core.Row := none) : CoreJoin.JoinedRow :=
  if exchanged then (inner.getD (CoreJoin.nullRow context.leftSchema.columns.length), outer)
  else (outer, inner.getD (CoreJoin.nullRow context.rightSchema.columns.length))

def joinSearchFilter (context : JoinContext) (prepared : JoinScalarPrepared)
    (exchanged : Bool) (outer : Core.Row) (key : JoinSearchKey) (value : Value)
    (rows : List (Core.Row × Nat)) : Except String (List (Core.Row × Nat)) :=
  rows.filterM fun (row, _) => do
    let input := CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer row)
    let column ← prepared.context.eval input key.column
    return SQLite.Numeric.truth (SQLite.Scalar.expressionComparisonWith prepared.context.affinity
      key.operation key.column key.value column value) == .true

/-- Cursor initialization happens before its first candidate pair. A rowid
seek evaluates its key even on an empty table. Rewind and automatic-index
construction can instead finish an inner join before evaluating that key. -/
def joinSearchCandidates (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (exchanged : Bool) (outer : Core.Row) (access : JoinSearchAccess)
    (inner : List (Core.Row × Nat)) : Except String JoinSearchResult := do
  let input := CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer)
  let evaluate := prepared.context.eval input
  let filter := joinSearchFilter context prepared exchanged outer
  match access with
  | .scan => return { rows := inner, halt := inner.isEmpty && !source.leftJoin }
  | .point key =>
      let value ← evaluate key.value
      return { rows := ← filter key value inner }
  | .membership column expressions =>
      let values ← expressions.mapM evaluate
      let rows ← inner.filterM fun (row, _) => do
        let rowInput := CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer row)
        let value ← prepared.context.eval rowInput column
        return values.any (fun key => SQLite.Numeric.truth (SQLite.Scalar.comparison .eq
          (SQLite.Scalar.applyComparisonAffinity .numeric value)
          (SQLite.Scalar.applyComparisonAffinity .numeric key)) == .true)
      return { rows }
  | .range start finish =>
      if start.isNone && inner.isEmpty then return { rows := [], halt := !source.leftJoin }
      let rows ← match start with
        | none => pure inner
        | some key => do filter key (← evaluate key.value) inner
      if rows.isEmpty then return { rows := [] }
      let rows ← match finish with
        | none => pure rows
        | some key => do filter key (← evaluate key.value) rows
      return { rows }
  | .automatic keys =>
      if inner.isEmpty && !source.leftJoin then return { rows := [], halt := true }
      let mut evaluated := []
      for key in keys do
        let value ← evaluate key.value
        if value == .null && key.operation == .eq then return { rows := [] }
        evaluated := evaluated ++ [(key, value)]
      let rows ← evaluated.foldlM (fun rows (key, value) => filter key value rows) inner
      return { rows }

/-- Failure to compute a selected point key propagates before inspecting any
candidate row, including when the physical input is empty. -/
theorem joinSearchCandidates_point_error (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (exchanged : Bool) (outer : Core.Row) (key : JoinSearchKey)
    (inner : List (Core.Row × Nat)) (message : String)
    (failed : prepared.context.eval
      (CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer))
      key.value = .error message) :
    joinSearchCandidates context prepared source exchanged outer (.point key) inner = .error message := by
  simp [joinSearchCandidates, failed, bind, Except.bind]

/-- Rewind does not evaluate an ON expression on an absent candidate pair. -/
theorem joinSearchCandidates_scan_empty (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (exchanged : Bool) (outer : Core.Row) :
    joinSearchCandidates context prepared source exchanged outer .scan [] =
      .ok { rows := [], halt := !source.leftJoin } := by
  simp [joinSearchCandidates, pure, Except.pure]

/-- For an inner join, building an empty automatic index halts before its
search-key expressions. LEFT joins instead proceed to initialize their keys. -/
theorem joinSearchCandidates_automatic_empty (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (exchanged : Bool) (outer : Core.Row) (keys : List JoinSearchKey)
    (inner : source.leftJoin = false) :
    joinSearchCandidates context prepared source exchanged outer (.automatic keys) [] =
      .ok { rows := [], halt := true } := by
  simp [joinSearchCandidates, inner, pure, Except.pure]

/-- Source-local inner WHERE filters run after cursor initialization and
before dynamic ON. Outer joins retain their ON-before-WHERE match bookkeeping. -/
def joinSearchMatches (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (row : CoreJoin.JoinedRow) : Except String Bool := do
  let input := CoreJoin.projectRow (joinScalarInputs context) row
  unless ← plan.innerWhere.allM (fun term => prepared.context.matches input (some term)) do return false
  joinScalarMatches context prepared (source.leftJoin || source.rightJoin) row

theorem joinSearchMatches_without_inner_filter (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (row : CoreJoin.JoinedRow)
    (empty : plan.innerWhere = []) :
    joinSearchMatches context prepared source plan row =
      joinScalarMatches context prepared (source.leftJoin || source.rightJoin) row := by
  simp [joinSearchMatches, empty]

/-- The planned row producer preserves original right-row indices for outer
match bookkeeping. An empty Rewind finishes its cursor nest; a failed point
seek merely advances to the next outer row. -/
def joinSearchRowsGo (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (exchanged : Bool)
    (inner : List (Core.Row × Nat)) : List Core.Row → List CoreJoin.JoinedRow → List Nat →
      Except String (List CoreJoin.JoinedRow)
  | [], reversed, matched =>
      let suffix := if source.rightJoin then
        (inner.filter (fun (_, index) => !matched.contains index)).map
          (fun (row, _) => (CoreJoin.nullRow context.leftSchema.columns.length, row)) else []
      .ok (reversed.reverse ++ suffix)
  | outer :: rest, reversed, matched => do
      let input := CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer)
      unless ← joinFixedMatches prepared input plan.fixed plan.early do
        return ← joinSearchRowsGo context prepared source plan exchanged inner rest reversed matched
      let found ← joinSearchCandidates context prepared source exchanged outer plan.access inner
      if found.halt then return reversed.reverse
      let selected ← found.rows.filterM (fun (row, _) => joinSearchMatches context prepared source plan (joinSearchPair context exchanged outer row))
      let rows := if selected.isEmpty && source.leftJoin then [joinSearchPair context false outer]
        else selected.map (fun (row, _) => joinSearchPair context exchanged outer row)
      joinSearchRowsGo context prepared source plan exchanged inner rest
        (rows.reverse ++ reversed) (selected.map Prod.snd ++ matched)

/-- Keep the proved total-predicate producer for scans without early terms;
computed searches and filters use the effectful cursor producer. -/
def joinSearchRows (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (exchanged : Bool)
    (inner : List (Core.Row × Nat)) (outer : List Core.Row) : Except String (List CoreJoin.JoinedRow) :=
  if plan.early.isEmpty && plan.innerWhere.isEmpty && prepared.onExpression.isNone then
    match plan.access with
    | .scan => joinScalarRowsM context prepared source
        (if exchanged then inner.map Prod.fst else outer)
        (if exchanged then outer else inner.map Prod.fst) exchanged
    | _ => joinSearchRowsGo context prepared source plan exchanged inner outer [] []
  else joinSearchRowsGo context prepared source plan exchanged inner outer [] []

structure JoinReadReport where
  result : Core.Result := {}
  width : Nat := 0
  error : Option String := none

def JoinReadReport.toExcept (report : JoinReadReport) : Except String (Core.Result × Nat) :=
  match report.error with
  | none => .ok (report.result, report.width)
  | some message => .error message

def joinScalarMaterializedReport (state : Core.State) (select : Select) : Except String JoinReadReport := do
  let (leftSource, originalRight) ← match select.sources.toList with
    | [left, right] => pure (left, right)
    | _ => unsupported "joined expression source count"
  unless leftSource.schema.isNone && leftSource.functionArgs.isNone && leftSource.subquerySql.isNone && originalRight.schema.isNone && originalRight.functionArgs.isNone && originalRight.subquerySql.isNone && leftSource.joinOn.isNone do
    unsupported "joined expression sources"
  let leftName := resolveTableName state leftSource.name
  let rightName := resolveTableName state originalRight.name
  let some left := state.database.findTable? leftName | throw s!"no such table: {leftSource.name}"
  let some right := state.database.findTable? rightName | throw s!"no such table: {originalRight.name}"
  let context ← joinContext leftSource originalRight leftName rightName left.schema right.schema
  unless context.leftName != context.rightName do throw "ambiguous join source names"
  let prepared ← joinScalarPrepare context select originalRight
  let where_ := prepared.select.where_
  let source := joinScalarReducedSource context prepared originalRight
  let (on, _) := match originalRight.joinOn with
    | none => (none, none)
    | some expression => CoreOrder.resolveJoinOnAliases (joinHasColumn context) select.columns.toList expression
  let on ← on.mapM (joinScalarBind context)
  let enabled ← if select.limit == some 0 || joinScalarKnownEmpty context prepared source then pure false
    else joinFixedConstantMatches context prepared source on
  let enabled ← if enabled && !source.leftJoin && !source.rightJoin then prepared.context.constantMatches on else pure enabled
  let (rows, ordered) ← if enabled then do
      let terms ← CoreOrder.resolve prepared.context prepared.select.columns.toList prepared.select.orderBy.toList
      let traversal := joinScalarTraversal context prepared source terms on
      let outerSide := if traversal.exchanged then CoreJoin.Side.right else .left
      let early := if source.rightJoin then [] else
        (where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
          (fun term => joinScalarOnlySide context prepared outerSide term && !prepared.context.constantExpression term)
      let plan := joinSearchPlan context prepared source traversal on
      let plan := { plan with early := early ++ plan.early }
      let left := if traversal.reverseLeft then left.rows.reverse else left.rows
      let right := if traversal.reverseRight then right.rows.reverse else right.rows
      let outer := if traversal.exchanged then right else left
      let inner := if traversal.exchanged then left else right
      let outer ← match traversal.root with
        | none => pure outer
        | some access => do
            let empty := CoreJoin.nullRow (if traversal.exchanged then context.leftSchema.columns.length else context.rightSchema.columns.length)
            pure ((← joinSearchCandidates context prepared source (!traversal.exchanged) empty access outer.zipIdx).rows.map Prod.fst)
      let inner := inner.zipIdx
      let rows ← joinSearchRows context prepared source plan traversal.exchanged inner outer
      pure (rows, traversal.ordered)
    else pure ([], false)
  if !prepared.select.groupBy.isEmpty then
    let inputs := rows.map (CoreJoin.projectRow (joinScalarInputs context))
    let (report, width) ← CoreGrouped.observe prepared.context prepared.select inputs
    return { result := { rows := report.rows }, width, error := report.error }
  let (result, width) ← joinScalarRun context prepared rows ordered
  return { result, width }

def joinScalarMaterializedResult (state : Core.State) (select : Select) : Except String (Core.Result × Nat) := do
  (← joinScalarMaterializedReport state select).toExcept

structure JoinStreamState where
  aggregates : Option (Array (CoreAggregate.Term × CoreAggregate.Accumulator)) := none
  reversed : List (List Core.Value) := []
  seen : List (List Core.Value) := []
  skip : Nat := 0
  remaining : Option Nat := none
  error : Option String := none

def JoinStreamState.stopped (state : JoinStreamState) : Bool :=
  state.error.isSome || state.remaining == some 0

def joinStreamStep (context : JoinContext) (prepared : JoinScalarPrepared)
    (expressions : List Expr) (state : JoinStreamState) (row : CoreJoin.JoinedRow) : JoinStreamState := Id.run do
  if state.stopped then return state
  let ctx := prepared.context
  let input := CoreJoin.projectRow (joinScalarInputs context) row
  let selected := ctx.matches input prepared.select.where_
  match selected with
  | .error message => return { state with error := some message }
  | .ok false => return state
  | .ok true =>
      if let some states := state.aggregates then
        match states.mapM (fun (term, accumulator) => do
            return (term, ← accumulator.ingest term ctx input)) with
        | .error message => return { state with error := some message }
        | .ok states => return { state with aggregates := some states, reversed := input :: state.reversed }
      if state.skip > 0 && !prepared.select.distinct then return { state with skip := state.skip - 1 }
      match ctx.projectRow input expressions with
      | .error message => return { state with error := some message }
      | .ok output =>
          if prepared.select.distinct && state.seen.any (CoreExpr.distinctEqual expressions output) then return state
          let state := { state with seen := Core.distinctRowKey output :: state.seen }
          if state.skip > 0 then return { state with skip := state.skip - 1 }
          return { state with reversed := output :: state.reversed, remaining := state.remaining.map (· - 1) }

def joinStreamRight (context : JoinContext) (prepared : JoinScalarPrepared) (source : TableRef) (plan : JoinSearchPlan)
    (expressions : List Expr) (exchanged : Bool) (outer : Core.Row) :
    List (Core.Row × Nat) → JoinStreamState → Bool → List Nat → JoinStreamState × Bool × List Nat
  | [], state, found, matched => (state, found, matched)
  | (inner, index) :: rest, state, found, matched =>
      if state.stopped then (state, found, matched)
      else
        let row := if exchanged then (inner, outer) else (outer, inner)
        match joinSearchMatches context prepared source plan row with
        | .error message => ({ state with error := some message }, found, matched)
        | .ok false => joinStreamRight context prepared source plan expressions exchanged outer rest state found matched
        | .ok true => joinStreamRight context prepared source plan expressions exchanged outer rest
            (joinStreamStep context prepared expressions state row) true (index :: matched)

def joinStreamSuffix (context : JoinContext) (prepared : JoinScalarPrepared)
    (expressions : List Expr) : List Core.Row → JoinStreamState → JoinStreamState
  | [], state => state
  | row :: rows, state =>
      if state.stopped then state else
      joinStreamSuffix context prepared expressions rows
        (joinStreamStep context prepared expressions state (CoreJoin.nullRow context.leftSchema.columns.length, row))

def joinStreamLeft (context : JoinContext) (prepared : JoinScalarPrepared) (source : TableRef)
    (expressions early : List Expr) (exchanged : Bool) (inner : List (Core.Row × Nat))
    (plan : JoinSearchPlan) :
    List Core.Row → JoinStreamState → List Nat → JoinStreamState
  | [], state, matched =>
      if source.rightJoin then joinStreamSuffix context prepared expressions
        ((inner.filter (fun (_, index) => !matched.contains index)).map Prod.fst) state else state
  | outer :: rest, state, matched =>
      if state.stopped then state
      else
        let input := CoreJoin.projectRow (joinScalarInputs context)
          (if exchanged then (CoreJoin.nullRow context.leftSchema.columns.length, outer)
            else (outer, CoreJoin.nullRow context.rightSchema.columns.length))
        match joinFixedMatches prepared input plan.fixed early with
        | .error message => { state with error := some message }
        | .ok false => joinStreamLeft context prepared source expressions early exchanged inner plan rest state matched
        | .ok true =>
            match joinSearchCandidates context prepared source exchanged outer plan.access inner with
            | .error message => { state with error := some message }
            | .ok candidates =>
                if candidates.halt then state else
                let (state, found, matched) := joinStreamRight context prepared source plan expressions exchanged outer candidates.rows state false matched
                let state := if !found && source.leftJoin then joinStreamStep context prepared expressions state
                    (outer, CoreJoin.nullRow context.rightSchema.columns.length) else state
                joinStreamLeft context prepared source expressions early exchanged inner plan rest state matched

/-- An aggregate output is produced only after all input steps finish. A
recorded input error wins over finalization, HAVING and result expressions. -/
def joinAggregateStreamFinish (ctx : CoreExpr.Context)
    (select : Select) (prepared : CoreAggregateHaving.Prepared)
    (state : JoinStreamState) : Except String JoinReadReport := do
  if let some message := state.error then throw message
  let some states := state.aggregates | unsupported "missing joined aggregate accumulators"
  let values ← states.mapM fun (term, accumulator) => accumulator.finish term
  let row ← CoreAggregateHaving.representative ctx prepared.results.terms state.reversed.reverse
  let selected ← prepared.matches ctx values row
  let rows ← if !selected || select.offset > 0 then pure []
    else do pure [← prepared.finish ctx values row]
  return { result := { rows }, width := prepared.results.expressions.length }

theorem joinAggregateStreamFinish_error (ctx : CoreExpr.Context) (select : Select)
    (prepared : CoreAggregateHaving.Prepared) (state : JoinStreamState) (message : String)
    (failed : state.error = some message) :
    joinAggregateStreamFinish ctx select prepared state = .error message := by
  simp only [joinAggregateStreamFinish, failed] <;> rfl

/-- Use the same join cursors, ON bookkeeping and early predicates as scalar
streaming. Each accepted pair steps every aggregate before visiting a new pair. -/
def joinAggregateStreamResult (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (traversal : JoinScalarTraversal) (on : Option Expr)
    (leftRows rightRows : List Core.Row) : Except String JoinReadReport := do
  let ctx := prepared.context
  let select := prepared.select
  if select.distinct then CoreExpr.validateDistinct (select.columns.toList.map (·.expr))
  let aggregate ← CoreAggregateHaving.prepare ctx select.columns.toList select.orderBy.toList select.having
  let _ ← select.where_.mapM ctx.validate
  let width := aggregate.results.expressions.length
  if select.limit == some 0 then return { width }
  let initial : JoinStreamState := {
    aggregates := some (aggregate.results.terms.map (fun term => (term, {}))) }
  let finish := joinAggregateStreamFinish ctx select aggregate
  if joinScalarKnownEmpty context prepared source then return ← finish initial
  unless ← joinFixedConstantMatches context prepared source on do return ← finish initial
  let right := if traversal.reverseRight then rightRows.reverse else rightRows
  let left := if traversal.reverseLeft then leftRows.reverse else leftRows
  let outerSide := if traversal.exchanged then CoreJoin.Side.right else .left
  let early := if source.rightJoin then [] else
    (select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
      (fun term => joinScalarOnlySide context prepared outerSide term && !ctx.constantExpression term)
  let plan := joinSearchPlan context prepared source traversal on
  let early := early ++ plan.early
  unless source.leftJoin || source.rightJoin do
    unless ← ctx.constantMatches on do return ← finish initial
  let outer := if traversal.exchanged then right else left
  let inner := if traversal.exchanged then left else right
  let outer ← match traversal.root with
    | none => pure outer
    | some access => do
        let empty := CoreJoin.nullRow (if traversal.exchanged then context.leftSchema.columns.length else context.rightSchema.columns.length)
        pure ((← joinSearchCandidates context prepared source (!traversal.exchanged) empty access outer.zipIdx).rows.map Prod.fst)
  let result := joinStreamLeft context prepared source [] early traversal.exchanged inner.zipIdx plan outer initial []
  finish result

def joinStreamPrepared (state : Core.State) (select : Select) : Except String JoinReadReport := do
  let (leftSource, originalRight) ← match select.sources.toList with
    | [left, right] => pure (left, right)
    | _ => unsupported "joined expression source count"
  unless leftSource.schema.isNone && leftSource.functionArgs.isNone && leftSource.subquerySql.isNone && originalRight.schema.isNone && originalRight.functionArgs.isNone && originalRight.subquerySql.isNone && leftSource.joinOn.isNone do
    unsupported "joined expression sources"
  let leftName := resolveTableName state leftSource.name
  let rightName := resolveTableName state originalRight.name
  let some left := state.database.findTable? leftName | throw s!"no such table: {leftSource.name}"
  let some right := state.database.findTable? rightName | throw s!"no such table: {originalRight.name}"
  let context ← joinContext leftSource originalRight leftName rightName left.schema right.schema
  unless context.leftName != context.rightName do throw "ambiguous join source names"
  let prepared ← joinScalarPrepare context select originalRight
  let source := joinScalarReducedSource context prepared originalRight
  let terms ← CoreOrder.resolve prepared.context prepared.select.columns.toList prepared.select.orderBy.toList
  let aggregate := !prepared.select.groupBy.isEmpty || prepared.select.columns.any (fun c => CoreAggregate.containsAggregate c.expr)
  let (on, _) := match originalRight.joinOn with
    | none => (none, none)
    | some expression => CoreOrder.resolveJoinOnAliases (joinHasColumn context) select.columns.toList expression
  let on ← on.mapM (joinScalarBind context)
  let traversal := joinScalarTraversal context prepared source terms on
  if !prepared.select.groupBy.isEmpty || (!aggregate && !terms.isEmpty && !traversal.ordered) then
    return ← joinScalarMaterializedReport state select
  if aggregate then
    return ← joinAggregateStreamResult context prepared source traversal on left.rows right.rows
  let ctx := prepared.context
  unless prepared.select.having.isNone do unsupported "HAVING requires an aggregate"
  let expressions ← ctx.projection prepared.select.columns.toList
  if prepared.select.distinct then CoreExpr.validateDistinct expressions
  let _ ← prepared.select.where_.mapM ctx.validate
  let _ ← terms.mapM (CoreOrder.validateTerm ctx)
  let width := expressions.length
  if select.limit == some 0 || joinScalarKnownEmpty context prepared source then return { width }
  unless ← joinFixedConstantMatches context prepared source on do return { width }
  let right := if traversal.reverseRight then right.rows.reverse else right.rows
  let left := if traversal.reverseLeft then left.rows.reverse else left.rows
  let outerSide := if traversal.exchanged then CoreJoin.Side.right else .left
  let early := if source.rightJoin then [] else
    (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
      (fun term => joinScalarOnlySide context prepared outerSide term && !ctx.constantExpression term)
  let plan := joinSearchPlan context prepared source traversal on
  let early := early ++ plan.early
  unless source.leftJoin || source.rightJoin do
    unless ← ctx.constantMatches on do return { width }
  let outer := if traversal.exchanged then right else left
  let inner := if traversal.exchanged then left else right
  let outer ← match traversal.root with
    | none => pure outer
    | some access => do
        let empty := CoreJoin.nullRow (if traversal.exchanged then context.leftSchema.columns.length else context.rightSchema.columns.length)
        pure ((← joinSearchCandidates context prepared source (!traversal.exchanged) empty access outer.zipIdx).rows.map Prod.fst)
  let inner := inner.zipIdx
  let initial : JoinStreamState := { skip := select.offset, remaining := select.limit }
  let result := joinStreamLeft context prepared source expressions early traversal.exchanged inner plan outer initial []
  return { result := { rows := result.reversed.reverse }, width, error := result.error }

/-- Preparation failures have no emitted prefix. Runtime failures in a streamed
scan retain exactly the rows produced before the failing step. -/
def joinScalarReadReport (state : Core.State) (select : Select) : JoinReadReport :=
  match joinStreamPrepared state select with
  | .ok report => report
  | .error message => { error := some message }

def joinScalarResult (state : Core.State) (select : Select) : Except String (Core.Result × Nat) :=
  (joinScalarReadReport state select).toExcept

theorem joinStreamStep_stopped (context : JoinContext) (prepared : JoinScalarPrepared)
    (expressions : List Expr) (state : JoinStreamState) (row : CoreJoin.JoinedRow)
    (stopped : state.stopped = true) :
    joinStreamStep context prepared expressions state row = state := by
  simp [joinStreamStep, stopped]

theorem joinStreamRight_stopped (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (expressions : List Expr) (exchanged : Bool) (outer : Core.Row)
    (rows : List (Core.Row × Nat)) (state : JoinStreamState) (found : Bool) (matched : List Nat)
    (stopped : state.stopped = true) :
    joinStreamRight context prepared source plan expressions exchanged outer rows state found matched =
      (state, found, matched) := by
  cases rows <;> simp [joinStreamRight, stopped]

theorem joinStreamSuffix_stopped (context : JoinContext) (prepared : JoinScalarPrepared)
    (expressions : List Expr) (rows : List Core.Row) (state : JoinStreamState)
    (stopped : state.stopped = true) :
    joinStreamSuffix context prepared expressions rows state = state := by
  cases rows <;> simp [joinStreamSuffix, stopped]

theorem joinStreamLeft_stopped (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (expressions early : List Expr) (exchanged : Bool)
    (inner : List (Core.Row × Nat)) (plan : JoinSearchPlan) (outer : List Core.Row) (state : JoinStreamState)
    (matched : List Nat) (stopped : state.stopped = true) :
    joinStreamLeft context prepared source expressions early exchanged inner plan outer state matched = state := by
  cases outer <;> simp [joinStreamLeft, stopped, joinStreamSuffix_stopped context prepared expressions _ state stopped]

def executeJoinScalar (state : Core.State) (select : Select) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> joinScalarResult state select

theorem executeJoinScalar_preserves_state {state : Core.State} {select : Select}
    {result : SelectExecution} (success : executeJoinScalar state select = .ok result) :
    result.state = state := by
  unfold executeJoinScalar at success
  cases executed : joinScalarResult state select with
  | error message => simp [executed, Functor.map, Except.map] at success
  | ok output =>
      simp [executed, Functor.map, Except.map] at success
      cases success
      rfl

/-- Extend only two-source queries. Successful existing execution remains
authoritative, and all other source shapes keep their original error behavior. -/
def executeSelectBaseComplete (state : Core.State) (select : Select) : Except String SelectExecution :=
  if select.sources.size != 2 then executeSelectBase state select
  else match executeSelectBase state select with
    | .ok result => .ok result
    | .error _ => executeJoinScalar state select

theorem executeSelectBaseComplete_existing (state : Core.State) (select : Select)
    (result : SelectExecution) (success : executeSelectBase state select = .ok result) :
    executeSelectBaseComplete state select = .ok result := by
  simp [executeSelectBaseComplete, success]

theorem joinScalarRowsM_pure (context : JoinContext) (prepared : JoinScalarPrepared) (source : TableRef)
    (left right : List Core.Row) (pureOn : prepared.onExpression = none) :
    joinScalarRowsM context prepared source left right =
      .ok (joinScalarRows context source prepared.on left right) := by
  simp [joinScalarRowsM, pureOn, pure, Except.pure]

theorem joinScalarRowsM_exchange_inner (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (left right : List Core.Row)
    (noLeft : source.leftJoin = false) (noRight : source.rightJoin = false) :
    joinScalarRowsM context prepared source left right true =
      (right.flatMap (fun r => left.map (fun l => (l, r)))).filterM
        (joinScalarMatches context prepared false) := by
  simp [joinScalarRowsM, noLeft, noRight]

/-- Bind identifiers and expand stars before resolving each output column's
explicit or declared collation. Joined stars expand with BINARY metadata;
wrapped atoms retain their original explicit and inherited collation. -/
def baseResultCollations (state : Core.State) (select : Select) (wrappedValues : Bool := false) :
    Except String (List (Option String)) := do
  if let some rows := select.valueRows then
    return SQLite.Values.collations rows.toList wrappedValues
  match select.sources.toList with
  | [] => return select.columns.toList.map (fun column => SQLite.ExprCollation.effectiveName column.expr)
  | [source] =>
      let some stored := state.database.findTable? (resolveTableName state source.name) | throw s!"no such table: {source.name}"
      let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
      let expanded ← CoreOrder.expandResults ctx select.columns.toList
      return expanded.map (fun column => SQLite.ExprCollation.effectiveName (ctx.bindNames column.expr))
  | [leftSource, rightSource] =>
      let some left := state.database.findTable? (resolveTableName state leftSource.name) | throw s!"no such table: {leftSource.name}"
      let some right := state.database.findTable? (resolveTableName state rightSource.name) | throw s!"no such table: {rightSource.name}"
      let leftName := resolveTableName state leftSource.name
      let rightName := resolveTableName state rightSource.name
      let context ← joinContext leftSource rightSource leftName rightName left.schema right.schema
      match joinAliasQuery { select with orderBy := #[], offset := 0 }
          leftName rightName left.schema right.schema left.rows right.rows with
      | .ok _ => return (← joinWrappedColumns context select.columns.toList).2
      | .error _ =>
          let prepared ← joinScalarPrepare context { select with orderBy := #[], offset := 0 } rightSource
          let _ ← joinScalarRun context { prepared with select := { prepared.select with limit := some 0 } } []
          return prepared.select.columns.toList.map (fun column => SQLite.ExprCollation.effectiveName column.expr)
  | _ => unsupported "compound source shape"

/-- multiSelectCollSeq takes the first arm that supplies a collation for each
output position. An unused later unknown name must not replace an earlier one. -/
def resultCollationsFuel : Nat → Core.State → Select → Except String (List (Option String))
  | 0, _, _ => .error "compound collation depth exhausted"
  | fuel + 1, state, select => do
      let first ← baseResultCollations state select
      select.compounds.toList.foldlM (fun current (operation, arm) => do
        let next ← if arm.valueRows.isSome then baseResultCollations state arm true
          else resultCollationsFuel fuel state arm
        unless current.length == next.length do
          throw (CoreCompound.widthError operation)
        return current.zipWith (fun left right => left.orElse fun _ => right) next) first

/-- Expand source columns for compound ORDER BY alias/expression matching. -/
def compoundTailArm (state : Core.State) (select : Select) : Except String CoreCompoundTail.Arm := do
  match select.sources.toList with
  | [] =>
      return { columns := select.columns.toList, context := some {
        schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" } }
  | [source] =>
      let some stored := state.database.findTable? (resolveTableName state source.name) | throw s!"no such table: {source.name}"
      let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
      return { columns := ← CoreOrder.expandResults ctx select.columns.toList, context := some ctx }
  | [leftSource, rightSource] =>
      let leftName := resolveTableName state leftSource.name
      let rightName := resolveTableName state rightSource.name
      let some left := state.database.findTable? leftName | throw s!"no such table: {leftSource.name}"
      let some right := state.database.findTable? rightName | throw s!"no such table: {rightSource.name}"
      let context ← joinContext leftSource rightSource leftName rightName left.schema right.schema
      return {
        columns := ← joinCompoundColumns context select.columns.toList
        context := none
        bindExpression := some (fun expression => joinCompoundBind context
          (CoreOrder.resolveAliasesWith (joinHasColumn context) select.columns.toList expression)) }
  | _ => unsupported "compound source shape"

def compoundValuesArms (rows : Array (Array Expr)) (wrapped : Bool) : List CoreCompoundTail.Arm :=
  (SQLite.Values.projections rows.toList wrapped).map fun (row, source) =>
    { columns := row.toList.zipIdx.map (fun (expression, index) =>
        if source then { expr := .column none s!"column{index + 1}", alias := some s!"column{index + 1}" }
        else { expr := expression }), context := none }

def compoundTailArmsFuel : Nat → Core.State → Select → Bool → Except String (List CoreCompoundTail.Arm)
  | 0, _, _, _ => .error "compound ORDER BY depth exhausted"
  | fuel + 1, state, select, wrapped => do
      let first ← if let some rows := select.valueRows then pure (compoundValuesArms rows wrapped)
        else (fun arm => [arm]) <$> compoundTailArm state select
      let others ← select.compounds.toList.mapM (fun arm => compoundTailArmsFuel fuel state arm.2 true)
      return first ++ others.flatten

/-- Leaf execution keeps ORDER BY's top-N evaluation discipline. Aggregates,
groups and bounded joins already produce their output rows in their own
executor, so result-slot ordering is applied to those rows. The second return
value counts rows consumed by OFFSET for concatenated UNION ALL arms. -/
def compoundTailLeaf (run : Core.State → Select → Except String SelectExecution)
    (state : Core.State) (select : Select) (terms : List CoreCompoundTail.Term)
    (offset : Nat) (limit : Option Nat) (wrappedValues : Bool := false) : Except String (List (List Core.Value) × Nat) := do
  if let some rows := select.valueRows then
    if terms.isEmpty then
      if wrappedValues && rows.size > 1 then
        let result ← run state { select with orderBy := #[], offset := 0, limit := limit.map (· + offset) }
        return (result.result.rows.drop offset, min offset rows.size)
      let result ← run state { select with orderBy := #[], offset, limit }
      return (result.result.rows, min offset rows.size)
    else
      let result ← run state { select with orderBy := #[], offset := 0, limit := none }
      let sorted := CoreCompoundTail.sort terms result.result.rows
      return (CoreCompoundTail.window offset limit sorted, min offset sorted.length)
  let aggregate := select.columns.any (fun c => CoreAggregate.containsAggregate c.expr)
  if !terms.isEmpty then
    if !aggregate && select.groupBy.isEmpty && select.sources.size ≤ 1 then
      let result ← run state { select with orderBy := (terms.map CoreCompoundTail.orderTerm).toArray, offset, limit }
      return (result.result.rows, 0)
    let result ← run state { select with orderBy := #[], offset := 0, limit := none }
    let sorted := CoreCompoundTail.sort terms result.result.rows
    return (CoreCompoundTail.window offset limit sorted, min offset sorted.length)
  if offset > 0 && !select.distinct && select.groupBy.isEmpty && !aggregate && select.sources.size ≤ 1 then
    -- Count skipped source rows without evaluating their output expressions.
    -- Supported scalar functions are deterministic; validation of the original
    -- projections has already happened before any leaf executes.
    let skipped ← run state { select with columns := #[{ expr := .literal (.integer 1) }], orderBy := #[], offset := 0, limit := some offset }
    let count := skipped.result.rows.length
    if count < offset then return ([], count)
    let result ← run state { select with orderBy := #[], offset, limit }
    return (result.result.rows, count)
  if aggregate && select.groupBy.isEmpty then
    let result ← run state { select with orderBy := #[], offset, limit }
    return (result.result.rows, min offset 1)
  let result ← run state { select with orderBy := #[], offset := 0, limit := limit.map (· + offset) }
  return (CoreCompoundTail.window offset limit result.result.rows, min offset result.result.rows.length)

/-- Reverse-arm recursion represents SQL's left-associated compound tree.
Only UNION ALL propagates a finite bound into its input arms. Set operations
complete the merge key with the remaining output columns. -/
def compoundTailPlan (run : Core.State → Select → Except String SelectExecution)
    (state : Core.State) (kinds : List SQLite.Collation.Kind) (base : Select) :
    List (CompoundOp × Select) → List CoreCompoundTail.Term → Nat → Option Nat →
      Except String (List (List Core.Value) × Nat)
  | [], terms, offset, limit => compoundTailLeaf run state base terms offset limit
  | (operation, arm) :: prior, terms, offset, limit => do
      if operation == .unionAll && terms.isEmpty then
        let (left, skipped) ← compoundTailPlan run state kinds base prior [] offset limit
        let remaining := limit.map (· - left.length)
        if remaining == some 0 then return (left, skipped)
        let (right, moreSkipped) ← compoundTailLeaf run state arm [] (offset - skipped) remaining true
        return (left ++ right, skipped + moreSkipped)
      let ordering := if operation == .unionAll then terms else CoreCompoundTail.complete kinds terms
      let capacity := if operation == .unionAll then limit.map (· + offset) else none
      let (left, _) ← compoundTailPlan run state kinds base prior ordering 0 capacity
      if left.isEmpty && (operation == .intersect || operation == .except) then return ([], 0)
      let (right, _) ← compoundTailLeaf run state arm ordering 0 capacity true
      let rows := CoreCompoundTail.merge kinds operation ordering left right
      return (CoreCompoundTail.window offset limit rows, min offset rows.length)

def compoundTailResult (run : Core.State → Select → Except String SelectExecution)
    (state : Core.State) (select : Select) : Except String (Core.Result × Nat) := do
  let names ← resultCollationsFuel select.compoundHeight state select
  let usesSets := select.compounds.any (fun arm => arm.1 != .unionAll)
  let kinds ← if usesSets then names.mapM (fun name => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName name))
    else pure (names.map (fun name => (SQLite.ExprCollation.ofName name).getD .binary))
  let bindings ← compoundTailArmsFuel select.compoundHeight state select false
  let terms ← select.orderBy.toList.mapM (CoreCompoundTail.resolve bindings names)
  let base := { select with compounds := #[], orderBy := #[], limit := none, offset := 0 }
  for (operation, arm) in ((select.compounds[0]?.map Prod.fst).getD .unionAll, base) :: select.compounds.toList do
    let validated ← run state { arm with orderBy := #[], limit := some 0, offset := 0 }
    unless validated.width == names.length do
      throw (CoreCompound.widthError operation)
  if select.limit == some 0 then return ({}, names.length)
  let externalSort := usesSets && select.orderBy.any (fun term => (SQLite.ExprCollation.name term.expr).isSome)
  let rows ← if externalSort then do
      let (rows, _) ← compoundTailPlan run state kinds base select.compounds.toList.reverse [] 0 none
      pure (CoreCompoundTail.window select.offset select.limit (CoreCompoundTail.sort terms rows))
    else do
      let (rows, _) ← compoundTailPlan run state kinds base select.compounds.toList.reverse terms select.offset select.limit
      pure rows
  return ({ rows }, names.length)

def executeCompoundTail (run : Core.State → Select → Except String SelectExecution)
    (state : Core.State) (select : Select) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> compoundTailResult run state select

theorem executeCompoundTail_preserves_state
    {run : Core.State → Select → Except String SelectExecution}
    {state : Core.State} {select : Select} {execution : SelectExecution}
    (success : executeCompoundTail run state select = .ok execution) : execution.state = state := by
  unfold executeCompoundTail at success
  cases result : compoundTailResult run state select with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

def executeSelectFuel : Nat → Core.State → Select → Except String SelectExecution
  | 0, _, _ => .error "compound SELECT exceeds its verified recursion bound"
  | fuel + 1, state, select => do
      if !(select.compounds.isEmpty ||
          (select.orderBy.isEmpty && select.limit.isNone && select.offset = 0)) then
        return ← executeCompoundTail (executeSelectFuel fuel) state select
      if requiresCompoundCollation select then
        let names ← resultCollationsFuel select.compoundHeight state select
        let kinds ← if select.compounds.any (fun arm => arm.1 != .unionAll) then
            names.mapM (fun name => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName name))
          else pure []
        let base ← executeSelectBaseComplete state { select with compounds := #[] }
        let rec executeCollatedArms (current : SelectExecution) :
            List (CompoundOp × Select) → Except String SelectExecution
          | [] => .ok current
          | (operation, arm) :: arms => do
              let next ← executeSelectFuel fuel current.state arm
              unless current.width == next.width do
                throw (CoreCompound.widthError operation)
              let combined : SelectExecution := {
                state := next.state
                result := { rows := CoreCompound.combineCollated kinds operation current.result.rows next.result.rows }
                width := current.width }
              executeCollatedArms combined arms
        return ← executeCollatedArms base select.compounds.toList
      let base ← executeSelectBaseComplete state { select with compounds := #[] }
      let rec executeArms (current : SelectExecution) :
          List (CompoundOp × Select) → Except String SelectExecution
        | [] => .ok current
        | (operation, arm) :: arms => do
            let next ← executeSelectFuel fuel current.state arm
            unless current.width = next.width do
              throw (CoreCompound.widthError operation)
            let combined : SelectExecution := {
              state := next.state
              result := { rows := (combineRows
                (CoreOptimizerBridge.optimizeCompoundOp operation)
                current.result.rows next.result.rows) }
              width := current.width }
            executeArms combined arms
      executeArms base select.compounds.toList

def executeSelect (state : Core.State) (select : Select) :
    Except String SelectExecution :=
  executeSelectFuel select.compoundHeight state select

/-- Read-only observation retains a typed row prefix separately from the
ordinary success/error result. It cannot turn a failure into a successful read. -/
structure ObservedSelect where
  execution : SelectExecution
  error : Option String := none

def ObservedSelect.toExcept (report : ObservedSelect) : Except String SelectExecution :=
  match report.error with
  | none => .ok report.execution
  | some message => .error message

def executeSelectBaseObserved (state : Core.State) (select : Select) : ObservedSelect :=
  match executeSelectBase state select with
  | .ok execution => { execution }
  | .error _ =>
      let report := joinScalarReadReport state select
      { execution := ⟨state, report.result, report.width⟩, error := report.error }

theorem executeSelectBaseObserved_refines (state : Core.State) (select : Select)
    (twoSources : select.sources.size = 2) :
    (executeSelectBaseObserved state select).toExcept = executeSelectBaseComplete state select := by
  cases base : executeSelectBase state select with
  | ok execution => simp [executeSelectBaseObserved, ObservedSelect.toExcept,
      executeSelectBaseComplete, twoSources, base]
  | error message =>
      cases failure : (joinScalarReadReport state select).error <;>
        simp [executeSelectBaseObserved, ObservedSelect.toExcept, executeSelectBaseComplete,
          twoSources, base, executeJoinScalar, joinScalarResult, JoinReadReport.toExcept,
          failure, Functor.map, Except.map]

theorem executeSelect_without_compounds (state : Core.State) (select : Select)
    (noCompounds : select.compounds = #[]) :
    executeSelect state select = executeSelectBaseComplete state select := by
  have height : select.compoundHeight = 1 := by
    rw [show select.compoundHeight = selectCompoundListHeight select.compounds.toList + 1 by
      cases select
      rfl, noCompounds]
    rfl
  have cleared : { select with compounds := #[] } = select := by
    cases select
    simp_all
  cases base : executeSelectBaseComplete state select <;>
    simp [executeSelect, height, executeSelectFuel, requiresCompoundCollation, noCompounds,
      cleared, base, executeSelectFuel.executeArms, bind, Except.bind]

/-- Add observation only to a complete two-source leaf. Compound operators keep
owning their materialization and result publication. -/
def observeJoinedSelect? (state : Core.State) (select : Select) : Option ObservedSelect :=
  if select.sources.size = 2 ∧ select.compounds = #[] then
    some (executeSelectBaseObserved state select)
  else none

theorem observeJoinedSelect_refines (state : Core.State) (select : Select)
    (report : ObservedSelect) (observed : observeJoinedSelect? state select = some report) :
    report.toExcept = executeSelect state select := by
  unfold observeJoinedSelect? at observed
  split at observed
  next supported =>
    cases Option.some.inj observed
    rw [executeSelectBaseObserved_refines state select supported.1,
      executeSelect_without_compounds state select supported.2]
  next unsupported => simp at observed

/-- Prepare a single-table read using the same bound sources as execution.
Ordered groups retain their emitted prefix; ungrouped aggregates remain atomic. -/
def singleSourceReadPrepared (state : Core.State) (select : Select) : Except String ScalarReadReport := do
  unless select.sources.size == 1 do unsupported "single-source read observation"
  let some source := select.sources[0]? | unsupported "single-source observation source"
  unless source.schema.isNone && source.functionArgs.isNone && source.subquerySql.isNone && source.joinOn.isNone do
    unsupported "single-source observation source"
  let some stored := state.database.findTable? (resolveTableName state source.name) |
    throw s!"no such table: {source.name}"
  if !select.groupBy.isEmpty then
    let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
    let (report, width) ← CoreGrouped.observe ctx select (stored.rows.map (·.values))
    return { result := { rows := report.rows }, width, error := report.error }
  unless select.having.isNone &&
      !select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) do
    unsupported "single-source aggregate observation"
  let select ← if selectNamesBound stored.schema source select then pure select else do
    let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
    unless select.where_.any (CoreOrder.needsAliases ctx select.columns.toList) do
      if let some message := selectResolutionError stored.schema source select then throw message
      unsupported "unbound SELECT name"
    unless selectNamesBound stored.schema source { select with where_ := none } do
      if let some message := selectResolutionError stored.schema source { select with where_ := none } then throw message
      unsupported "unbound SELECT result or ordering name"
    pure { select with where_ := select.where_.map (CoreOrder.resolveAliases ctx select.columns.toList) }
  filteredSelectReadPrepared state select source stored

def singleSourceReadReport (state : Core.State) (select : Select) : ScalarReadReport :=
  match singleSourceReadPrepared state select with
  | .ok report => report
  | .error message => { error := some message }

/-- Successful reads retain the existing optimized file route. On a failed
single-source read, publish its prefix only when the observation
reproduces that same failure. The original execution remains authoritative;
this consistency check cannot admit an unsupported query or suppress an error. -/
def observeSingleSelect? (state : Core.State) (select : Select) : Option ObservedSelect :=
  if select.sources.size = 1 ∧ select.compounds = #[] ∧ simpleQuery? state select = none then
    match executeSelectBase state select with
    | .ok _ => none
    | .error message =>
        let report := singleSourceReadReport state select
        if report.error = some message then
          some { execution := ⟨state, report.result, report.width⟩, error := report.error }
        else none
  else none

theorem observeSingleSelect_refines (state : Core.State) (select : Select)
    (report : ObservedSelect) (observed : observeSingleSelect? state select = some report) :
    report.toExcept = executeSelect state select := by
  unfold observeSingleSelect? at observed
  split at observed
  next supported =>
    cases base : executeSelectBase state select with
    | ok execution => simp [base] at observed
    | error message =>
        simp only [base] at observed
        split at observed
        next sameFailure =>
          cases Option.some.inj observed
          rw [executeSelect_without_compounds state select supported.2.1]
          simp [ObservedSelect.toExcept, sameFailure, executeSelectBaseComplete, supported.1, base]
        next different => simp at observed
  next unsupported => simp at observed

/-- A translated direct Core query keeps the existing file/index route
without evaluating the ordinary SELECT merely to obtain an observation. -/
theorem observeSingleSelect_direct (state : Core.State) (select : Select)
    (query : String × Core.Query) (direct : simpleQuery? state select = some query) :
    observeSingleSelect? state select = none := by
  simp [observeSingleSelect?, direct]

def observeReadSelect? (state : Core.State) (select : Select) : Option ObservedSelect :=
  (observeJoinedSelect? state select).orElse (fun _ => observeSingleSelect? state select)

theorem observeReadSelect_refines (state : Core.State) (select : Select)
    (report : ObservedSelect) (observed : observeReadSelect? state select = some report) :
    report.toExcept = executeSelect state select := by
  cases joined : observeJoinedSelect? state select with
  | none =>
      apply observeSingleSelect_refines state select report
      simpa [observeReadSelect?, joined] using observed
  | some result =>
      have equal : result = report := by simpa [observeReadSelect?, joined] using observed
      subst result
      exact observeJoinedSelect_refines state select report joined

/-- A declared non-rowid key also needs the allocate-before-delete REPLACE
trace, even when its automatic index is the only unique index. -/
def hasReplaceKeys (stored : Core.Table) : Bool :=
  (stored.schema.hasHiddenRowid && stored.schema.declaredPrimaryKey?.isSome) ||
    stored.indexes.any (·.unique) || stored.schema.columns.any (fun column => column.notNull && column.defaultValue.isSome)

/-- Allocate the replacement rowid against the original table, then remove
all rows conflicting with the primary key or any explicit UNIQUE index. -/
def uniqueReplacePlan (stored : Core.Table) (values : List Core.Value) :
    Except String (List Core.Command) := do
  CoreNullConflict.validate stored.schema (List.range stored.schema.columns.length) (some .replace)
  let some values ← CoreNullConflict.prepare stored.schema values false (some .replace)
    | throw "unexpected ignored REPLACE row"
  let row ← stored.createRow values
  let declared := stored.findDeclaredPrimary? row
  let conflicts := stored.rows.filter fun existing =>
    existing.rowid == row.rowid || declared.any (fun old => old.rowid == existing.rowid) ||
      stored.indexes.any (fun index => index.rowConflict row existing)
  let deletes := conflicts.map fun old => Core.Command.deleteWhere stored.schema.name
    (some (.equal stored.schema.primaryKey (.integer old.rowid)))
  return deletes ++ [.insert stored.schema.name row.values]

def replaceUniqueRows (state : Core.State) (table : String)
    (schema : Core.Schema) (columns : Option (Array String))
    (inputs : List (Array Expr)) (evaluateAll : Bool := false) :
    Except String (Core.State × List Core.Result) :=
  match inputs with
  | [] => .ok (state, [])
  | expressions :: rows => do
      let values ← inputRowValues schema columns evaluateAll expressions
      let stored ← match state.database.findTable? table with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      let commands ← uniqueReplacePlan stored values
      let (next, _) ← runCoreCommands state commands
      let (finalState, results) ← replaceUniqueRows next table schema columns rows evaluateAll
      return (finalState, { changes := 1 } :: results)

/-- Validate target arity even if the source SELECT yields no rows. -/
def checkInsertSelectColumns (schema : Core.Schema) (columns : Option (Array String))
    (width : Nat) (implicitWidth : Option Nat := none) : Except String Unit := do
  if let some expected := implicitWidth then
    unless width == expected do
      throw s!"table {schema.name} has {expected} columns but {width} values were supplied"
    return ()
  match columns with
  | none =>
      unless width == schema.visibleColumns.length do
        throw s!"table {schema.name} has {schema.visibleColumns.length} columns but {width} values were supplied"
  | some names =>
      let _ ← names.toList.mapM (column schema)
      unless width == names.size do throw s!"{width} values for {names.size} columns"

/-- Convert an already evaluated source row without rendering SQL text. This
retains storage classes and malformed TEXT bytes through the existing bridge. -/
def selectedRowExpressions (values : List Core.Value) : Except String (Array Expr) := do
  let values ← values.mapM CoreExpr.value
  return (values.map (fun value => Expr.literal value)).toArray

def insertSelection (state : Core.State) (table : String) (stored : Core.Table)
    (columns : Option (Array String)) (replacing : Bool)
    (rows : List (Array Expr)) : Except String (Core.State × List Core.Result) :=
  if replacing && hasReplaceKeys stored then
    replaceUniqueRows state table stored.schema columns rows
  else insertRows state table stored.schema columns replacing rows

theorem insertSelection_empty (state : Core.State) (table : String) (stored : Core.Table)
    (columns : Option (Array String)) (replacing : Bool) :
    insertSelection state table stored columns replacing [] = .ok (state, []) := by
  unfold insertSelection
  split <;> rfl

/-- Constant omitted defaults are initialized even for an empty SELECT source.
Replacement defaults are prepared without executing their runtime expressions. -/
def prepareInsertSelectionDefaults (schema : Core.Schema) (columns : Option (Array String))
    (conflict : ConflictAction) : Except String Unit := do
  if let some names := columns then
    let positions ← names.toList.mapM (column schema)
    for (target, position) in schema.columns.zipIdx do
      unless positions.contains position do discard <| target.defaultForInsert
  if conflict == .default || conflict == .replace then
    CoreNullConflict.validate schema (List.range schema.columns.length) (if conflict == .replace then some .replace else none)

/-- Evaluate the SELECT against the pre-statement database before inserting
its rows, including when the source is the destination table. All writes then
use the ordinary INSERT affinity, rowid and conflict-policy machinery. -/
def executeInsertSelect (state : Core.State) (table : String)
    (columns : Option (Array String)) (query : Select) (conflict : ConflictAction) :
    Except String (Core.State × List Core.Result) := do
  unless conflict == .default || conflict == .abort || conflict == .replace || conflict == .ignore do
    throw "unsupported general verified-MVP SQL: INSERT conflict policy"
  let tableName := resolveTableName state table
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  let selection ← executeSelect state query
  checkInsertSelectColumns stored.schema columns selection.width
  prepareInsertSelectionDefaults stored.schema columns conflict
  let rows ← selection.result.rows.mapM selectedRowExpressions
  if conflict == .default && CoreDefaultConflict.active stored.schema then
    schemaInsertRows state tableName stored.schema columns rows
  else if conflict == .ignore then ignoreInsertRows state tableName stored.schema columns rows
  else insertSelection state tableName stored columns (conflict == .replace) rows

theorem checkInsertSelectColumns_all {schema : Core.Schema} {width : Nat}
    (same : width = schema.visibleColumns.length) :
    checkInsertSelectColumns schema none width = .ok () := by
  simp [checkInsertSelectColumns, same, pure, Except.pure]

/-- Materialize RETURNING immediately for each accepted insertion. REPLACE
may later delete that row, but it must not erase its already collected output.
Ignored rows produce no output and do not evaluate RETURNING expressions. -/
def insertReturningValues (state : Core.State) (tableName : String) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (cells : List CoreReturning.Cell)
    (preparation : Option RowPreparation := none) :
    Except String (Core.State × Option (List Core.Value)) := do
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {tableName}"
  let some input ← (match preparation with
    | none => pure (some ({ cells, converted := List.range stored.schema.columns.length } : RowInput))
    | some prepare => prepare.row state stored conflict { cells, converted := List.range stored.schema.columns.length })
    | return (state, none)
  let cells := input.cells
  let values := cells.map (·.value)
  if conflict == .default then
    CoreDefaultConflict.validate stored none
    let some cells ← CoreReturning.prepareValues stored.schema cells false | return (state, none)
    let prepared ← CoreDefaultConflict.plan stored (cells.map (·.value)) none
    match prepared with
    | none => return (state, none)
    | some (row, trace) =>
        let (next, _) ← runCoreCommands state trace
        let output ← CoreReturning.project ctx (CoreReturning.withValues cells row.values)
          (projection.map (CoreLastInsert.bind next))
        return (next.recordForeignWrite tableName row.rowid none, some output)
  if conflict == .ignore then
    unless ← CoreInsertIgnore.shouldInsert stored values do return (state, none)
  let cells ← if conflict == .replace || conflict == .abort then do
      let some prepared ← CoreReturning.prepareValues stored.schema cells false
        (some (if conflict == .replace then .replace else .abort))
        | throw "unexpected ignored checked insertion"
      pure prepared
    else pure cells
  let row ← stored.createRow (cells.map (·.value))
  let trace ← if conflict == .replace then uniqueReplacePlan stored row.values
    else pure [Core.Command.insert tableName row.values]
  let (next, _) ← runCoreCommands state trace
  let output ← CoreReturning.project ctx (CoreReturning.withValues cells row.values)
          (projection.map (CoreLastInsert.bind next))
  return (next.recordForeignWrite tableName row.rowid none, some output)

/-- Only omitted target fields share default registers. Source values and
NOT NULL replacement defaults are evaluated in their own row registers. -/
def insertDefaultRegisters (schema : Core.Schema) (columns : Option (Array String))
    (input : Array Expr) (cells : List CoreReturning.Cell) : List (Option CoreReturning.Cell) :=
  let supplied := if input.isEmpty then [] else
    match columns with
    | none => schema.visibleColumnIndices
    | some names => names.toList.filterMap schema.column?
  cells.zipIdx.map fun (value,index) => if supplied.contains index then none else some value

def insertReturningStep (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (input : Array Expr)
    (evaluateAll : Bool) (defaults : List (Option CoreReturning.Cell))
    (preparation : Option RowPreparation := none) :
    Except String (Core.State × Option (List Core.Value) × List (Option CoreReturning.Cell)) := do
  let cells ← inputRowValuesTyped schema columns evaluateAll (input.map (CoreLastInsert.bind state)) defaults
  let (next, output) ← insertReturningValues state tableName conflict ctx projection cells preparation
  let defaults := if output.isSome then insertDefaultRegisters schema columns input cells else defaults
  return (next, output, defaults)

def insertReturningRow (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (input : Array Expr)
    (evaluateAll : Bool := false) (preparation : Option RowPreparation := none) :
    Except String (Core.State × Option (List Core.Value)) :=
  (fun result => (result.1,result.2.1)) <$>
    insertReturningStep state tableName schema columns conflict ctx projection input evaluateAll [] preparation

theorem insertReturningRow_ignored (state : Core.State) (tableName : String)
    (schema : Core.Schema) (columns : Option (Array String)) (ctx : CoreExpr.Context)
    (projection : List Expr) (input : Array Expr) (values : List CoreReturning.Cell) (stored : Core.Table)
    (converted : rowValuesTyped schema columns (input.map (CoreLastInsert.bind state)) = .ok values)
    (found : state.database.findTable? tableName = some stored)
    (skip : CoreInsertIgnore.shouldInsert stored (values.map (·.value)) = .ok false) :
    insertReturningRow state tableName schema columns .ignore ctx projection input = .ok (state, none) := by
  simp [insertReturningRow, insertReturningStep, inputRowValuesTyped, insertReturningValues,
    converted, found, skip, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

def insertReturningRows (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr)
    (inputs : List (Array Expr)) (evaluateAll : Bool := false)
    (defaults : List (Option CoreReturning.Cell) := []) (preparation : Option RowPreparation := none) :
    Except String (Core.State × List (List Core.Value)) :=
  match inputs with
  | [] => .ok (state, [])
  | input :: inputs => do
      let (next, output, defaults) ← insertReturningStep state tableName schema columns conflict
        ctx projection input evaluateAll defaults preparation
      let (finalState, outputs) ← insertReturningRows next tableName schema columns conflict
        ctx projection inputs evaluateAll defaults preparation
      return (finalState, output.toList ++ outputs)

theorem insertReturningRows_length_le (state : Core.State) (tableName : String)
    (schema : Core.Schema) (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (inputs : List (Array Expr))
    (next : Core.State) (outputs : List (List Core.Value)) (evaluateAll : Bool)
    (defaults : List (Option CoreReturning.Cell))
    (success : insertReturningRows state tableName schema columns conflict ctx projection inputs evaluateAll defaults = .ok (next, outputs)) :
    outputs.length ≤ inputs.length := by
  induction inputs generalizing state next outputs defaults with
  | nil =>
      simp [insertReturningRows] at success
      rcases success with ⟨_, rfl⟩
      simp
  | cons input inputs ih =>
      cases head : insertReturningStep state tableName schema columns conflict ctx projection input evaluateAll defaults with
      | error message => simp [insertReturningRows, head, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨middle, output, registers⟩
          cases tail : insertReturningRows middle tableName schema columns conflict ctx projection inputs evaluateAll registers with
          | error message => simp [insertReturningRows, head, tail, bind, Except.bind] at success
          | ok pair =>
              rcases pair with ⟨finalState, more⟩
              simp [insertReturningRows, head, tail, bind, Except.bind, pure, Except.pure] at success
              rcases success with ⟨_, rfl⟩
              have bound := ih middle finalState more registers tail
              cases output <;> simp_all <;> omega

def executeInsertReturning (state : Core.State) (table : String) (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) (conflict : ConflictAction) (returning : Array ResultColumn)
    (preparation : Option RowPreparation := none) :
    Except String (Core.State × List Core.Result) := do
  unless conflict == .default || conflict == .abort || conflict == .replace || conflict == .ignore do
    throw "unsupported general verified-MVP SQL: INSERT conflict policy"
  let tableName := resolveTableName state table
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := tableName }
  let targets ← prepareInsertTargets columns source preparation
  let columns := targets.columns
  if let .inl rows := source then CoreInsertPrepare.check stored.schema columns rows targets.implicitWidth
  let projection ← CoreLastInsert.prepareReturning state ctx returning.toList
  let inputs ← match source with
    | .inl rows => pure (if returning.isEmpty then rows.toList else
        rows.toList.map (·.map (CoreLastInsert.bind state)))
    | .inr query => do
        let selection ← executeSelect state query
        checkInsertSelectColumns stored.schema columns selection.width targets.implicitWidth
        prepareInsertSelectionDefaults stored.schema columns conflict
        selection.result.rows.mapM selectedRowExpressions
  let evaluateAll := match source with
    | .inl rows => 1 < rows.size
    | .inr _ => false
  let (next, outputs) ← insertReturningRows state tableName stored.schema columns conflict ctx projection inputs evaluateAll [] preparation
  return (next, [{ rows := if returning.isEmpty then [] else outputs, changes := outputs.length }])

/-- AUTOINCREMENT candidates use the existing checked conflict/RETURNING
executor after an explicit rowid has been allocated. The private counter is
threaded through ignored rows, without exposing it to the statement's SELECT. -/
def autoInsertRows (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (counter : CoreAutoIncrement.Context)
    (inputs : List (Array Expr)) (evaluateAll : Bool)
    (defaults : List (Option CoreReturning.Cell) := []) (preparation : Option RowPreparation := none) :
    Except String (Core.State × CoreAutoIncrement.Context × List (Option (List Core.Value))) :=
  match inputs with
  | [] => .ok (state, counter, [])
  | input :: inputs => do
      let cells ← inputRowValuesTyped schema columns evaluateAll (input.map (CoreLastInsert.bind state)) defaults
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {tableName}"
      let (counter, values) ← CoreAutoIncrement.prepare stored counter (cells.map (·.value))
      let (next, output) ← insertReturningValues state tableName conflict ctx projection
        (CoreReturning.withValues cells values) preparation
      let defaults := if output.isSome then insertDefaultRegisters schema columns input cells else defaults
      let (finalState, finalCounter, outputs) ← autoInsertRows next tableName schema columns conflict
        ctx projection counter inputs evaluateAll defaults preparation
      return (finalState, finalCounter, output :: outputs)

def executeAutoInsert (state : Core.State) (table : String) (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) (conflict : ConflictAction) (returning : Array ResultColumn)
    (preparation : Option RowPreparation := none) :
    Except String (Core.State × List Core.Result) := do
  unless conflict == .default || conflict == .abort || conflict == .replace || conflict == .ignore do
    throw "unsupported general verified-MVP SQL: INSERT conflict policy"
  let tableName := resolveTableName state table
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  let counter ← CoreAutoIncrement.beginContext state tableName
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := tableName }
  let targets ← prepareInsertTargets columns source preparation
  let columns := targets.columns
  if let .inl rows := source then CoreInsertPrepare.check stored.schema columns rows targets.implicitWidth
  let projection ← CoreLastInsert.prepareReturning state ctx returning.toList
  let inputs ← match source with
    | .inl rows => pure (if returning.isEmpty then rows.toList else
        rows.toList.map (·.map (CoreLastInsert.bind state)))
    | .inr query => do
        let selection ← executeSelect state query
        checkInsertSelectColumns stored.schema columns selection.width targets.implicitWidth
        prepareInsertSelectionDefaults stored.schema columns conflict
        selection.result.rows.mapM selectedRowExpressions
  let evaluateAll := match source with
    | .inl rows => 1 < rows.size
    | .inr _ => false
  let (next, counter, outputs) ← autoInsertRows state tableName stored.schema columns conflict ctx projection
    counter inputs evaluateAll [] preparation
  let next ← CoreAutoIncrement.finish next counter
  if returning.isEmpty then
    let results : List Core.Result := outputs.map fun output => { changes := if output.isSome then 1 else 0 }
    return (next, results)
  else
    let rows := outputs.flatMap Option.toList
    return (next, [{ rows, changes := rows.length }])

def automaticTable (state : Core.State) (name : String) : Bool :=
  (state.database.findTable? (resolveTableName state name)).any (fun stored => stored.schema.autoIncrement)

/-- Stream an external source while feeding each accepted INSERT's connection
register into the next projection and predicate. Source rows are immutable. -/
def insertRegisterRows (state : Core.State) (table : String) (columns : Option (Array String))
    (conflict : ConflictAction) (ctx : CoreExpr.Context) (projection : List Expr)
    (condition : Option Expr) (rows : List Core.Row) (offset : Nat) (remaining : Option Nat)
    (preparation : Option RowPreparation := none) : Except String (Core.State × List Core.Result) :=
  match rows with
  | [] => .ok (state, [])
  | row :: rows => do
      if remaining == some 0 then return (state, [])
      unless ← ctx.matches row.values (condition.map (CoreLastInsert.bind state)) do
        return ← insertRegisterRows state table columns conflict ctx projection condition rows offset remaining preparation
      if offset > 0 then
        return ← insertRegisterRows state table columns conflict ctx projection condition rows (offset-1) remaining preparation
      let values ← ctx.projectRow row.values (projection.map (CoreLastInsert.bind state))
      let input ← selectedRowExpressions values
      let (next, results) ← if automaticTable state table then
          executeAutoInsert state table columns (.inl #[input]) conflict #[] preparation
        else executeInsertReturning state table columns (.inl #[input]) conflict #[] preparation
      let (finalState, more) ← insertRegisterRows next table columns conflict ctx projection condition rows 0
        (remaining.map (·-1)) preparation
      return (finalState, results ++ more)

theorem insertRegisterRows_limit_zero (state : Core.State) (table : String)
    (columns : Option (Array String)) (conflict : ConflictAction) (ctx : CoreExpr.Context)
    (projection : List Expr) (condition : Option Expr) (rows : List Core.Row) (offset : Nat) :
    insertRegisterRows state table columns conflict ctx projection condition rows offset (some 0) =
      .ok (state, []) := by
  cases rows <;> simp [insertRegisterRows, pure, Except.pure]

/-- RETURNING and a source reading its own destination require materialization.
External plain scans can interleave reading and writing, so binding the register
once at statement entry would give the wrong values. -/
def executeRegisterInsertSelect (state : Core.State) (table : String)
    (columns : Option (Array String)) (query : Select) (conflict : ConflictAction)
    (returning : Array ResultColumn) (preparation : Option RowPreparation := none) : Except String (Core.State × List Core.Result) := do
  let source? := query.sources[0]?
  let materialized := !returning.isEmpty || source?.any (fun source =>
    resolveTableName state source.name == resolveTableName state table)
  if materialized || (query.sources.isEmpty && query.compounds.isEmpty) then
    let bound := CoreLastInsert.select state query
    if automaticTable state table then return ← executeAutoInsert state table columns (.inr bound) conflict returning preparation
    if returning.isEmpty && preparation.isNone then return ← executeInsertSelect state table columns bound conflict
    return ← executeInsertReturning state table columns (.inr bound) conflict returning preparation
  unless query.sources.size == 1 && query.compounds.isEmpty && query.valueRows.isNone &&
      query.orderBy.isEmpty && query.groupBy.isEmpty && query.having.isNone && !query.distinct do
    throw "unsupported connection-register INSERT SELECT plan"
  let some source := source? | throw "missing INSERT SELECT source"
  unless source.schema.isNone && source.functionArgs.isNone && source.subquerySql.isNone && source.joinOn.isNone do
    throw "unsupported connection-register INSERT SELECT source"
  let some stored := state.database.findTable? (resolveTableName state source.name)
    | throw s!"no such table: {source.name}"
  let some target := state.database.findTable? (resolveTableName state table)
    | throw s!"no such table: {table}"
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
  let projection ← CoreLastInsert.prepareProjection state ctx query.columns.toList
  if let some condition := query.where_ then ctx.validate (CoreLastInsert.bind state condition)
  let targets ← prepareInsertTargets columns (.inr query) preparation
  let columns := targets.columns
  checkInsertSelectColumns target.schema columns projection.length targets.implicitWidth
  prepareInsertSelectionDefaults target.schema columns conflict
  insertRegisterRows state table columns conflict ctx projection query.where_ stored.rows query.offset query.limit preparation

def indexNameExists (state : Core.State) (name : String) : Bool :=
  state.database.tables.any fun table => table.indexes.any fun index => canonical index.name == canonical name

def prepareCreateTable (state : Core.State) (name : String) (ifNotExists : Bool) :
    Except String Bool := do
  if (canonical name).startsWith "sqlite_" then throw s!"object name reserved for internal use: {name}"
  if (CoreNames.table? state.database name).isSome then
    if ifNotExists then return false else throw s!"table already exists: {name}"
  if indexNameExists state name then throw s!"there is already an index named {name}"
  return true

/-- CTAS emits one ordinary CREATE followed by ordinary Core INSERTs. The
selected rows are evaluated before the destination exists. -/
def createTableAsCommands (state : Core.State) (name : String) (query : Select) :
    Except String (List Core.Command) := do
  SQLite.Limit.validate query.limitClause
  let collations ← resultCollationsFuel query.compoundHeight state query
  discard <| collations.mapM (fun name => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName name))
  let selection ← executeSelect state query
  let definitions ← CoreCreateTableAs.columns state.database query
  unless definitions.size == selection.width do throw "CTAS output width mismatch"
  let schema ← schema name definitions #[]
  let inputs ← selection.result.rows.mapM selectedRowExpressions
  let values ← inputs.mapM (rowValues schema none)
  return .createTable schema :: values.map (Core.Command.insert name)

/-- SQLite's CTAS printer derives its type words from result affinity and
uses its own identifier quoting and layout threshold. Keep the resulting text
only through the schema-checked catalog constructor. -/
def retainCreateTableAsSQL (state : Core.State) (name : String) : Except String Core.State := do
  let some table := state.database.findTable? name | throw "created table is missing"
  let sql := SQLite.CtasCatalog.print table.schema.name
    (table.schema.catalogColumns.map (fun column => (column.name, column.affinity)))
  let retained ← table.withCatalogSQL sql
  let database ← state.database.updateTable retained
  return { state with database }

def executeCreateTableAs (state : Core.State) (name : String) (query : Select)
    (ifNotExists : Bool) : Except String (Core.State × List Core.Result) := do
  unless ← prepareCreateTable state name ifNotExists do return (state, [{}])
  let commands ← createTableAsCommands state name query
  let (next, _) ← runCoreCommands state commands
  let next ← retainCreateTableAsSQL next name
  return (next, [{}])

theorem executeCreateTableAs_trace (state : Core.State) (name : String)
    (query : Select) (ifNotExists : Bool) (commands : List Core.Command)
    (fresh : prepareCreateTable state name ifNotExists = .ok true)
    (planned : createTableAsCommands state name query = .ok commands) :
    executeCreateTableAs state name query ifNotExists = (do
      let outcome ← runCoreCommands state commands
      let next ← retainCreateTableAsSQL outcome.1 name
      pure (next, [{}])) := by
  simp only [executeCreateTableAs, fresh, planned, bind, Except.bind, pure, Except.pure]
  cases result : runCoreCommands state commands <;> rfl

/-- The target table must already have been resolved before checking the
index name. Existing indexes skip expression binding under IF NOT EXISTS. -/
def prepareCreateIndex (state : Core.State) (name : String) (ifNotExists : Bool)
    (table : String := "") : Except String Bool := do
  if (canonical table).startsWith "sqlite_" then throw s!"table {table} may not be indexed"
  if (canonical name).startsWith "sqlite_" then throw s!"object name reserved for internal use: {name}"
  if (CoreNames.table? state.database name).isSome then
    throw s!"there is already a table named {name}"
  if indexNameExists state name then
    if ifNotExists then return false else throw s!"index already exists: {name}"
  return true

def prepareDropTable (state : Core.State) (name : String) (ifExists : Bool) :
    Except String Bool := do
  if ["sqlite_schema", "sqlite_master", "sqlite_temp_schema", "sqlite_temp_master"].contains (canonical name) then
    throw s!"table {name} may not be dropped"
  if (CoreNames.table? state.database name).isSome then
    if canonical name == CoreAutoIncrement.sequenceName then throw "table sqlite_sequence may not be dropped"
    return true
  if ifExists then return false
  throw s!"no such table: {name}"

def indexOwner? (state : Core.State) (name : String) : Option Core.Table :=
  state.database.tables.find? fun stored =>
    stored.indexes.any fun index => canonical index.name == canonical name

def prepareDropIndex (state : Core.State) (name : String) (ifExists : Bool) :
    Except String Bool := do
  match indexOwner? state name with
  | none =>
      if ifExists then return false
      throw s!"no such index: {name}"
  | some stored =>
      if stored.indexes.any (fun index =>
          canonical index.name == canonical name && CoreAutomaticIndex.contains stored index) then
        throw "index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped"
      return true

/-- A successful schema no-op must also skip physical publication. -/
def schemaNoop (state : Core.State) : Statement → Bool
  | .dropTable name ifExists => (prepareDropTable state name ifExists).toOption == some false
  | .dropIndex name ifExists => (prepareDropIndex state name ifExists).toOption == some false
  | .createTable name _ _ ifNotExists | .createStrictTable name _ _ ifNotExists | .createTableAs name _ ifNotExists =>
      (prepareCreateTable state name ifNotExists).toOption == some false
  | .createIndex name table _ _ _ ifNotExists =>
      (state.database.findTable? (resolveTableName state table)).isSome &&
        (prepareCreateIndex state name ifNotExists (resolveTableName state table)).toOption == some false
  | _ => false

/-- Resolve and validate the common ALTER target before any row rebuild.
Source-level schema programs reuse these checks before their own restrictions. -/
def prepareAddColumn (state : Core.State) (table : String) (definition : ColumnDef) :
    Except String Core.Table := do
  let tableName := resolveTableName state table
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  if canonical tableName == CoreAutoIncrement.sequenceName then throw "table sqlite_sequence may not be altered"
  if stored.schema.catalogColumns.any (fun column => canonical column.name == canonical definition.name) then
    throw s!"duplicate column name: {definition.name}"
  unless stored.schema.catalogColumns.length < SQLite.Limits.maxColumns do throw "too many columns"
  return stored

def executeStatement (state : Core.State) :
    Statement → Except String (Core.State × List Core.Result)
  | .createTableAs name query ifNotExists => executeCreateTableAs state name query ifNotExists
  | .alterDropColumn table name => do
      let tableName := resolveTableName state table
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {table}"
      if canonical tableName == CoreAutoIncrement.sequenceName then throw "table sqlite_sequence may not be altered"
      let position ← indexColumn stored.schema name
      let updated ← CoreSchemaDropColumn.table stored position
      let database ← state.database.updateTable updated
      return ({ state with database }, [{}])
  | .alterAddColumn table definition => do
      let stored ← prepareAddColumn state table definition
      unless columnAllowed definition && definition.collation.toLower == "binary" && definition.generated.isNone && definition.references.isNone && definition.check.isNone && definition.earlierChecks.isEmpty && !definition.primaryKey && !definition.unique &&
          definition.conflict == .abort do
        unsupported "ADD COLUMN constraint or default"
      if stored.schema.hasHiddenRowid && canonical definition.name == "__sqleanite_rowid" then
        unsupported "reserved internal rowid column name"
      let column ← columnWithConflicts definition (ordinaryColumn definition)
      let updated ← CoreSchemaAdd.table stored column
      let database ← state.database.updateTable updated
      return ({ state with database }, [{}])
  | .alterRenameTable table name => do
      let tableName := resolveTableName state table
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {table}"
      if canonical tableName == CoreAutoIncrement.sequenceName then throw "table sqlite_sequence may not be altered"
      let _ ← prepareCreateTable state name false
      let renamed ← CoreSchemaRename.table stored name
      let database ← CoreSchemaRename.replace state.database tableName renamed
      let next := { state with database }
      let next ← CoreAutoIncrement.rename next tableName name
      return (next, [{}])
  | .alterRenameColumn table oldName newName => do
      let tableName := resolveTableName state table
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {table}"
      if canonical tableName == CoreAutoIncrement.sequenceName then throw "table sqlite_sequence may not be altered"
      let target ← indexColumn stored.schema oldName
      if stored.schema.catalogColumns.zipIdx.any (fun (column, index) =>
          index != target && canonical column.name == canonical newName) then
        throw s!"duplicate column name: {newName}"
      let renamed ← CoreSchemaRename.column stored target newName
      let database ← state.database.updateTable renamed
      return ({ state with database }, [{}])
  | .insertSelect table columns query conflict returning =>
      if CoreLastInsert.queryUses query.compoundHeight query then
        executeRegisterInsertSelect state table columns query conflict returning
      else if automaticTable state table then executeAutoInsert state table columns (.inr query) conflict returning
      else if returning.isEmpty then executeInsertSelect state table columns query conflict
      else executeInsertReturning state table columns (.inr query) conflict returning
  | .dropTable name ifExists => do
      unless ← prepareDropTable state name ifExists do return (state, [{}])
      let tableName := resolveTableName state name
      let automatic := automaticTable state tableName
      let database ← CoreSchemaDrop.table state.database tableName
      let next := { state with database }
      let next ← if automatic then CoreAutoIncrement.remove next tableName else pure next
      return (next, [{}])
  | .dropIndex name ifExists => do
      unless ← prepareDropIndex state name ifExists do return (state, [{}])
      let stored ← match indexOwner? state name with
        | some stored => pure stored
        | none => throw s!"no such index: {name}"
      let updated ← CoreSchemaDrop.index stored (CoreNames.indexName stored name)
      let database ← state.database.updateTable updated
      return ({ state with database }, [{}])
  | .createTable name columns constraints ifNotExists => do
      unless ← prepareCreateTable state name ifNotExists do return (state, [{}])
      unless (CoreCheck.collect columns constraints).isEmpty do
        unsupported "CHECK declaration requires retained SQL source"
      unless columns.all (fun column => column.generated.isNone) do
        unsupported "generated declaration requires retained SQL source"
      unless columns.all (fun column => column.collation.toLower == "binary") do
        unsupported "collation declaration requires retained SQL source"
      unless columns.all (fun column => column.references.isNone) &&
          constraints.all (fun constraint => constraint.references.isNone) do
        unsupported "FOREIGN KEY declaration requires retained SQL source"
      let admitted ← schema name columns constraints
      let (next, results) ← executeCommand state (.createTable admitted)
      let next ← if columns.any (·.unique) || constraints.any (fun constraint => !constraint.primaryKey) then do
          let indexes ← automaticIndexes admitted columns constraints
          let table ← Core.Table.rebuild admitted indexes []
          let database ← next.database.updateTable table
          pure { next with database }
        else pure next
      let next ← if admitted.autoIncrement then CoreAutoIncrement.ensure next else pure next
      return (next, results)
  | .createIndex name table expressions unique where_ ifNotExists => do
      let tableName := resolveTableName state table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      unless ← prepareCreateIndex state name ifNotExists tableName do return (state, [{}])
      if where_.isSome then unsupported "partial index"
      else
        let columnName ← match expressions.toList with
          | [expression] => match indexColumnName? expression with
            | some name => .ok name
            | none => unsupported "index expression"
          | _ => unsupported "index expression"
        let columnIndex ← indexColumn stored.schema columnName
        executeCommand state (.createIndex tableName {
          name := name, column := columnIndex, unique })
  | .insert table columns rows conflict returning => do
      if automaticTable state table then return ← executeAutoInsert state table columns (.inl rows) conflict returning
      if !returning.isEmpty || rows.any (fun row => row.any CoreLastInsert.uses) then
        return ← executeInsertReturning state table columns (.inl rows) conflict returning
      unless conflict == .default || conflict == .abort || conflict == .replace || conflict == .ignore do
        throw "unsupported general verified-MVP SQL: INSERT conflict policy"
      let tableName := resolveTableName state table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      if conflict == .default && CoreDefaultConflict.active stored.schema then
        schemaInsertRows state tableName stored.schema columns rows.toList (1 < rows.size)
      else if conflict == .ignore then
        ignoreInsertRows state tableName stored.schema columns rows.toList (1 < rows.size)
      else if conflict == .replace && hasReplaceKeys stored then
        replaceUniqueRows state tableName stored.schema columns rows.toList (1 < rows.size)
      else
        insertRows state tableName stored.schema columns (conflict == .replace) rows.toList (1 < rows.size)
  | .delete table alias where_ returning => do
      let tableName := resolveTableName state table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      unless writeNamesBound stored.schema table alias #[] where_ do unsupported "unbound DELETE name"
      if !returning.isEmpty then return ← executeDeleteReturning state tableName alias stored where_ returning
      match where_.mapM (predicate stored.schema) with
      | .ok condition => executeCommand state (.deleteWhere tableName condition)
      | .error _ => executeExpressionDelete state tableName alias stored where_
  | .update table alias assignments where_ conflict returning => do
      unless conflict == .default || conflict == .abort || conflict == .ignore || conflict == .replace do
        throw "unsupported general verified-MVP SQL: UPDATE conflict policy"
      let tableName := resolveTableName state table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      unless writeNamesBound stored.schema table alias assignments where_ do
        let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD table }
        for expression in assignments.toList.map (·.2) ++ where_.toList do
          if let some message := SQLite.Scalar.resolutionError (fun q n => (ctx.column? q n).isSome) expression then
            throw message
        unsupported "unbound UPDATE name"
      if stored.hasChecks then
        let (next, results) ← executeUpdateReturning state tableName alias stored assignments.toList where_ conflict returning
        return (next, if returning.isEmpty then results.map (fun result => { result with rows := [] }) else results)
      if !returning.isEmpty then
        return ← executeUpdateReturning state tableName alias stored assignments.toList where_ conflict returning
      if conflict == .default && CoreDefaultConflict.active stored.schema then
        return ← executeSchemaUpdate state tableName alias stored assignments.toList where_
      if conflict == .ignore then
        return ← executeIgnoredUpdate state tableName alias stored assignments.toList where_
      if conflict == .replace then
        return ← executeReplacedUpdate state tableName alias stored assignments.toList where_
      match updateAssignments stored.schema assignments.toList,
          where_.mapM (predicate stored.schema) with
      | .ok updates, .ok condition =>
          executeCommand state (.updateWhere tableName updates condition)
      | _, _ =>
          if assignments.any (fun assignment =>
              findColumn? stored.schema assignment.1 == some stored.schema.primaryKey ||
              findColumn? stored.schema assignment.1 == some stored.schema.declaredPrimaryKey) then
            executeRekeyUpdate state tableName alias stored assignments.toList where_
          else executeExpressionUpdate state tableName alias stored assignments.toList where_
  | .pragma name argument schema =>
      if SQLite.ApplicationHeader.supported name then CoreHeaderPragma.execute state name argument schema
      else CoreSchemaPragma.execute state name argument schema
  | .select select => do
      let execution ← executeSelect state select
      return (execution.state, [execution.result])
  | .savepoint name => .ok (CoreSavepoint.push state name, [{}])
  | .release name => do return (← CoreSavepoint.release state name, [{}])
  | .rollbackTo name => do return (← CoreSavepoint.rollbackTo state name, [{}])
  | .begin => executeCommand state .begin
  | .commit => executeCommand state .commit
  | .rollback => executeCommand state .rollback
  | _ => unsupported "statement"

theorem executeStatement_dropTable_noop (state : Core.State) (name : String) (ifExists : Bool)
    (skipped : prepareDropTable state name ifExists = .ok false) :
    executeStatement state (.dropTable name ifExists) = .ok (state, [{}]) := by
  simp [executeStatement, skipped, bind, Except.bind, pure, Except.pure]

theorem executeStatement_dropIndex_noop (state : Core.State) (name : String) (ifExists : Bool)
    (skipped : prepareDropIndex state name ifExists = .ok false) :
    executeStatement state (.dropIndex name ifExists) = .ok (state, [{}]) := by
  simp [executeStatement, skipped, bind, Except.bind, pure, Except.pure]

theorem executeStatement_createTable_noop (state : Core.State) (name : String)
    (columns : Array ColumnDef) (constraints : Array TableConstraintDef) (ifNotExists : Bool)
    (skipped : prepareCreateTable state name ifNotExists = .ok false) :
    executeStatement state (.createTable name columns constraints ifNotExists) = .ok (state, [{}]) := by
  simp [executeStatement, skipped, bind, Except.bind, pure, Except.pure]

theorem executeStatement_createIndex_noop (state : Core.State) (name table : String)
    (expressions : Array Expr) (unique : Bool) (where_ : Option Expr) (ifNotExists : Bool)
    (stored : Core.Table) (found : state.database.findTable? (resolveTableName state table) = some stored)
    (skipped : prepareCreateIndex state name ifNotExists (resolveTableName state table) = .ok false) :
    executeStatement state (.createIndex name table expressions unique where_ ifNotExists) = .ok (state, [{}]) := by
  simp [executeStatement, found, skipped, bind, Except.bind, pure, Except.pure]

def runStatements : Core.State → List Statement →
    Except String (Core.State × List Core.Result)
  | state, [] => .ok (state, [])
  | state, statement :: statements =>
      match executeStatement state statement with
      | .error message => .error message
      | .ok (next, results) =>
          match runStatements next statements with
          | .error message => .error message
          | .ok (finalState, remaining) =>
              .ok (finalState, results ++ remaining)

def execute (state : Core.State) (sql : String) :
    Except String (Core.State × List Core.Result) := do
  let parsed ← CoreTokenGrammar.parseCertified sql
  runStatements state parsed.statements.toList

theorem runStatements_append (state : Core.State)
    (left right : List Statement) :
    runStatements state (left ++ right) =
      match runStatements state left with
      | .error message => .error message
      | .ok (middle, leftResults) =>
          match runStatements middle right with
          | .error message => .error message
          | .ok (finalState, rightResults) =>
              .ok (finalState, leftResults ++ rightResults) := by
  induction left generalizing state with
  | nil =>
      cases outcome : runStatements state right with
      | error message => simp [runStatements, outcome]
      | ok pair =>
          rcases pair with ⟨finalState, results⟩
          simp [runStatements, outcome]
  | cons statement statements induction =>
      cases execution : executeStatement state statement with
      | error message => simp [runStatements, execution]
      | ok pair =>
          rcases pair with ⟨nextState, statementResults⟩
          rw [show runStatements state ((statement :: statements) ++ right) =
            runStatements state (statement :: (statements ++ right)) by rfl]
          simp only [runStatements, execution]
          rw [induction nextState]
          cases tail : runStatements nextState statements with
          | error message => simp [runStatements, execution, tail]
          | ok pair =>
              rcases pair with ⟨middle, results⟩
              cases suffix : runStatements middle right with
              | error message => simp [runStatements, execution, tail, suffix]
              | ok pair =>
                  rcases pair with ⟨finalState, rightResults⟩
                  simp [runStatements, execution, tail, suffix, List.append_assoc]

end CoreSQL
end SQLeanite
