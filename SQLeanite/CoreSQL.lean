import SQLeanite.CoreEngine
import SQLeanite.CoreOptimizerBridge
import SQLeanite.CoreTokenGrammar
import SQLeanite.SQLSurface
import SQLeanite.CoreExpr
import SQLeanite.CoreOrder
import SQLeanite.CoreAggregate
import SQLeanite.CoreCompound

namespace SQLeanite
namespace CoreSQL

def unsupported (feature : String) : Except String α :=
  .error s!"unsupported general verified-MVP SQL: {feature}"

def canonical (name : String) : String := name.toLower

/-- build.c dequotes a quoted declared type before computing affinity. Keep
the original spelling of ordinary multiword/parameterized type names. -/
def declaredTypeName (source : String) : String :=
  match lex source with
  | .ok tokens => match (CoreTokenGrammar.significant tokens.toList).head? with
      | some (.quotedIdent name _) | some (.string name) => name
      | _ => source.trimAscii.toString
  | .error _ => source.trimAscii.toString

def columnAllowed (column : ColumnDef) : Bool :=
  column.defaultValue.isNone && column.generated.isNone && !column.unique &&
  column.references.isNone && column.check.isNone && !column.autoIncrement &&
  column.collation.toLower == "binary"

def schema (name : String) (definitions : Array ColumnDef)
    (constraints : Array TableConstraintDef) : Except String Core.Schema := do
  unless constraints.isEmpty do
    throw "unsupported general verified-MVP SQL: table constraints"
  unless definitions.toList.all columnAllowed do
    throw "unsupported general verified-MVP SQL: column constraint"
  let primaryKeys := definitions.toList.filter (·.primaryKey)
  if primaryKeys.isEmpty then
    let visibleColumns : List Core.Column := definitions.toList.map fun column => {
      name := canonical column.name
      notNull := column.notNull
      declaredType := declaredTypeName column.declaredType }
    unless !visibleColumns.isEmpty do throw "table must have at least one column"
    if visibleColumns.any (fun column => column.name == "__sqleanite_rowid") then
      throw "reserved verified column name: __sqleanite_rowid"
    return {
      name := canonical name
      columns := visibleColumns ++ [Core.hiddenRowidColumn]
      primaryKey := visibleColumns.length
      declaredPrimaryKey := visibleColumns.length + 1 }
  unless primaryKeys.length = 1 do
    throw "verified MVP tables require exactly one PRIMARY KEY"
  let primaryKey ← match definitions.findIdx? (fun column => column.primaryKey) with
    | some index => .ok index
    | none => .error "verified MVP table has no primary key"
  let primaryDefinition ← match definitions[primaryKey]? with
    | some column => .ok column
    | none => .error "verified MVP primary-key index is out of bounds"
  let integerAlias := (declaredTypeName primaryDefinition.declaredType).toLower == "integer"
  unless integerAlias || (declaredTypeName primaryDefinition.declaredType).toLower == "text" do
    throw "verified MVP primary key must have declared type INTEGER or TEXT"
  let visibleColumns : List Core.Column := definitions.toList.map fun column =>
    if column.primaryKey then {
      name := canonical column.name
      notNull := true
      integerPrimaryKey := integerAlias
      textPrimaryKey := !integerAlias }
    else {
      name := canonical column.name
      notNull := column.notNull
      declaredType := declaredTypeName column.declaredType }
  if integerAlias then return {
    name := canonical name
    columns := visibleColumns
    primaryKey
    declaredPrimaryKey := primaryKey }
  else
    let hiddenName := "__sqleanite_rowid"
    if visibleColumns.any (fun column => column.name == hiddenName) then
      throw s!"reserved verified column name: {hiddenName}"
    return {
      name := canonical name
      columns := visibleColumns ++ [Core.hiddenRowidColumn]
      primaryKey := visibleColumns.length
      declaredPrimaryKey := primaryKey }

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
  match schema.columns.findIdx? (fun column => column.name == canonical name) with
  | some index => some index
  | none => if ["rowid", "oid", "_rowid_"].contains (canonical name) then
      some schema.primaryKey else none

def column (schema : Core.Schema) (name : String) : Except String Nat :=
  match findColumn? schema name with
  | some index => .ok index
  | none => .error s!"no such column: {name}"

/-- CREATE INDEX cannot name an implicit rowid alias. A real column with
that spelling is still permitted. -/
def indexColumn (schema : Core.Schema) (name : String) : Except String Nat :=
  match schema.catalogColumns.findIdx? (fun column => column.name == canonical name) with
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

def indexColumnName? : Expr → Option String
  | .column none name => some name
  | .call "lean_dqs" #[.literal (.text name)] false => some name
  | .call "__sqlean_boolean_true" #[] false => some "true"
  | .call "__sqlean_boolean_false" #[] false => some "false"
  | _ => none

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
  | [{ expr := .call name #[.column qualifier columnName] false, .. }] =>
      if qualifier.isSome then .ok none
      else if canonical name == "sum" then return some (← column schema columnName)
      else .ok none
  | [{ expr := .call name _ _, .. }] =>
      .ok none
  | _ => .ok none

def extremeColumn? (schema : Core.Schema) :
    List ResultColumn → Except String (Option (Bool × Nat))
  | [{ expr := .call name #[.column qualifier columnName] false, .. }] =>
      if qualifier.isSome then .ok none
      else if canonical name == "min" then
        return some (true, ← column schema columnName)
      else if canonical name == "max" then
        return some (false, ← column schema columnName)
      else .ok none
  | [{ expr := .call name args star, .. }] =>
      if canonical name == "min" || canonical name == "max" then
        .ok none
      else .ok none
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

def rowValues (schema : Core.Schema) (insertColumns : Option (Array String))
    (expressions : Array Expr) : Except String (List Core.Value) := do
  if expressions.isEmpty then
    let _ ← insertColumns.mapM (fun names => names.toList.mapM (column schema))
    return List.replicate schema.columns.length .null
  match insertColumns with
  | none =>
      unless expressions.size = schema.visibleColumns.length do
        throw s!"table {schema.name} has {schema.visibleColumns.length} columns but {expressions.size} values were supplied"
      let visibleValues ← expressions.toList.mapM literal
      let pairs := schema.visibleColumnIndices.zip visibleValues
      schema.columns.mapIdxM fun index target =>
        match pairs.find? (fun pair => pair.1 == index) with
        | some pair => .ok (SQLite.PhysicalAffinity.write target.affinity pair.2)
        | none => .ok .null
  | some names =>
      unless names.size = expressions.size do
        throw "INSERT column/value count mismatch"
      let indices ← names.toList.mapM (column schema)
      schema.columns.mapIdxM fun targetIndex target =>
        match indices.findIdx? (· == targetIndex) with
        | some index => columnLiteral target expressions[index]!
        | none => .ok .null

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
    (schema : Core.Schema) (columns : Option (Array String)) (replacing : Bool) :
    List (Array Expr) → Except String (Core.State × List Core.Result)
  | [] => .ok (state, [])
  | expressions :: rows => do
      let values ← rowValues schema columns expressions
      let command : Core.Command :=
        if replacing then .replace table values else .insert table values
      let (next, result) ← Core.execute state command
      let (finalState, results) ← insertRows next table schema columns replacing rows
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
      simp only [insertRows, translated, Bool.false_eq_true, if_false,
        executeCommand, bind, Functor.map, Except.bind, pure]
  | true =>
      simp only [insertRows, translated, if_pos rfl, executeCommand,
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
    (replacing : Bool) : ∀ (rows : List (Array Expr))
      (values : List (List Core.Value)),
      rows.mapM (rowValues schema columns) = .ok values →
      insertRows state table schema columns replacing rows =
        runCoreCommands state (values.map fun row =>
          if replacing then .replace table row else .insert table row)
  | [], values, translated => by
      have empty : values = [] := by simpa using Except.ok.inj translated
      subst values
      rfl
  | expressions :: rows, values, translated => by
      cases head : rowValues schema columns expressions with
      | error message =>
          simp [List.mapM_cons, head, bind, Functor.map, Except.bind,
            pure, Except.pure, pure] at translated
      | ok value =>
          cases tail : rows.mapM (rowValues schema columns) with
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
                    schema columns replacing rows remaining tail
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
bound, but are not evaluated. Rowid changes use a separate delete/insert trace;
a declared non-rowid key still needs its own constraint implementation. -/
def expressionAssignmentsWith (allowRowid : Bool) (ctx : CoreExpr.Context) : List (String × Expr) →
    Except String (List (Nat × Expr))
  | [] => .ok []
  | (name, expression) :: rest => do
      let index ← column ctx.schema name
      ctx.validate expression
      let remaining ← expressionAssignmentsWith allowRowid ctx rest
      if remaining.any (fun next => next.1 == index) then return remaining
      if (index = ctx.schema.primaryKey || index = ctx.schema.declaredPrimaryKey) &&
          !(allowRowid && index = ctx.schema.primaryKey) then
        throw "updating the declared PRIMARY KEY is outside this path"
      return (index, expression) :: remaining

def expressionAssignments (ctx : CoreExpr.Context) := expressionAssignmentsWith false ctx

/-- All RHS expressions read the same original row; affinity is applied only
to each completed value. No earlier assignment changes a later RHS binding. -/
def evaluateAssignments (ctx : CoreExpr.Context) (row : Core.Row) :
    List (Nat × Expr) → Except String (List (Nat × Core.Value))
  | [] => .ok []
  | (index, expression) :: rest => do
      let target ← match ctx.schema.columns[index]? with
        | some target => .ok target
        | none => .error "UPDATE column is out of range"
      let value ← SQLSurface.value (← ctx.eval row.values expression)
      let remaining ← evaluateAssignments ctx row rest
      return (index, SQLite.PhysicalAffinity.write target.affinity value) :: remaining

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

def executeExpressionDelete (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  let commands ← expressionDeletePlan tableName alias stored condition
  let (next, results) ← runCoreCommands state commands
  return (next, [{ changes := (results.map (·.changes)).sum }])

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
      let left := findColumn? context.leftSchema columnName
      let right := findColumn? context.rightSchema columnName
      match left, right with
      | some index, none => .ok ⟨.left, index⟩
      | none, some index => .ok ⟨.right, index⟩
      | some _, some _ => .error s!"ambiguous column name: {name}"
      | none, none => .error s!"no such column: {name}"

def joinOperand (context : JoinContext) : Expr → Except String CoreJoin.Operand
  | .column qualifier name => .column <$> joinColumn context qualifier name
  | expression => .literal <$> literal expression

def joinColumnDefinition (context : JoinContext) (reference : CoreJoin.ColumnRef) :
    Except String Core.Column :=
  let schema := match reference.side with
    | .left => context.leftSchema
    | .right => context.rightSchema
  match schema.columns[reference.column]? with
  | some column => .ok column
  | none => .error "join column is out of range"

def joinOperandAffinity (context : JoinContext) (expression : Expr) :
    CoreJoin.Operand → Except String (Option SQLite.Affinity)
  | .column reference => do return some (← joinColumnDefinition context reference).affinity
  | .literal _ => .ok (SQLite.Scalar.expressionAffinity expression)

def joinOperandCoerce (context : JoinContext) (aff : SQLite.Affinity) :
    CoreJoin.Operand → Except String CoreJoin.Operand
  | .literal value => .ok (.literal (SQLite.PhysicalAffinity.comparison aff value))
  | operand@(.column reference) => do
      let target ← joinColumnDefinition context reference
      unless aff == .blob || aff.comparison == target.affinity.comparison do
        unsupported "join requiring conversion of a stored column"
      return operand

def joinComparison (context : JoinContext)
    (operation : CoreJoin.Operand → CoreJoin.Operand → CoreJoin.Predicate)
    (left right : Expr) : Except String CoreJoin.Predicate := do
  let a ← joinOperand context left
  let b ← joinOperand context right
  let aff := SQLite.Scalar.comparisonAffinity
    (← joinOperandAffinity context left a) (← joinOperandAffinity context right b)
  return operation (← joinOperandCoerce context aff a) (← joinOperandCoerce context aff b)

def joinPredicate (context : JoinContext) : Expr →
    Except String CoreJoin.Predicate
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
  | .unary .not expression => .not <$> joinPredicate context expression
  | .binary .and left right =>
      .and <$> joinPredicate context left <*> joinPredicate context right
  | .binary .or left right =>
      .or <$> joinPredicate context left <*> joinPredicate context right
  | _ => unsupported "join predicate"

def joinSideColumns (side : CoreJoin.Side) (count : Nat) :
    List CoreJoin.ColumnRef :=
  (List.range count).map fun index => ⟨side, index⟩

def joinVisibleColumns (side : CoreJoin.Side) (schema : Core.Schema) :
    List CoreJoin.ColumnRef :=
  schema.visibleColumnIndices.map fun index => ⟨side, index⟩

def joinResultColumn (context : JoinContext) : ResultColumn →
    Except String (List CoreJoin.ColumnRef)
  | { expr := .column qualifier name, .. } =>
      return [← joinColumn context qualifier name]
  | { expr := .star none, .. } =>
      .ok (joinVisibleColumns .left context.leftSchema ++
        joinVisibleColumns .right context.rightSchema)
  | { expr := .star (some qualifier), .. } =>
      let owner := canonical qualifier
      if owner == context.leftName then
        .ok (joinVisibleColumns .left context.leftSchema)
      else if owner == context.rightName then
        .ok (joinVisibleColumns .right context.rightSchema)
      else .error s!"no such table or alias: {qualifier}"
  | _ => unsupported "join projection"

def joinProjection (context : JoinContext) : List ResultColumn →
    Except String (List CoreJoin.ColumnRef)
  | [] => .ok []
  | result :: results =>
      return (← joinResultColumn context result) ++ (← joinProjection context results)

def joinOrderBy (context : JoinContext) : List OrderTerm →
    Except String (List (CoreJoin.ColumnRef × Bool))
  | [] => .ok []
  | { expr := .column qualifier name, descending, nullsFirst } :: terms => do
      unless nullsFirst.all (· == !descending) do unsupported "non-default join NULL ordering"
      return (← joinColumn context qualifier name, descending) ::
        (← joinOrderBy context terms)
  | _ => unsupported "join ORDER BY expression"

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

/-- Translate the supported two-source SQL shape independently of a materialized
database.  Both the ordinary engine and cold page-directed execution use this
single interpretation, preventing the fast path from acquiring subtly
different alias, projection, or predicate semantics. -/
def joinQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query := do
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless leftSource.subquerySql.isNone && rightSource.subquerySql.isNone &&
      leftSource.joinOn.isNone && !rightSource.rightJoin &&
      !rightSource.naturalJoin && rightSource.usingColumns.isEmpty do
    throw "unsupported general verified-MVP SQL: only INNER/LEFT JOIN ... ON"
  unless select.groupBy.isEmpty && select.having.isNone && !select.distinct &&
      select.offset = 0 do
    throw "unsupported general verified-MVP SQL: join SELECT shape"
  unless canonical leftSource.name = leftTable &&
      canonical rightSource.name = rightTable do
    throw "join source/schema mismatch"
  let context : JoinContext := {
    leftTable, rightTable
    leftName := canonical (leftSource.alias.getD leftSource.name)
    rightName := canonical (rightSource.alias.getD rightSource.name)
    leftSchema
    rightSchema }
  if context.leftName == context.rightName then
    throw "join sources require distinct names or aliases"
  let onExpression ← match rightSource.joinOn with
    | some expression => .ok expression
    | none => .error "inner join requires ON"
  return {
    columns := ← joinProjection context select.columns.toList
    on := some (← joinPredicate context onExpression)
    kind := if rightSource.leftJoin then .left else .inner
    rightWidth := rightSchema.columns.length
    where_ := ← select.where_.mapM (joinPredicate context)
    orderBy := ← joinOrderBy context select.orderBy.toList
    limit := select.limit }

def executeJoin (state : Core.State) (select : Select) :
    Except String SelectExecution := do
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless leftSource.subquerySql.isNone && rightSource.subquerySql.isNone &&
      leftSource.joinOn.isNone && !rightSource.rightJoin &&
      !rightSource.naturalJoin && rightSource.usingColumns.isEmpty do
    throw "unsupported general verified-MVP SQL: only INNER/LEFT JOIN ... ON"
  unless select.groupBy.isEmpty && select.having.isNone && !select.distinct &&
      select.offset = 0 do
    throw "unsupported general verified-MVP SQL: join SELECT shape"
  let leftTable := canonical leftSource.name
  let rightTable := canonical rightSource.name
  let left ← match state.database.findTable? leftTable with
    | some table => .ok table
    | none => .error s!"no such table: {leftSource.name}"
  let right ← match state.database.findTable? rightTable with
    | some table => .ok table
    | none => .error s!"no such table: {rightSource.name}"
  let query ← joinQuery select leftTable rightTable left.schema right.schema
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
  unless select.columns.all (fun column => SQLite.Scalar.admitted column.expr) &&
      select.where_.all SQLite.Scalar.admitted do
    unsupported "constant SELECT expression"
  let ctx : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  if select.distinct then
    CoreExpr.validateDistinct (select.columns.toList.map (·.expr))
  let ordering ← CoreOrder.resolve ctx select.columns.toList select.orderBy.toList
  let _ ← ordering.mapM (fun term => do
    let _ ← CoreOrder.specification term
    unless SQLite.Scalar.admitted (CoreOrder.keyExpression term.expr) do
      unsupported "constant ORDER BY expression")
  if select.limit == some 0 then return none
  if let some condition := select.where_ then
    unless ← SQLite.Scalar.testWhere condition do return none
  if select.offset > 0 then return none
  return some (← select.columns.toList.mapM (fun column => literal column.expr))

/-- A source-free aggregate consumes the SELECT's single implicit empty row,
unless WHERE rejects it. It still emits one aggregate row for empty input. -/
def constantRow (select : Select) : Except String (Option (List Core.Value)) := do
  unless select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) do
    return ← scalarConstantRow select
  unless select.sources.isEmpty && select.valueRows.isNone &&
      select.groupBy.isEmpty && select.having.isNone && select.orderBy.isEmpty do
    unsupported "constant aggregate SELECT shape"
  let ctx : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  if select.distinct then
    CoreExpr.validateDistinct (select.columns.toList.map (fun c => ctx.bindNames c.expr))
  let prepared ← CoreAggregate.prepareResults ctx select.columns.toList
  unless prepared.terms.all (fun term => term.argument.all SQLite.Scalar.admitted) &&
      select.where_.all SQLite.Scalar.admitted do
    unsupported "unbound constant aggregate expression"
  if select.limit == some 0 then return none
  let enabled ← match select.where_ with
    | none => pure true
    | some condition => SQLite.Scalar.testWhere condition
  let values ← prepared.accumulate ctx (if enabled then [[]] else [])
  if select.offset > 0 then return none
  return some (← prepared.finish values)

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

/-- Fallback for row-dependent WHERE expressions. Source rows still come from
Core.execute. A primary-key order determines scan direction; other orderings
sort surviving outputs. LIMIT is applied during an ordered scan or after a
sort, and all names are bound before either path can skip evaluation. -/
def filteredSelectResult (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String (Core.Result × Nat) := do
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
    unless ← ctx.constantMatches select.where_ do return ({}, expressions.length)
  let search ← if select.limit == some 0 then pure none
    else expressionSearch ctx stored select.where_
  let ctx := expressionSearchContext ctx search
  if select.limit != some 0 then
    unless ← expressionSearchReady ctx search select.where_ do return ({}, expressions.length)
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
  let (_, result) ← Core.execute state (.query (canonical source.name) query)
  let projected ← if orderedScan then
      ctx.scanWindow select.where_ expressions select.distinct result.rows select.offset select.limit []
    else CoreOrder.scan ctx select.where_ expressions terms select.distinct result.rows select.offset select.limit
  return ({ result with rows := projected.map (·.output) }, expressions.length)

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

/-- Aggregate arguments bind before empty-input/LIMIT shortcuts. WHERE is
scanned once over Core rows before any aggregate result is finalized. -/
def aggregateSelectResult (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String (Core.Result × Nat) := do
  unless select.groupBy.isEmpty && select.having.isNone && select.orderBy.isEmpty do
    unsupported "aggregate grouping, HAVING or ORDER BY"
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
  if select.distinct then
    CoreExpr.validateDistinct (select.columns.toList.map (fun c => ctx.bindNames c.expr))
  let prepared ← CoreAggregate.prepareResults ctx select.columns.toList
  let _ ← select.where_.mapM ctx.validate
  if select.limit == some 0 then return ({}, prepared.expressions.length)
  let enabled ← ctx.constantMatches select.where_
  let search ← if enabled then expressionSearch ctx stored select.where_ else pure none
  let ctx := expressionSearchContext ctx search
  let enabled ← if enabled then expressionSearchReady ctx search select.where_ else pure false
  let inputs ← if !enabled then pure [] else do
    let (_, result) ← Core.execute state (.query (canonical source.name)
      { columns := List.range stored.schema.columns.length, predicate := search })
    CoreAggregate.selectRows ctx select.where_ result.rows
  let values ← prepared.accumulate ctx inputs
  let rows ← if select.offset > 0 then pure [] else do pure [← prepared.finish values]
  return ({ rows }, prepared.expressions.length)

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

/-- Scalar and aggregate projections share bound Core source rows. A recognized
aggregate anywhere in a result expression selects the aggregate evaluator;
aggregate arguments and scalar output templates bind before evaluation. -/
def executeExpressionSelect (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) (_wherePredicate : Option Core.Predicate) :
    Except String SelectExecution :=
  if select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) then
    executeAggregateSelect state select source stored
  else executeFilteredSelect state select source stored

/-- Every single-source route, including page-directed reads, checks the same
source/alias scope before a direct Core command can omit an AST qualifier. -/
def selectNamesBound (schema : Core.Schema) (source : TableRef) (select : Select) : Bool :=
  let ctx : CoreExpr.Context := { schema, sourceName := source.alias.getD source.name }
  select.columns.all (fun result => ctx.namesBound result.expr) &&
    select.where_.all ctx.namesBound && select.groupBy.all ctx.namesBound &&
    select.having.all ctx.namesBound &&
    ((resolvedOrdering schema source select).toOption.any (fun terms => terms.all (fun term => ctx.namesBound term.expr)))

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

def executeSelectBase (state : Core.State) (select : Select) :
    Except String SelectExecution :=
  if select.sources.size = 2 then executeJoin state select
  else if select.sources.isEmpty then executeConstantSelect state select
  else do
    unless select.sources.size = 1 && select.having.isNone do
      throw "unsupported general verified-MVP SQL: SELECT shape"
    let source ← match select.sources[0]? with
      | some source => .ok source
      | none => .error "SELECT has no source table"
    unless source.subquerySql.isNone && source.joinOn.isNone do
      throw "unsupported general verified-MVP SQL: SELECT source"
    let tableName := canonical source.name
    let stored ← match state.database.findTable? tableName with
      | some stored => .ok stored
      | none => .error s!"no such table: {source.name}"
    unless selectNamesBound stored.schema source select do unsupported "unbound SELECT name"
    match select.where_.mapM (predicate stored.schema) with
    | .error _ => executeExpressionSelect state select source stored none
    | .ok wherePredicate => do
      if !select.groupBy.isEmpty then
        if select.distinct || !select.orderBy.isEmpty || select.limit.isSome || select.offset != 0 then
          unsupported "grouped DISTINCT, ORDER BY, or LIMIT"
        else
          let groups ← groupColumns stored.schema select.groupBy.toList
          let query : Core.GroupQuery := {
            groupBy := groups
            outputs := ← groupOutputs stored.schema groups select.columns.toList
            predicate := wherePredicate }
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
    if source.subquerySql.isNone && source.joinOn.isNone then
      let tableName := canonical source.name
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

def executeSelectFuel : Nat → Core.State → Select → Except String SelectExecution
  | 0, _, _ => .error "compound SELECT exceeds its verified recursion bound"
  | fuel + 1, state, select => do
      unless select.compounds.isEmpty ||
          (select.orderBy.isEmpty && select.limit.isNone && select.offset = 0) do
        throw "unsupported general verified-MVP SQL: compound ORDER BY or LIMIT"
      let base ← executeSelectBase state { select with compounds := #[] }
      let rec executeArms (current : SelectExecution) :
          List (CompoundOp × Select) → Except String SelectExecution
        | [] => .ok current
        | (operation, arm) :: arms => do
            let next ← executeSelectFuel fuel current.state arm
            unless current.width = next.width do
              throw "SELECTs to the left and right of a compound operator must have the same number of result columns"
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

/-- Allocate the replacement rowid against the original table, then remove
all rows conflicting with the primary key or any explicit UNIQUE index. -/
def uniqueReplacePlan (stored : Core.Table) (values : List Core.Value) :
    Except String (List Core.Command) := do
  let row ← stored.createRow values
  let declared := stored.findDeclaredPrimary? row
  let conflicts := stored.rows.filter fun existing =>
    existing.rowid == row.rowid || declared.any (fun old => old.rowid == existing.rowid) ||
      stored.indexes.any (fun index => index.rowConflict row existing)
  let deletes := conflicts.map fun old => Core.Command.deleteWhere stored.schema.name
    (some (.equal stored.schema.primaryKey (.integer old.rowid)))
  return deletes ++ [.insert stored.schema.name row.values]

def replaceUniqueRows (state : Core.State) (table : String)
    (schema : Core.Schema) (columns : Option (Array String)) :
    List (Array Expr) → Except String (Core.State × List Core.Result)
  | [] => .ok (state, [])
  | expressions :: rows => do
      let values ← rowValues schema columns expressions
      let stored ← match state.database.findTable? table with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      let commands ← uniqueReplacePlan stored values
      let (next, _) ← runCoreCommands state commands
      let (finalState, results) ← replaceUniqueRows next table schema columns rows
      return (finalState, { changes := 1 } :: results)

def indexNameExists (state : Core.State) (name : String) : Bool :=
  state.database.tables.any fun table => table.indexes.any fun index => index.name == canonical name

def prepareCreateTable (state : Core.State) (name : String) (ifNotExists : Bool) :
    Except String Bool := do
  if (canonical name).startsWith "sqlite_" then throw s!"object name reserved for internal use: {name}"
  if (state.database.findTable? (canonical name)).isSome then
    if ifNotExists then return false else throw s!"table already exists: {name}"
  if indexNameExists state name then throw s!"there is already an index named {name}"
  return true

/-- The target table must already have been resolved before checking the
index name. Existing indexes skip expression binding under IF NOT EXISTS. -/
def prepareCreateIndex (state : Core.State) (name : String) (ifNotExists : Bool) :
    Except String Bool := do
  if (canonical name).startsWith "sqlite_" then throw s!"object name reserved for internal use: {name}"
  if (state.database.findTable? (canonical name)).isSome then
    throw s!"there is already a table named {name}"
  if indexNameExists state name then
    if ifNotExists then return false else throw s!"index already exists: {name}"
  return true

/-- A successful schema no-op must also skip physical publication. -/
def schemaNoop (state : Core.State) : Statement → Bool
  | .createTable name _ _ ifNotExists => (prepareCreateTable state name ifNotExists).toOption == some false
  | .createIndex name table _ _ _ ifNotExists =>
      (state.database.findTable? (canonical table)).isSome &&
        (prepareCreateIndex state name ifNotExists).toOption == some false
  | _ => false

def executeStatement (state : Core.State) :
    Statement → Except String (Core.State × List Core.Result)
  | .createTable name columns constraints ifNotExists => do
      unless ← prepareCreateTable state name ifNotExists do return (state, [{}])
      executeCommand state (.createTable (← schema name columns constraints))
  | .createIndex name table expressions unique where_ ifNotExists => do
      let tableName := canonical table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      unless ← prepareCreateIndex state name ifNotExists do return (state, [{}])
      if where_.isSome then unsupported "partial index"
      else
        let columnName ← match expressions.toList with
          | [expression] => match indexColumnName? expression with
            | some name => .ok name
            | none => unsupported "index expression"
          | _ => unsupported "index expression"
        let columnIndex ← indexColumn stored.schema columnName
        executeCommand state (.createIndex tableName {
          name := canonical name, column := columnIndex, unique })
  | .insert table columns rows conflict => do
      unless conflict == .default || conflict == .abort || conflict == .replace do
        throw "unsupported general verified-MVP SQL: INSERT conflict policy"
      let tableName := canonical table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      if conflict == .replace && stored.indexes.any (·.unique) then
        replaceUniqueRows state tableName stored.schema columns rows.toList
      else
        insertRows state tableName stored.schema columns (conflict == .replace) rows.toList
  | .delete table alias where_ returning => do
      unless returning.isEmpty do
        throw "unsupported general verified-MVP SQL: DELETE RETURNING"
      let tableName := canonical table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      unless writeNamesBound stored.schema table alias #[] where_ do unsupported "unbound DELETE name"
      match where_.mapM (predicate stored.schema) with
      | .ok condition => executeCommand state (.deleteWhere tableName condition)
      | .error _ => executeExpressionDelete state tableName alias stored where_
  | .update table alias assignments where_ conflict => do
      unless conflict == .default || conflict == .abort do
        throw "unsupported general verified-MVP SQL: UPDATE conflict policy"
      let tableName := canonical table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      unless writeNamesBound stored.schema table alias assignments where_ do unsupported "unbound UPDATE name"
      match updateAssignments stored.schema assignments.toList,
          where_.mapM (predicate stored.schema) with
      | .ok updates, .ok condition =>
          executeCommand state (.updateWhere tableName updates condition)
      | _, _ =>
          if assignments.any (fun assignment =>
              findColumn? stored.schema assignment.1 == some stored.schema.primaryKey) then
            executeRekeyUpdate state tableName alias stored assignments.toList where_
          else executeExpressionUpdate state tableName alias stored assignments.toList where_
  | .select select => do
      let execution ← executeSelect state select
      return (execution.state, [execution.result])
  | .begin => executeCommand state .begin
  | .commit => executeCommand state .commit
  | .rollback => executeCommand state .rollback
  | _ => unsupported "statement"

theorem executeStatement_createTable_noop (state : Core.State) (name : String)
    (columns : Array ColumnDef) (constraints : Array TableConstraintDef) (ifNotExists : Bool)
    (skipped : prepareCreateTable state name ifNotExists = .ok false) :
    executeStatement state (.createTable name columns constraints ifNotExists) = .ok (state, [{}]) := by
  simp [executeStatement, skipped, bind, Except.bind, pure, Except.pure]

theorem executeStatement_createIndex_noop (state : Core.State) (name table : String)
    (expressions : Array Expr) (unique : Bool) (where_ : Option Expr) (ifNotExists : Bool)
    (stored : Core.Table) (found : state.database.findTable? (canonical table) = some stored)
    (skipped : prepareCreateIndex state name ifNotExists = .ok false) :
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
