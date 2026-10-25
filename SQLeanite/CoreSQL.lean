import SQLeanite.CoreJoinUsing
import SQLeanite.CoreSavepoint
import SQLeanite.CoreAutoIncrement
import SQLeanite.CoreEngine
import SQLeanite.CoreNames
import SQLeanite.CoreCreateTableAs
import SQLeanite.CoreSchemaPragma
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
import SQLeanite.CoreDefaultConflict
import SQLeanite.CoreNullConflict
import SQLeanite.CoreInsertIgnore
import SQLeanite.CoreUpdateIgnore
import SQLeanite.CoreUpdateReplace
import SQLeanite.CoreUpdateScan
import SQLeanite.SQLite.Values
import SQLeanite.SQLite.StaticCondition

namespace SQLeanite
namespace CoreSQL

def unsupported (feature : String) : Except String α :=
  .error s!"unsupported general verified-MVP SQL: {feature}"

def canonical (name : String) : String := name.toLower

def resolveTableName (state : Core.State) (name : String) : String :=
  CoreNames.tableName state.database name

/-- Exact public type spelling after SQLite's standard-type normalization. -/
def declaredTypeName := SQLite.ColumnType.name

def ordinaryColumn (definition : ColumnDef) : Core.Column :=
  if (SQLite.ColumnType.adjusted definition.declaredType).isEmpty then
    { name := definition.name, notNull := definition.notNull }
  else Core.Column.typed definition.name (declaredTypeName definition.declaredType) definition.notNull

def columnAllowed (column : ColumnDef) : Bool :=
  SQLite.ColumnType.valid column.declaredType &&
  (column.defaultValue.isSome == column.defaultSql.isSome) &&
  column.generated.isNone && !column.unique &&
  column.references.isNone && column.check.isNone && (!column.autoIncrement || column.primaryKey) &&
  column.collation.toLower == "binary" &&
  (column.conflict == .abort || column.conflict == .ignore || column.conflict == .replace) &&
  (column.primaryKey || column.conflict == .abort) &&
  (column.notNullConflict == .abort || column.notNullConflict == .ignore || column.notNullConflict == .replace) &&
  (column.notNull || column.notNullConflict == .abort)

def columnWithConflicts (definition : ColumnDef) (column : Core.Column) : Except String Core.Column := do
  let policy ← match definition.notNullConflict with
    | .abort => pure Core.NotNullConflict.abort
    | .ignore => pure Core.NotNullConflict.ignore
    | .replace => pure Core.NotNullConflict.replace
    | _ => unsupported "schema NOT NULL conflict policy"
  let column ← match column.withNotNullConflict policy with
    | some column => pure column
    | none => unsupported "NOT NULL policy without an explicit constraint"
  let primary ← match definition.conflict with
    | .abort => pure Core.NotNullConflict.abort
    | .ignore => pure Core.NotNullConflict.ignore
    | .replace => pure Core.NotNullConflict.replace
    | _ => unsupported "schema PRIMARY KEY conflict policy"
  let column ← match column.withPrimaryConflict primary with
    | some column => pure column
    | none => unsupported "primary policy without a PRIMARY KEY constraint"
  for (_, source) in definition.earlierDefaults do
    unless (ColumnDefault.fromSource source).isSome do unsupported "earlier DEFAULT expression"
  match definition.defaultSql with
  | none => return column
  | some source =>
      let some spec := ColumnDefault.fromSource source | unsupported "DEFAULT expression"
      return { column with defaultValue := some spec }

/-- Mark a table-level key without changing column order, names or other
column constraints. The caller validates that its target exists uniquely. -/
def markPrimaryColumn (name : String) (definitions : Array ColumnDef) (conflict : ConflictAction := .abort)
    (autoIncrement : Bool := false) : Array ColumnDef :=
  definitions.map fun column =>
    if canonical column.name == canonical name then { column with primaryKey := true, conflict, autoIncrement }
    else column

theorem markPrimaryColumn_size (name : String) (definitions : Array ColumnDef) (conflict : ConflictAction := .abort)
    (autoIncrement : Bool := false) :
    (markPrimaryColumn name definitions conflict autoIncrement).size = definitions.size := by
  simp [markPrimaryColumn]

theorem markPrimaryColumn_names (name : String) (definitions : Array ColumnDef) (conflict : ConflictAction := .abort)
    (autoIncrement : Bool := false) :
    (markPrimaryColumn name definitions conflict autoIncrement).toList.map (·.name) = definitions.toList.map (·.name) := by
  simp only [markPrimaryColumn, Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro column _
  simp only [Function.comp_apply]
  split <;> rfl

/-- Single-column table keys lower to the same Core key as column declarations.
Unlike column-level INTEGER PRIMARY KEY DESC, table-level DESC still aliases
the rowid in SQLite. Its index-only collation/direction therefore has no effect.
TEXT keys require the admitted ascending BINARY index representation. -/
def tablePrimaryColumns (definitions : Array ColumnDef)
    (constraints : Array TableConstraintDef) : Except String (Array ColumnDef) :=
  match constraints.toList with
  | [] => .ok definitions
  | [constraint] => do
      unless constraint.primaryKey && constraint.columns.size == 1 &&
          constraint.check.isNone &&
          (constraint.conflict == .abort || constraint.conflict == .ignore || constraint.conflict == .replace) do
        unsupported "table constraint"
      unless constraint.collations.size == 1 && constraint.descending.size == 1 do
        unsupported "table key metadata width"
      if definitions.any (·.primaryKey) then throw "table has more than one primary key"
      let name := constraint.columns[0]!
      let column ← match definitions.toList.find? (fun column => canonical column.name == canonical name) with
        | some column => .ok column
        | none => .error s!"no such column: {name}"
      let integerAlias := SQLite.ColumnType.standard column.declaredType == some "INTEGER"
      unless integerAlias || (!constraint.descending[0]! &&
          constraint.collations[0]!.all (fun name => canonical name == "binary")) do
        unsupported "table key index collation or direction"
      return markPrimaryColumn name definitions constraint.conflict constraint.autoIncrement
  | _ => unsupported "multiple table constraints"

theorem tablePrimaryColumns_empty (definitions : Array ColumnDef) :
    tablePrimaryColumns definitions #[] = .ok definitions := rfl

def schema (name : String) (definitions : Array ColumnDef)
    (constraints : Array TableConstraintDef) : Except String Core.Schema := do
  let definitions ← tablePrimaryColumns definitions constraints
  unless definitions.toList.all columnAllowed do
    throw "unsupported general verified-MVP SQL: column constraint"
  let foldedNames := definitions.toList.map (fun column => canonical column.name)
  unless foldedNames.eraseDups.length == foldedNames.length do
    throw "duplicate column name"
  let primaryKeys := definitions.toList.filter (·.primaryKey)
  if primaryKeys.isEmpty then
    let visibleColumns ← definitions.toList.mapM fun column => columnWithConflicts column (ordinaryColumn column)
    unless !visibleColumns.isEmpty do throw "table must have at least one column"
    if visibleColumns.any (fun column => canonical column.name == "__sqleanite_rowid") then
      throw "reserved verified column name: __sqleanite_rowid"
    return {
      name := name
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
  let integerAlias := SQLite.ColumnType.standard primaryDefinition.declaredType == some "INTEGER"
  unless !primaryDefinition.autoIncrement || integerAlias do
    throw "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"
  let ordinary := ordinaryColumn primaryDefinition
  let indexedType : Core.IndexedType := {
    declaredType := ordinary.declaredType, explicitEmptyType := ordinary.explicitEmptyType,
    explicitEmptyTypeOnly := fun present => (ordinary.explicitEmptyTypeOnly present).1 }
  let visibleColumns ← definitions.toList.mapM fun column => columnWithConflicts column <|
    if column.primaryKey then {
      name := column.name
      notNull := integerAlias || column.notNull
      integerPrimaryKey := integerAlias
      integerPrimaryNotNull := integerAlias && column.notNull
      autoIncrement := integerAlias && column.autoIncrement
      autoIncrementOnly := fun present => (Bool.and_eq_true_iff.mp present).1
      textPrimaryKey := !integerAlias
      indexedType := if integerAlias || indexedType.declaredType == "TEXT" then none else some indexedType
      indexedTypeOnly := by
        split
        · simp
        · next custom => simp_all }
    else ordinaryColumn column
  if integerAlias then return {
    name := name
    columns := visibleColumns
    primaryKey
    declaredPrimaryKey := primaryKey }
  else
    let hiddenName := "__sqleanite_rowid"
    if visibleColumns.any (fun column => canonical column.name == hiddenName) then
      throw s!"reserved verified column name: {hiddenName}"
    return {
      name := name
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

def rowValues (schema : Core.Schema) (insertColumns : Option (Array String))
    (expressions : Array Expr) : Except String (List Core.Value) := do
  -- Repeated targets keep the first ordinary value and the last rowid value.
  -- SQLite still binds discarded expressions and functions before assignment.
  unless expressions.all SQLite.Scalar.admitted do unsupported "INSERT expression"
  if expressions.isEmpty then
    let _ ← insertColumns.mapM (fun names => names.toList.mapM (column schema))
    return ← schema.columns.mapM Core.Column.defaultForInsert
  match insertColumns with
  | none =>
      unless expressions.size = schema.visibleColumns.length do
        throw s!"table {schema.name} has {schema.visibleColumns.length} columns but {expressions.size} values were supplied"
      let visibleValues ← expressions.toList.mapM literal
      let pairs := schema.visibleColumnIndices.zip visibleValues
      schema.columns.mapIdxM fun index target =>
        match pairs.find? (fun pair => pair.1 == index) with
        | some pair => .ok (SQLite.PhysicalAffinity.write target.affinity pair.2)
        | none => target.defaultForInsert
  | some names =>
      unless names.size = expressions.size do
        throw "INSERT column/value count mismatch"
      let indices ← names.toList.mapM (column schema)
      schema.columns.mapIdxM fun targetIndex target =>
        match insertValueIndex schema.primaryKey targetIndex indices with
        | some index => columnLiteral target expressions[index]!
        | none => target.defaultForInsert

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
def inputRowValues (schema : Core.Schema) (columns : Option (Array String))
    (evaluateAll : Bool) (expressions : Array Expr) : Except String (List Core.Value) := do
  if !evaluateAll then return ← rowValues schema columns expressions
  unless expressions.all SQLite.Scalar.admitted do unsupported "INSERT expression"
  match columns with
  | none =>
      unless expressions.size = schema.visibleColumns.length do throw "INSERT column/value count mismatch"
  | some names =>
      unless names.size = expressions.size do throw "INSERT column/value count mismatch"
      discard <| names.toList.mapM (column schema)
  rowValues schema columns (← evaluateInsertExpressions expressions)

@[simp] theorem inputRowValues_single (schema : Core.Schema)
    (columns : Option (Array String)) (expressions : Array Expr) :
    inputRowValues schema columns false expressions = rowValues schema columns expressions := by
  simp [inputRowValues]

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

/-- RETURNING forces the two-phase UPDATE path even for IGNORE. Values are
read from the current pending row; its original name binds RETURNING while the
UPDATE alias remains the source for RHS and WHERE expressions. -/
def updateReturningRow (state : Core.State) (tableName : String) (ctx outputCtx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (conflict : ConflictAction) (projection : List Expr)
    (rowid : Core.Integer) : Except String (Core.State × Option (List Core.Value)) := do
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {tableName}"
  let some row := stored.findRowid? rowid | return (state, none)
  let updates ← evaluateAssignments ctx row assignments
  let values := Core.applyAssignments row.values updates
  let prepared ← if conflict == .default || conflict == .replace then
      CoreNullConflict.prepare ctx.schema values true (if conflict == .replace then some .replace else none)
    else pure (some values)
  let some values := prepared | return (state, none)
  let outcome ← if conflict == .default then
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
  CoreReturning.updatedOutput outputCtx values projection outcome

theorem updateReturningRow_missing (state : Core.State) (tableName : String)
    (ctx outputCtx : CoreExpr.Context) (assignments : List (Nat × Expr)) (conflict : ConflictAction)
    (projection : List Expr) (rowid : Core.Integer) (stored : Core.Table)
    (found : state.database.findTable? tableName = some stored) (missing : stored.findRowid? rowid = none) :
    updateReturningRow state tableName ctx outputCtx assignments conflict projection rowid = .ok (state, none) := by
  simp [updateReturningRow, found, missing, bind, Except.bind, pure, Except.pure]

def updateReturningRows (state : Core.State) (tableName : String) (ctx outputCtx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (conflict : ConflictAction) (projection : List Expr) :
    List Core.Integer → Except String (Core.State × List (List Core.Value))
  | [] => .ok (state, [])
  | rowid :: rowids => do
      let (next, output) ← updateReturningRow state tableName ctx outputCtx assignments conflict projection rowid
      let (finalState, outputs) ← updateReturningRows next tableName ctx outputCtx assignments conflict projection rowids
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
    (conflict : ConflictAction) (returning : Array ResultColumn) :
    Except String (Core.State × List Core.Result) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let outputCtx : CoreExpr.Context := { schema := stored.schema, sourceName := tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  if conflict == .default || conflict == .replace then
    CoreNullConflict.validate stored.schema (bound.map Prod.fst) (if conflict == .replace then some .replace else none)
  let projection ← CoreReturning.prepare outputCtx returning.toList
  let trace ← expressionDeletePlan tableName alias stored condition
  let rowids ← CoreUpdateReplace.pending tableName stored.schema.primaryKey trace
  let (next, outputs) ← updateReturningRows state tableName ctx outputCtx bound conflict projection rowids
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
          if CoreJoinUsing.merges context.shared name li ri then .ok ⟨.left, li⟩
          else .error s!"ambiguous column name: {name}"
      | [] => .error s!"no such column: {name}"
      | _ => .error s!"ambiguous column name: {name}"

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
  | some (qualifier, name) => .column <$> joinColumn context qualifier name
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

theorem joinOperandAffinity_plus (context : JoinContext) (expression : Expr)
    (operand : CoreJoin.Operand) : joinOperandAffinity context (.unary .plus expression) operand = .ok none := rfl

def joinOperandCoerce (context : JoinContext) (aff : SQLite.Affinity) :
    CoreJoin.Operand → Except String CoreJoin.Operand
  | .literal value => .ok (.literal (SQLite.PhysicalAffinity.comparison aff value))
  | operand@(.column reference) => do
      let target ← joinColumnDefinition context reference
      if aff == .blob || aff.comparison == target.affinity.comparison then return operand
      return .coercedColumn aff reference
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

def joinResultExpr (context : JoinContext) : Expr → Except String (List CoreJoin.Operand)
  | .column qualifier name => return [.column (← joinColumn context qualifier name)]
  | .star none =>
      .ok ((joinVisibleColumns .left context.leftSchema ++
        (joinVisibleColumns .right context.rightSchema).filter
          (fun reference => !CoreJoinUsing.suppressesRight context.shared reference.column)).map
            CoreJoin.Operand.column)
  | .star (some qualifier) =>
      let owner := canonical qualifier
      if owner == context.leftName then
        .ok ((joinVisibleColumns .left context.leftSchema).map CoreJoin.Operand.column)
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
  | .coercedColumn .. => unsupported "coerced join output ordering"

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
    shared := ← CoreJoinUsing.columns leftSchema rightSchema rightSource }

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
      leftSource.joinOn.isNone && !rightSource.rightJoin do
    throw "unsupported general verified-MVP SQL: only two-table INNER/CROSS/comma/LEFT JOIN"
  unless select.groupBy.isEmpty && select.having.isNone do
    throw "unsupported general verified-MVP SQL: join SELECT shape"
  unless canonical leftSource.name = canonical leftTable &&
      canonical rightSource.name = canonical rightTable do
    throw "join source/schema mismatch"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  if context.leftName == context.rightName then
    throw "join sources require distinct names or aliases"
  let explicitOn ← rightSource.joinOn.mapM (fun expression => joinPredicate context expression rightSource.leftJoin)
  let sharedOn ← joinUsingPredicate context
  let on := match explicitOn, sharedOn with
    | none, predicate | predicate, none => predicate
    | some left, some right => some (CoreJoin.Predicate.and left right)
  let where_ ← select.where_.mapM (joinPredicate context)
  let orderColumns ← joinOrderColumns context select.columns.toList
  let orderBy ← joinOrderBy context orderColumns select.orderBy.toList
  let mayExchange := !rightSource.leftJoin && !rightSource.crossJoin
  let lookupScanOrder := joinLookupScanOrder leftSchema rightSchema mayExchange on where_ orderBy
  return {
    columns := ← joinProjection context select.columns.toList
    on
    kind := if rightSource.leftJoin then .left else .inner
    rightWidth := rightSchema.columns.length
    where_
    orderBy
    limit := select.limit
    offset := select.offset
    distinct := select.distinct
    lookupScanOrder
    distinctScanOrder := joinDistinctScanOrder leftSchema rightSchema
      mayExchange
      (on.any (joinHasRowidEquality leftSchema rightSchema) ||
        where_.any (joinHasRowidEquality leftSchema rightSchema))
      (orderBy.map (fun term => (term.reference, term.descending))) }

/-- LIMIT zero still resolves the original predicates and validates every
operation that SQLite would generate, but emits no predicate value evaluation.
Projection, ordering and source checks retain the ordinary join translator. -/
def joinZeroLayout (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query := do
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

/-- An outer ON expression has no candidate pair to evaluate when either
input is empty. Resolution/code-generation checks still use the original ON;
WHERE and every other query component retain ordinary translation. -/
def joinEmptyOnQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query := do
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless rightSource.leftJoin && (leftRows.isEmpty || rightRows.isEmpty) do
    unsupported "outer ON requires an empty input"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  for expression in rightSource.joinOn.toList do
    let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
    unless joinStaticAdmitted context prepared true do
      unsupported "unbound or invalid empty-input outer ON"
  joinQueryWithZero { select with sources := #[leftSource, { rightSource with joinOn := none }] }
    leftTable rightTable leftSchema rightSchema

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

def executeJoin (state : Core.State) (select : Select) :
    Except String SelectExecution := do
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless leftSource.subquerySql.isNone && rightSource.subquerySql.isNone &&
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
  let query ← joinQueryForRows select leftTable rightTable left.schema right.schema left.rows right.rows
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
  let (_, result) ← Core.execute state (.query (resolveTableName state source.name) query)
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
  let inputs ← if !enabled then pure [] else do
    let (_, result) ← Core.execute state (.query (resolveTableName state source.name)
      { columns := List.range stored.schema.columns.length, predicate := search })
    CoreAggregate.selectRows ctx select.where_ result.rows
  let values ← prepared.results.accumulate ctx inputs
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
    unless source.subquerySql.isNone && source.joinOn.isNone do
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
          unsupported "unbound SELECT result or ordering name"
        let resolved := { select with where_ := select.where_.map (CoreOrder.resolveAliases ctx select.columns.toList) }
        return ← executeExpressionSelect state resolved source stored none
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
    if source.subquerySql.isNone && source.joinOn.isNone then
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

/-- Bind identifiers and expand stars before resolving each output column's
explicit or declared collation. A supported join projects only stored columns,
whose admitted schema collation is BINARY. -/
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
      let query ← joinQueryForRows { select with orderBy := #[], offset := 0 }
        (resolveTableName state leftSource.name) (resolveTableName state rightSource.name) left.schema right.schema left.rows right.rows
      return List.replicate query.columns.length (some "binary")
  | _ => unsupported "compound source shape"

/-- multiSelectCollSeq takes the first arm that supplies a collation for each
output position. An unused later unknown name must not replace an earlier one. -/
def resultCollationsFuel : Nat → Core.State → Select → Except String (List (Option String))
  | 0, _, _ => .error "compound collation depth exhausted"
  | fuel + 1, state, select => do
      let first ← baseResultCollations state select
      select.compounds.toList.foldlM (fun current (_, arm) => do
        let next ← if arm.valueRows.isSome then baseResultCollations state arm true
          else resultCollationsFuel fuel state arm
        unless current.length == next.length do
          throw "SELECTs to the left and right of a compound operator must have the same number of result columns"
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
  | sources =>
      let mut columns := []
      for column in select.columns do
        match column.expr with
        | .star qualifier =>
            for source in sources do
              if qualifier.all (fun q => q.toLower == (source.alias.getD source.name).toLower) then
                let some stored := state.database.findTable? (resolveTableName state source.name) | throw s!"no such table: {source.name}"
                columns := columns ++ stored.schema.catalogColumns.map (fun c =>
                  { expr := .column (some (source.alias.getD source.name)) c.name })
        | _ => columns := columns ++ [column]
      return { columns, context := none }

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
  for arm in base :: select.compounds.toList.map (·.2) do
    let validated ← run state { arm with orderBy := #[], limit := some 0, offset := 0 }
    unless validated.width == names.length do
      throw "SELECTs to the left and right of a compound operator must have the same number of result columns"
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
        let base ← executeSelectBase state { select with compounds := #[] }
        let rec executeCollatedArms (current : SelectExecution) :
            List (CompoundOp × Select) → Except String SelectExecution
          | [] => .ok current
          | (operation, arm) :: arms => do
              let next ← executeSelectFuel fuel current.state arm
              unless current.width == next.width do
                throw "SELECTs to the left and right of a compound operator must have the same number of result columns"
              let combined : SelectExecution := {
                state := next.state
                result := { rows := CoreCompound.combineCollated kinds operation current.result.rows next.result.rows }
                width := current.width }
              executeCollatedArms combined arms
        return ← executeCollatedArms base select.compounds.toList
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
    (width : Nat) : Except String Unit := do
  match columns with
  | none =>
      unless width == schema.visibleColumns.length do
        throw s!"table {schema.name} has {schema.visibleColumns.length} columns but {width} values were supplied"
  | some names =>
      let _ ← names.toList.mapM (column schema)
      unless width == names.size do throw "INSERT column/value count mismatch"

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
def insertReturningRow (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (input : Array Expr)
    (evaluateAll : Bool := false) :
    Except String (Core.State × Option (List Core.Value)) := do
  let values ← inputRowValues schema columns evaluateAll input
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {tableName}"
  if conflict == .default then
    let prepared ← CoreDefaultConflict.plan stored values none
    match prepared with
    | none => return (state, none)
    | some (row, trace) =>
        let (next, _) ← runCoreCommands state trace
        let output ← ctx.projectRow row.values projection
        return (next, some output)
  if conflict == .ignore then
    unless ← CoreInsertIgnore.shouldInsert stored values do return (state, none)
  let values ← if conflict == .replace then do
      let some prepared ← CoreNullConflict.prepare stored.schema values false (some .replace)
        | throw "unexpected ignored REPLACE row"
      pure prepared
    else pure values
  let row ← stored.createRow values
  let trace ← if conflict == .replace then uniqueReplacePlan stored row.values
    else pure [Core.Command.insert tableName row.values]
  let (next, _) ← runCoreCommands state trace
  let output ← ctx.projectRow row.values projection
  return (next, some output)

theorem insertReturningRow_ignored (state : Core.State) (tableName : String)
    (schema : Core.Schema) (columns : Option (Array String)) (ctx : CoreExpr.Context)
    (projection : List Expr) (input : Array Expr) (values : List Core.Value) (stored : Core.Table)
    (converted : rowValues schema columns input = .ok values)
    (found : state.database.findTable? tableName = some stored)
    (skip : CoreInsertIgnore.shouldInsert stored values = .ok false) :
    insertReturningRow state tableName schema columns .ignore ctx projection input = .ok (state, none) := by
  simp [insertReturningRow, converted, found, skip, bind, Except.bind, pure, Except.pure]

def insertReturningRows (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr)
    (inputs : List (Array Expr)) (evaluateAll : Bool := false) :
    Except String (Core.State × List (List Core.Value)) :=
  match inputs with
  | [] => .ok (state, [])
  | input :: inputs => do
      let (next, output) ← insertReturningRow state tableName schema columns conflict ctx projection input evaluateAll
      let (finalState, outputs) ← insertReturningRows next tableName schema columns conflict ctx projection inputs evaluateAll
      return (finalState, output.toList ++ outputs)

theorem insertReturningRows_length_le (state : Core.State) (tableName : String)
    (schema : Core.Schema) (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (inputs : List (Array Expr))
    (next : Core.State) (outputs : List (List Core.Value)) (evaluateAll : Bool)
    (success : insertReturningRows state tableName schema columns conflict ctx projection inputs evaluateAll = .ok (next, outputs)) :
    outputs.length ≤ inputs.length := by
  induction inputs generalizing state next outputs with
  | nil =>
      simp [insertReturningRows] at success
      rcases success with ⟨_, rfl⟩
      simp
  | cons input inputs ih =>
      cases head : insertReturningRow state tableName schema columns conflict ctx projection input evaluateAll with
      | error message => simp [insertReturningRows, head, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨middle, output⟩
          cases tail : insertReturningRows middle tableName schema columns conflict ctx projection inputs evaluateAll with
          | error message => simp [insertReturningRows, head, tail, bind, Except.bind] at success
          | ok pair =>
              rcases pair with ⟨finalState, more⟩
              simp [insertReturningRows, head, tail, bind, Except.bind, pure, Except.pure] at success
              rcases success with ⟨_, rfl⟩
              have bound := ih middle finalState more tail
              cases output <;> simp_all <;> omega

def executeInsertReturning (state : Core.State) (table : String) (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) (conflict : ConflictAction) (returning : Array ResultColumn) :
    Except String (Core.State × List Core.Result) := do
  unless conflict == .default || conflict == .abort || conflict == .replace || conflict == .ignore do
    throw "unsupported general verified-MVP SQL: INSERT conflict policy"
  let tableName := resolveTableName state table
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := tableName }
  let projection ← CoreReturning.prepare ctx returning.toList
  let inputs ← match source with
    | .inl rows => pure rows.toList
    | .inr query => do
        let selection ← executeSelect state query
        checkInsertSelectColumns stored.schema columns selection.width
        prepareInsertSelectionDefaults stored.schema columns conflict
        selection.result.rows.mapM selectedRowExpressions
  let evaluateAll := match source with
    | .inl rows => 1 < rows.size
    | .inr _ => false
  let (next, outputs) ← insertReturningRows state tableName stored.schema columns conflict ctx projection inputs evaluateAll
  return (next, [{ rows := outputs, changes := outputs.length }])

/-- AUTOINCREMENT candidates use the existing checked conflict/RETURNING
executor after an explicit rowid has been allocated. The private counter is
threaded through ignored rows, without exposing it to the statement's SELECT. -/
def autoInsertRows (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (counter : CoreAutoIncrement.Context)
    (inputs : List (Array Expr)) (evaluateAll : Bool) :
    Except String (Core.State × CoreAutoIncrement.Context × List (Option (List Core.Value))) :=
  match inputs with
  | [] => .ok (state, counter, [])
  | input :: inputs => do
      let values ← inputRowValues schema columns evaluateAll input
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {tableName}"
      let (counter, values) ← CoreAutoIncrement.prepare stored counter values
      let literals ← selectedRowExpressions values
      let (next, output) ← insertReturningRow state tableName schema none conflict ctx projection literals
      let (finalState, finalCounter, outputs) ← autoInsertRows next tableName schema columns conflict
        ctx projection counter inputs evaluateAll
      return (finalState, finalCounter, output :: outputs)

def executeAutoInsert (state : Core.State) (table : String) (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) (conflict : ConflictAction) (returning : Array ResultColumn) :
    Except String (Core.State × List Core.Result) := do
  unless conflict == .default || conflict == .abort || conflict == .replace || conflict == .ignore do
    throw "unsupported general verified-MVP SQL: INSERT conflict policy"
  let tableName := resolveTableName state table
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  let counter ← CoreAutoIncrement.beginContext state tableName
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := tableName }
  let projection ← CoreReturning.prepare ctx returning.toList
  let inputs ← match source with
    | .inl rows => pure rows.toList
    | .inr query => do
        let selection ← executeSelect state query
        checkInsertSelectColumns stored.schema columns selection.width
        prepareInsertSelectionDefaults stored.schema columns conflict
        selection.result.rows.mapM selectedRowExpressions
  let evaluateAll := match source with
    | .inl rows => 1 < rows.size
    | .inr _ => false
  let (next, counter, outputs) ← autoInsertRows state tableName stored.schema columns conflict ctx projection
    counter inputs evaluateAll
  let next ← CoreAutoIncrement.finish next counter
  if returning.isEmpty then
    let results : List Core.Result := outputs.map fun output => { changes := if output.isSome then 1 else 0 }
    return (next, results)
  else
    let rows := outputs.flatMap Option.toList
    return (next, [{ rows, changes := rows.length }])

def automaticTable (state : Core.State) (name : String) : Bool :=
  (state.database.findTable? (resolveTableName state name)).any (fun stored => stored.schema.autoIncrement)

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
  let selection ← executeSelect state query
  let definitions ← CoreCreateTableAs.columns state.database query
  unless definitions.size == selection.width do throw "CTAS output width mismatch"
  let schema ← schema name definitions #[]
  let inputs ← selection.result.rows.mapM selectedRowExpressions
  let values ← inputs.mapM (rowValues schema none)
  return .createTable schema :: values.map (Core.Command.insert name)

def executeCreateTableAs (state : Core.State) (name : String) (query : Select)
    (ifNotExists : Bool) : Except String (Core.State × List Core.Result) := do
  unless ← prepareCreateTable state name ifNotExists do return (state, [{}])
  let commands ← createTableAsCommands state name query
  let (next, _) ← runCoreCommands state commands
  return (next, [{}])

theorem executeCreateTableAs_trace (state : Core.State) (name : String)
    (query : Select) (ifNotExists : Bool) (commands : List Core.Command)
    (fresh : prepareCreateTable state name ifNotExists = .ok true)
    (planned : createTableAsCommands state name query = .ok commands) :
    executeCreateTableAs state name query ifNotExists =
      (fun outcome => (outcome.1, [{}])) <$> runCoreCommands state commands := by
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
          canonical index.name == canonical name && index.isImplicitPrimary stored.schema) then
        throw "index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped"
      return true

/-- A successful schema no-op must also skip physical publication. -/
def schemaNoop (state : Core.State) : Statement → Bool
  | .dropTable name ifExists => (prepareDropTable state name ifExists).toOption == some false
  | .dropIndex name ifExists => (prepareDropIndex state name ifExists).toOption == some false
  | .createTable name _ _ ifNotExists | .createTableAs name _ ifNotExists =>
      (prepareCreateTable state name ifNotExists).toOption == some false
  | .createIndex name table _ _ _ ifNotExists =>
      (state.database.findTable? (resolveTableName state table)).isSome &&
        (prepareCreateIndex state name ifNotExists (resolveTableName state table)).toOption == some false
  | _ => false

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
      let tableName := resolveTableName state table
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {table}"
      if canonical tableName == CoreAutoIncrement.sequenceName then throw "table sqlite_sequence may not be altered"
      if stored.schema.catalogColumns.any (fun column => canonical column.name == canonical definition.name) then
        throw s!"duplicate column name: {definition.name}"
      unless stored.schema.catalogColumns.length < SQLite.Limits.maxColumns do
        throw "too many columns"
      unless columnAllowed definition && !definition.primaryKey &&
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
      if automaticTable state table then executeAutoInsert state table columns (.inr query) conflict returning
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
      let admitted ← schema name columns constraints
      if admitted.autoIncrement then
        let (next, results) ← executeCommand state (.createTable admitted)
        let next ← CoreAutoIncrement.ensure next
        return (next, results)
      else executeCommand state (.createTable admitted)
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
      if !returning.isEmpty then
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
      unless writeNamesBound stored.schema table alias assignments where_ do unsupported "unbound UPDATE name"
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
  | .pragma name argument schema => CoreSchemaPragma.execute state name argument schema
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
