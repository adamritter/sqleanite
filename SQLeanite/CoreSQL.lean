import SQLeanite.CoreEngine
import SQLeanite.CoreOptimizerBridge
import SQLeanite.CoreTokenGrammar
import SQLeanite.SQLSurface

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
  let target ← match schema.columns[index]? with
    | some target => .ok target
    | none => .error "comparison column is out of range"
  let aff := SQLite.Scalar.comparisonAffinity (some target.affinity)
    (SQLite.Scalar.expressionAffinity expression)
  unless aff == .blob || aff.comparison == target.affinity.comparison do
    unsupported "comparison requiring conversion of the stored column"
  return SQLite.PhysicalAffinity.comparison aff value

def findColumn? (schema : Core.Schema) (name : String) : Option Nat :=
  schema.columns.findIdx? (fun column => column.name == canonical name)

def column (schema : Core.Schema) (name : String) : Except String Nat :=
  match findColumn? schema name with
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
  | .column _ name => some name
  | .call "lean_dqs" #[.literal (.text name)] false => some name
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
  | { expr := .column _ name, descending } :: terms =>
      return (← column schema name, descending) :: (← orderBy schema terms)
  | _ => unsupported "ORDER BY expression"

def countTarget? (schema : Core.Schema) :
    List ResultColumn → Except String (Option Core.CountTarget)
  | [{ expr := .call name arguments star, .. }] =>
      if canonical name != "count" then .ok none
      else if star && arguments.isEmpty then .ok (some .star)
      else match arguments.toList, star with
        | [.column _ name], false => return some (.column (← column schema name))
        | _, _ => unsupported "COUNT argument"
  | _ => .ok none

def sumColumn? (schema : Core.Schema) :
    List ResultColumn → Except String (Option Nat)
  | [{ expr := .call name #[.column _ columnName] false, .. }] =>
      if canonical name == "sum" then return some (← column schema columnName)
      else .ok none
  | [{ expr := .call name _ _, .. }] =>
      if canonical name == "sum" then unsupported "SUM argument" else .ok none
  | _ => .ok none

def extremeColumn? (schema : Core.Schema) :
    List ResultColumn → Except String (Option (Bool × Nat))
  | [{ expr := .call name #[.column _ columnName] false, .. }] =>
      if canonical name == "min" then
        return some (true, ← column schema columnName)
      else if canonical name == "max" then
        return some (false, ← column schema columnName)
      else .ok none
  | [{ expr := .call name _ _, .. }] =>
      if canonical name == "min" || canonical name == "max" then
        unsupported "MIN/MAX argument"
      else .ok none
  | _ => .ok none

def groupColumns (schema : Core.Schema) : List Expr → Except String (List Nat)
  | [] => .ok []
  | .column _ name :: expressions =>
      return (← column schema name) :: (← groupColumns schema expressions)
  | _ => unsupported "GROUP BY expression"

def groupOutput (schema : Core.Schema) (groups : List Nat) :
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
          else if canonical name == "min" then
            .minColumn <$> column schema columnName
          else if canonical name == "max" then
            .maxColumn <$> column schema columnName
          else unsupported "aggregate expression"
      | _ => unsupported "group projection expression"
  | _ => unsupported "group projection expression"

def groupOutputs (schema : Core.Schema) (groups : List Nat) :
    List ResultColumn → Except String (List Core.GroupOutput)
  | [] => .ok []
  | result :: results =>
      return (← groupOutput schema groups result) ::
        (← groupOutputs schema groups results)

def rowValues (schema : Core.Schema) (insertColumns : Option (Array String))
    (expressions : Array Expr) : Except String (List Core.Value) := do
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
      let canonicalNames := names.toList.map canonical
      schema.columns.mapM fun target =>
        if target.name == "__sqleanite_rowid" && target.integerPrimaryKey then
          .ok .null
        else
        match canonicalNames.findIdx? (· == target.name) with
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
      return (index, ← columnLiteral target assignment.2) :: remaining

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
  | { expr := .column qualifier name, descending, .. } :: terms =>
      return (← joinColumn context qualifier name, descending) ::
        (← joinOrderBy context terms)
  | _ => unsupported "join ORDER BY expression"

/-- SQLite's compound operators over list-backed bags. UNION/INTERSECT/EXCEPT
remove duplicates; UNION ALL is the only multiplicity-preserving form. -/
def combineRows (operation : CompoundOp) (left right : List (List Core.Value)) :
    List (List Core.Value) :=
  CoreOptimizerBridge.compoundRows operation left right

theorem mem_combineRows (operation : CompoundOp) (left right : List (List Core.Value))
    (row : List Core.Value) :
    row ∈ combineRows operation left right ↔
      match operation with
      | .unionAll | .unionDistinct => row ∈ left ∨ row ∈ right
      | .intersect => row ∈ left ∧ row ∈ right
      | .except => row ∈ left ∧ row ∉ right := by
  cases operation <;> simp [combineRows, CoreOptimizerBridge.compoundRows,
    Core.mem_deduplicate]

theorem combineRows_nodup (operation : CompoundOp)
    (notAll : operation ≠ .unionAll) (left right : List (List Core.Value)) :
    (combineRows operation left right).Nodup := by
  cases operation with
  | unionAll => contradiction
  | unionDistinct => exact Core.deduplicate_nodup _
  | intersect => exact (Core.deduplicate_nodup left).filter _
  | except => exact (Core.deduplicate_nodup left).filter _

def RowsHaveWidth (width : Nat) (rows : List (List Core.Value)) : Prop :=
  ∀ row ∈ rows, row.length = width

theorem combineRows_width (operation : CompoundOp) (width : Nat)
    {left right : List (List Core.Value)}
    (leftWidth : RowsHaveWidth width left)
    (rightWidth : RowsHaveWidth width right) :
    RowsHaveWidth width (combineRows operation left right) := by
  intro row member
  have semantic := (mem_combineRows operation left right row).mp member
  cases operation with
  | unionAll | unionDistinct =>
      rcases semantic with member | member
      · exact leftWidth row member
      · exact rightWidth row member
  | intersect => exact leftWidth row semantic.1
  | except => exact leftWidth row semantic.1

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
def constantRow (select : Select) : Except String (Option (List Core.Value)) := do
  unless select.sources.isEmpty && select.valueRows.isNone &&
      select.groupBy.isEmpty && select.having.isNone && select.orderBy.isEmpty do
    unsupported "constant SELECT shape"
  unless select.columns.all (fun column => SQLite.Scalar.admitted column.expr) &&
      select.where_.all SQLite.Scalar.admitted do
    unsupported "constant SELECT expression"
  if select.limit == some 0 then return none
  if let some condition := select.where_ then
    unless SQLite.Numeric.truth (← SQLite.Scalar.eval condition) == .true do return none
  if select.offset > 0 then return none
  return some (← select.columns.toList.mapM (fun column => literal column.expr))

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

def executeSelectBase (state : Core.State) (select : Select) :
    Except String SelectExecution :=
  if select.sources.size = 2 then executeJoin state select
  else if select.sources.isEmpty then executeConstantSelect state select
  else do
    unless select.sources.size = 1 &&
        select.having.isNone && select.offset = 0 do
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
    let wherePredicate ← select.where_.mapM (predicate stored.schema)
    if !select.groupBy.isEmpty then
      if select.distinct || !select.orderBy.isEmpty || select.limit.isSome then
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
        if select.distinct || !select.orderBy.isEmpty || select.limit.isSome then
          unsupported "COUNT DISTINCT, ORDER BY, or LIMIT"
        else
          let (next, result) ← Core.execute state (.count tableName target wherePredicate)
          return ⟨next, result, 1⟩
      | none, some column, none =>
        if select.distinct || !select.orderBy.isEmpty || select.limit.isSome then
          unsupported "SUM DISTINCT, ORDER BY, or LIMIT"
        else
          let (next, result) ← Core.execute state (.sum tableName column wherePredicate)
          return ⟨next, result, 1⟩
      | none, none, some (minimum, column) =>
        if select.distinct || !select.orderBy.isEmpty || select.limit.isSome then
          unsupported "MIN/MAX DISTINCT, ORDER BY, or LIMIT"
        else
          let (next, result) ← Core.execute state
            (.extreme tableName minimum column wherePredicate)
          return ⟨next, result, 1⟩
      | none, none, none =>
        let query : Core.Query := {
          columns := ← projection stored.schema select.columns.toList
          predicate := wherePredicate
          orderBy := ← orderBy stored.schema select.orderBy.toList
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
      let wherePredicate ← (select.where_.mapM (predicate stored.schema)).toOption
      let count ← (countTarget? stored.schema select.columns.toList).toOption
      let sum ← (sumColumn? stored.schema select.columns.toList).toOption
      let extreme ← (extremeColumn? stored.schema select.columns.toList).toOption
      if count.isNone && sum.isNone && extreme.isNone then
        let columns ← (projection stored.schema select.columns.toList).toOption
        let ordering ← (orderBy stored.schema select.orderBy.toList).toOption
        some (tableName, {
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

def executeStatement (state : Core.State) :
    Statement → Except String (Core.State × List Core.Result)
  | .createTable name columns constraints _ => do
      executeCommand state (.createTable (← schema name columns constraints))
  | .createIndex name table expressions unique where_ _ => do
      if unique || where_.isSome then unsupported "UNIQUE or partial index"
      else
        let tableName := canonical table
        let stored ← match state.database.findTable? tableName with
          | some stored => .ok stored
          | none => .error s!"no such table: {table}"
        let columnName ← match expressions.toList with
          | [expression] => match indexColumnName? expression with
            | some name => .ok name
            | none => unsupported "index expression"
          | _ => unsupported "index expression"
        let columnIndex ← column stored.schema columnName
        executeCommand state (.createIndex tableName {
          name := canonical name, column := columnIndex })
  | .insert table columns rows conflict => do
      unless conflict == .default || conflict == .abort || conflict == .replace do
        throw "unsupported general verified-MVP SQL: INSERT conflict policy"
      let tableName := canonical table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      insertRows state tableName stored.schema columns (conflict == .replace)
        rows.toList
  | .delete table _ where_ returning => do
      unless returning.isEmpty do
        throw "unsupported general verified-MVP SQL: DELETE RETURNING"
      let tableName := canonical table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      executeCommand state (.deleteWhere tableName
        (← where_.mapM (predicate stored.schema)))
  | .update table _ assignments where_ conflict => do
      unless conflict == .default || conflict == .abort do
        throw "unsupported general verified-MVP SQL: UPDATE conflict policy"
      let tableName := canonical table
      let stored ← match state.database.findTable? tableName with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      executeCommand state (.updateWhere tableName
        (← updateAssignments stored.schema assignments.toList)
        (← where_.mapM (predicate stored.schema)))
  | .select select => do
      let execution ← executeSelect state select
      return (execution.state, [execution.result])
  | .begin => executeCommand state .begin
  | .commit => executeCommand state .commit
  | .rollback => executeCommand state .rollback
  | _ => unsupported "statement"

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
