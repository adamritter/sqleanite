import SQLeanite.CoreAggregate
import SQLeanite.CoreNullConflict

/-! RETURNING expressions use the modified table's original name, not its
DELETE alias. Output is materialized before a successful statement is exposed.
Callers support scalar INSERT/UPDATE/DELETE RETURNING on admitted Core tables. -/
namespace SQLeanite.CoreReturning

/-- A write candidate retains its expression metadata until RETURNING has
finished. Only `value` crosses the Core row and file boundaries. -/
structure Cell where
  value : Core.Value
  subtype : UInt8 := 0

def Cell.plain (value : Core.Value) : Cell := ⟨value, 0⟩

def Cell.fromScalar (value : SQLite.ScalarValue) : Except String Cell := do
  return ⟨← SQLSurface.value value.value, value.subtype⟩

def literal (expression : Expr) : Except String Cell := do
  unless SQLite.Scalar.admitted expression do
    SQLSurface.unsupported "non-constant or unsupported expression"
  Cell.fromScalar (← SQLite.Scalar.evalTypedWith
    (fun _ _ => .error "unsupported constant expression") SQLite.Scalar.expressionAffinity expression)

def Cell.writeAffinity (affinity : SQLite.Affinity) (cell : Cell) : Cell :=
  ⟨SQLite.PhysicalAffinity.write affinity cell.value,
    if SQLite.PhysicalAffinity.clearsSubtype affinity cell.value then 0 else cell.subtype⟩

def columnLiteral (column : Core.Column) (expression : Expr) : Except String Cell := do
  let input ← literal expression
  return input.writeAffinity column.affinity

def defaultValue (column : Core.Column) (spec : ColumnDefault.Spec) : Except String Cell := do
  let expression ← ColumnDefault.expression spec.source
  columnLiteral column (ColumnDefault.emittedFuel expression.height expression)

def defaultForInsert (column : Core.Column) : Except String Cell := do
  if column.integerPrimaryKey then return Cell.plain .null
  match column.defaultValue with
  | none => return Cell.plain .null
  | some spec => defaultValue column spec

/-- Omitted defaults occupy reusable statement registers. Each successful
record write applies affinity to the current register representation again. -/
def defaultFromRegister (column : Core.Column) (cached : Option Cell) : Except String Cell :=
  match cached with
  | some value => .ok (value.writeAffinity column.affinity)
  | none => defaultForInsert column

theorem Cell.writeAffinity_value (affinity : SQLite.Affinity) (cell : Cell) :
    (cell.writeAffinity affinity).value = SQLite.PhysicalAffinity.write affinity cell.value := rfl

theorem defaultFromRegister_reuse (column : Core.Column) (value : Cell) :
    defaultFromRegister column (some value) = .ok (value.writeAffinity column.affinity) := rfl

def prepareValues (schema : Core.Schema) (values : List Cell) (updating : Bool)
    (override : Option Core.NotNullConflict := none) : Except String (Option (List Cell)) :=
  CoreNullConflict.prepareWith (·.value) defaultValue schema values updating override

/-- Rowid allocation and MustBeInt supply a fresh integer register. Other
columns keep their evaluated tag through affinity application. -/
def lookup (ctx : CoreExpr.Context) (values : List Cell)
    (qualifier : Option String) (name : String) : Except String SQLite.ScalarValue := do
  let some index := ctx.column? qualifier name | throw s!"no such column: {name}"
  let some input := values[index]? | throw "row expression column is outside the input row"
  return ⟨← CoreExpr.value input.value, if index == ctx.schema.primaryKey then 0 else input.subtype,1,none⟩

def project (ctx : CoreExpr.Context) (values : List Cell) (expressions : List Expr) :
    Except String (List Core.Value) :=
  expressions.mapM fun expression => do
    let output ← SQLite.Scalar.evalTypedWith (lookup ctx values) ctx.affinity (ctx.bindNames expression)
    SQLSurface.value output.value

/-- Core can allocate a rowid while validating the candidate. The checked
physical row replaces the physical fields without inventing subtype metadata. -/
def withValues (inputs : List Cell) (values : List Core.Value) : List Cell :=
  values.zipIdx.map fun (value, index) => ⟨value, ((inputs[index]?).map (·.subtype)).getD 0⟩

/-- Function binding in trigger.c's RETURNING expansion precedes zero-AND
simplification. Column binding still follows the ordinary expression rules. -/
def prepare (ctx : CoreExpr.Context) (columns : List ResultColumn) : Except String (List Expr) := do
  for column in columns do
    if column.expr.any (fun expression => match expression with
        | .star (some _) => true | _ => false) then
      throw "RETURNING may not use TABLE.* wildcards"
    if let some message := SQLite.Scalar.aggregateMisuseFuel column.expr.height column.expr then
      throw message
    if (ctx.bindNames column.expr).any (fun expression => match expression with
        | .call .. => SQLite.Scalar.forbidden expression | _ => false) then
      throw "unsupported function or invalid function arguments in RETURNING"
  let expressions ← ctx.projection columns
  unless ctx.internalProjection || decide (expressions.length ≤ SQLite.Limits.maxColumns) do throw "too many columns in result set"
  return expressions

/-- A skipped point update supplies no RETURNING row and never evaluates
its output expressions. Accepted point updates materialize their new values. -/
def updatedOutput (ctx : CoreExpr.Context) (values : List Cell) (expressions : List Expr)
    (outcome : Core.State × Core.Result) : Except String (Core.State × Option (List Core.Value)) := do
  if outcome.2.changes == 0 then return (outcome.1, none)
  let output ← project ctx values expressions
  return (outcome.1, some output)

theorem updatedOutput_zero (ctx : CoreExpr.Context) (values : List Cell) (expressions : List Expr)
    (state : Core.State) (result : Core.Result) (skipped : result.changes = 0) :
    updatedOutput ctx values expressions (state, result) = .ok (state, none) := by
  simp [updatedOutput, skipped, pure, Except.pure]

/-- Only exact rowid deletions produced by the DELETE planner can supply an
old row. Missing rows and other command shapes are errors, never omissions. -/
def deletedRow? (stored : Core.Table) : Core.Command → Option Core.Row
  | .deleteWhere table (some (.equal column (.integer rowid))) =>
      if table == stored.schema.name && column == stored.schema.primaryKey then stored.findRowid? rowid
      else none
  | _ => none

def deletionOutput (stored : Core.Table) (ctx : CoreExpr.Context) (expressions : List Expr) :
    List Core.Command → Except String (List (List Core.Value))
  | [] => .ok []
  | command :: commands => do
      let some row := deletedRow? stored command | throw "RETURNING deletion row is missing"
      let output ← ctx.projectRow row.values expressions
      let outputs ← deletionOutput stored ctx expressions commands
      return output :: outputs

/-- Successful materialization emits exactly one output per planned deletion. -/
theorem deletionOutput_length (stored : Core.Table) (ctx : CoreExpr.Context) (expressions : List Expr)
    (commands : List Core.Command) (outputs : List (List Core.Value))
    (success : deletionOutput stored ctx expressions commands = .ok outputs) :
    outputs.length = commands.length := by
  induction commands generalizing outputs with
  | nil => simpa [deletionOutput] using success
  | cons command commands ih =>
      cases found : deletedRow? stored command with
      | none => simp [deletionOutput, found] at success
      | some row =>
          cases projected : ctx.projectRow row.values expressions with
          | error message => simp [deletionOutput, found, projected, bind, Except.bind] at success
          | ok output =>
              cases rest : deletionOutput stored ctx expressions commands with
              | error message => simp [deletionOutput, found, projected, rest, bind, Except.bind] at success
              | ok tail =>
                  simp [deletionOutput, found, projected, rest, bind, Except.bind, pure, Except.pure] at success
                  subst outputs
                  simpa using ih tail rest

theorem withValues_physical (inputs : List Cell) (values : List Core.Value) :
    (withValues inputs values).map (·.value) = values := by
  simp [withValues, List.map_map, Function.comp_def]

theorem lookup_rowid (ctx : CoreExpr.Context) (values : List Cell)
    (qualifier : Option String) (name : String)
    (bound : ctx.column? qualifier name = some ctx.schema.primaryKey) :
    lookup ctx values qualifier name = do
      let some input := values[ctx.schema.primaryKey]?
        | throw "row expression column is outside the input row"
      return ⟨← CoreExpr.value input.value,0,1,none⟩ := by
  simp [lookup, bound] <;> rfl

end SQLeanite.CoreReturning
