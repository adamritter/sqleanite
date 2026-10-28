import SQLeanite.CoreTriggerSQL
import SQLeanite.CoreScalarQuery

namespace SQLeanite.CoreTriggerProgram

abbrev Executor := Core.State → Statement → String → Except String (Core.State × List Core.Result)
abbrev ScopedRead := Bool → Core.State → List CoreScalarQuery.Frame → Select → Except String Core.Result

def eventMatches (statement : Statement) (trigger : CoreCatalogData.Trigger) : Bool :=
  let definition := trigger.definition
  let owner := definition.table.toLower
  match statement, definition.event with
  | .insert table .., .insert | .insertSelect table .., .insert => table.toLower == owner
  | .delete table .., .delete => table.toLower == owner
  | .update table .., .update => table.toLower == owner
  | .update table _ assignments .., .updateOf columns =>
      table.toLower == owner && assignments.any (fun assignment =>
        columns.any (fun column => column.toLower == assignment.1.toLower))
  | _, _ => false

def programs (state : Core.State) (statement : Statement) : List CoreCatalogData.Trigger :=
  (state.catalog.current.triggers.filter (eventMatches statement)).reverse

def frame (state : Core.State) (table : Core.Table) (name : String) (row : List Core.Value) :
    Except String CoreScalarQuery.Frame := do
  let declarations ← match table.catalogSource with
    | none => pure []
    | some source => source.compiledCollations
  return {
    context := { schema := table.schema, sourceName := name, storedTexts := state.catalog.storedTexts }
    row
    declarations }

def frames (state : Core.State) (table : Core.Table) (statement : Statement)
    (old new : List Core.Value) : Except String (List CoreScalarQuery.Frame) := do
  match statement with
  | .insert .. | .insertSelect .. => return [← frame state table "new" new]
  | .delete .. => return [← frame state table "old" old]
  | _ => return [← frame state table "old" old, ← frame state table "new" new]

/-- Only explicit OLD/NEW qualifiers enter the lexical parent scope. Ordinary
unqualified names continue to belong to the body statement's local table. -/
def bindExpression (ctx : CoreExpr.Context) (parents : List CoreScalarQuery.Frame)
    (expression : Expr) : Except String Expr := do
  let expression ← CoreScalarQuery.bind ctx parents [] (expression.height + 1) expression
  if let some message := SQLite.Scalar.resolutionError
      (fun q n => (ctx.column? q n).isSome) expression then throw message
  return expression

def bindStatement (state : Core.State) (parents : List CoreScalarQuery.Frame)
    (statement : Statement) : Except String Statement := do
  let empty : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  let context := fun table alias => do
    let some stored := CoreNames.table? state.database table | throw s!"no such table: main.{table}"
    return ({ schema := stored.schema, sourceName := alias.getD table } : CoreExpr.Context)
  match statement with
  | .insert table columns rows conflict returning =>
      return .insert table columns (← rows.mapM (·.mapM (bindExpression empty parents))) conflict returning
  | .update table alias assignments condition conflict returning =>
      let ctx ← context table alias
      return .update table alias (← assignments.mapM fun (name,value) =>
        return (name, ← bindExpression ctx parents value)) (← condition.mapM (bindExpression ctx parents)) conflict returning
  | .delete table alias condition returning =>
      let ctx ← context table alias
      return .delete table alias (← condition.mapM (bindExpression ctx parents)) returning
  | .select .. => return statement
  | _ => throw "unsupported trigger body statement"

/-- Rowid names are resolved against the actual target schema, including a
user column which shadows one of SQLite's three implicit rowid names. -/
def rowidName (table : Core.Table) : Except String String := do
  let ctx : CoreExpr.Context := { schema := table.schema, sourceName := table.schema.name }
  let names := (table.schema.columns[table.schema.primaryKey]?.map (·.name)).toList ++ ["rowid","_rowid_","oid"]
  let some name := names.find? (fun name => ctx.column? none name == some table.schema.primaryKey)
    | throw "unsupported fully shadowed trigger rowid"
  return name

def returning : Statement → Array ResultColumn
  | .insert _ _ _ _ columns | .insertSelect _ _ _ _ columns |
      .update _ _ _ _ _ columns | .delete _ _ _ columns => columns
  | _ => #[]

/-- changes() is restored after each trigger frame. total_changes() remains
dynamic so later outer rows observe the writes of earlier trigger programs. -/
def bindEntryChanges (changes : Nat) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
    let bind := bindEntryChanges changes fuel
    match expression with
    | .call name args star =>
        if args.isEmpty && !star && name.toLower == "changes" then
          .literal (.integer changes)
        else .call name (args.map bind) star
    | .unary op arg => .unary op (bind arg)
    | .binary op left right => .binary op (bind left) (bind right)
    | .isNull arg negated => .isNull (bind arg) negated
    | .inList arg values negated affinity => .inList (bind arg) (values.map bind) negated affinity
    | .collate arg name => .collate (bind arg) name
    | .case_ base branches other =>
        .case_ (base.map bind) (branches.map fun (a,b) => (bind a,bind b)) (other.map bind)
    | .inSubquery arg sql negated => .inSubquery (bind arg) sql negated
    | other => other

def bindCounters (state : Core.State) (statement : Statement) : Statement :=
  let visit := fun expression => bindEntryChanges state.lastChanges expression.height expression
  match statement with
  | .insert table columns rows conflict outputs =>
      .insert table columns (rows.map (·.map visit)) conflict (outputs.map fun col => { col with expr := visit col.expr })
  | .insertSelect table columns query conflict outputs =>
      .insertSelect table columns (CoreLastInsert.mapSelect visit query.compoundHeight query) conflict
        (outputs.map fun col => { col with expr := visit col.expr })
  | .update table alias assignments condition conflict outputs =>
      .update table alias (assignments.map fun (name,value) => (name, visit value)) (condition.map visit) conflict
        (outputs.map fun col => { col with expr := visit col.expr })
  | .delete table alias condition outputs =>
      .delete table alias (condition.map visit) (outputs.map fun col => { col with expr := visit col.expr })
  | other => other

theorem bindEntryChanges_other (changes fuel : Nat) (name : String)
    (other : name.toLower ≠ "changes") :
    bindEntryChanges changes (fuel + 1) (.call name #[] false) =
      .call name #[] false := by
  simp [bindEntryChanges, other]

theorem programs_empty (state : Core.State) (statement : Statement)
    (empty : state.catalog.current.triggers = []) : programs state statement = [] := by
  simp [programs, empty]

theorem bindCounters_no_dml (state : Core.State) (query : Select) :
    bindCounters state (.select query) = .select query := rfl

end SQLeanite.CoreTriggerProgram
