import SQLeanite.CoreSQL.ResolveTableName
import SQLeanite.CoreUpdateIgnore
import SQLeanite.CoreUpdateReplace
import SQLeanite.CoreUpdateScan

namespace SQLeanite
namespace CoreSQL

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
  let ctx : CoreExpr.Context := { schema := stored.schema, rowidAliases := !stored.withoutRowid, sourceName := alias.getD tableName }
  let bound ← expressionAssignments ctx assignments
  let _ ← condition.mapM ctx.validate
  unless ← ctx.constantMatches condition do return []
  let search ← expressionSearch ctx stored condition
  let ctx := expressionSearchContext ctx search
  unless ← expressionSearchReady ctx search condition do return []
  rowUpdateCommands tableName ctx bound condition (stored.rows.filter (Core.selects search))

def rekeyUpdatePlan (tableName : String) (alias : Option String) (stored : Core.Table)
    (assignments : List (String × Expr)) (condition : Option Expr) : Except String RekeyBatch := do
  let ctx : CoreExpr.Context := { schema := stored.schema, rowidAliases := !stored.withoutRowid, sourceName := alias.getD tableName }
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
  let ctx : CoreExpr.Context := { schema := stored.schema, internalProjection := state.internalReturning, rowidAliases := !stored.withoutRowid, sourceName := alias.getD tableName }
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
  let ctx : CoreExpr.Context := { schema := stored.schema, internalProjection := state.internalReturning, rowidAliases := !stored.withoutRowid, sourceName := alias.getD tableName }
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
    (condition : Option Expr) (internalProjection : Bool := false) : Except String (List Core.Command) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, internalProjection, rowidAliases := !stored.withoutRowid, sourceName := alias.getD tableName }
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
  let ctx : CoreExpr.Context := { schema := stored.schema, internalProjection := state.internalReturning, rowidAliases := !stored.withoutRowid, sourceName := alias.getD tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  CoreNullConflict.validate stored.schema (bound.map Prod.fst) (some .replace)
  let trace ← expressionDeletePlan tableName alias stored condition
  let rowids ← CoreUpdateReplace.pending tableName stored.schema.primaryKey trace
  let (next, results) ← replacedUpdateRows state tableName ctx bound rowids
  return (next, [{ changes := (results.map (·.changes)).sum }])

end CoreSQL

end SQLeanite
