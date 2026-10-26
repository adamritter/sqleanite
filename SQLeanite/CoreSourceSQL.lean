import SQLeanite.CoreSQL
import SQLeanite.SQLite.CreateCatalog
import SQLeanite.SQLite.Script

/-! Source-aware execution adds checked catalog spelling to the abstract CoreSQL
statement trace. CoreSQL.execute remains the AST trace model; production file
engines call this source-aware boundary before publishing a changed database. -/
namespace SQLeanite.CoreSourceSQL

def retain (state : Core.State) (name sql : String) : Except String Core.State := do
  let some table := state.database.findTable? name | throw "created table is missing"
  let retained ← table.withCatalogSQL sql
  let database ← state.database.updateTable retained
  return { state with database }

theorem retain_effect {state next : Core.State} {name sql : String}
    (success : retain state name sql = .ok next) :
    ∃ before after : Core.Table,
      state.database.findTable? name = some before ∧
      next.database.findTable? name = some after ∧
      after.schema = before.schema ∧ after.indexes = before.indexes ∧
      after.rows = before.rows ∧ after.catalogSQL = sql ∧
      (∀ other, other ≠ name →
        next.database.findTable? other = state.database.findTable? other) := by
  unfold retain at success
  cases found : state.database.findTable? name with
  | none => simp [found] at success
  | some before =>
      simp only [found] at success
      cases attached : before.withCatalogSQL sql with
      | error message => simp [attached, bind, Except.bind] at success
      | ok after =>
          cases updated : state.database.updateTable after with
          | error message => simp [attached, updated, bind, Except.bind] at success
          | ok database =>
              simp [attached, updated, bind, Except.bind, pure, Except.pure] at success
              subst next
              have kept := Core.Table.withCatalogSQL_preserves attached
              have nameEq : after.schema.name = name := by
                rw [kept.1]
                exact Core.findTable?_some_schemaName found
              refine ⟨before, after, rfl,
                Core.Database.updateTable_target found nameEq updated,
                kept.1, kept.2.1, kept.2.2.1, kept.2.2.2, ?_⟩
              intro other different
              exact Core.Database.updateTable_frame updated other (by simpa [nameEq] using different)

/-- Abstract errors name decoded identifiers; SQLite CREATE errors instead
print the source token. Only that duplicate-table error changes its spelling. -/
def errorMessage (statement : Statement) (source message : String) : String :=
  match statement with
  | .createTable name .. | .createTableAs name .. =>
      if message == s!"table already exists: {name}" then
        match SQLite.CreateCatalog.nameToken source with
        | some token => s!"table {token} already exists"
        | none => message
      else message
  | _ => message

def executeStatement (state : Core.State) (statement : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  let (next, results) ← match CoreSQL.executeStatement state statement with
    | .error message => .error (errorMessage statement source message)
    | .ok result => .ok result
  match statement with
  | .createTable name _ _ _ =>
      if CoreSQL.schemaNoop state statement then return (next, results)
      let some sql := SQLite.CreateCatalog.table source |
        throw "cannot retain CREATE TABLE source"
      let retained ← retain next name sql
      return (retained, results)
  | _ => return (next, results)

theorem executeStatement_create_noop (state : Core.State) (name source : String)
    (columns : Array ColumnDef) (constraints : Array TableConstraintDef) (ifNotExists : Bool)
    (skipped : CoreSQL.prepareCreateTable state name ifNotExists = .ok false) :
    executeStatement state (.createTable name columns constraints ifNotExists) source =
      .ok (state, [{}]) := by
  simp [executeStatement, CoreSQL.executeStatement_createTable_noop state name columns constraints ifNotExists skipped,
    CoreSQL.schemaNoop, skipped, Except.toOption, bind, Except.bind, pure, Except.pure]

theorem executeStatement_create_trace (state next : Core.State) (name source sql : String)
    (columns : Array ColumnDef) (constraints : Array TableConstraintDef) (ifNotExists : Bool)
    (results : List Core.Result)
    (executed : CoreSQL.executeStatement state (.createTable name columns constraints ifNotExists) = .ok (next, results))
    (fresh : CoreSQL.schemaNoop state (.createTable name columns constraints ifNotExists) = false)
    (normalized : SQLite.CreateCatalog.table source = some sql) :
    executeStatement state (.createTable name columns constraints ifNotExists) source =
      (do let retained ← retain next name sql; pure (retained, results)) := by
  simp [executeStatement, executed, fresh, normalized, bind, Except.bind, pure, Except.pure]

theorem executeStatement_error (state : Core.State) (statement : Statement) (source message : String)
    (failed : CoreSQL.executeStatement state statement = .error message) :
    executeStatement state statement source = .error (errorMessage statement source message) := by
  simp [executeStatement, failed, bind, Except.bind]

def runStatements (source : String) : Core.State → List Statement →
    Except String (Core.State × List Core.Result)
  | state, [] => .ok (state, [])
  | state, statement :: statements => do
      let (next, results) ← executeStatement state statement source
      let (finalState, remaining) ← runStatements source next statements
      pure (finalState, results ++ remaining)

def runChunks : Core.State → List String → Except String (Core.State × List Core.Result)
  | state, [] => .ok (state, [])
  | state, source :: sources => do
      let parsed ← CoreTokenGrammar.parseCertified source
      let (next, results) ← runStatements source state parsed.statements.toList
      let (finalState, remaining) ← runChunks next sources
      pure (finalState, results ++ remaining)

/-- Pure source-aware execution for the same chunks used by both file engines. -/
def execute (state : Core.State) (sql : String) : Except String (Core.State × List Core.Result) :=
  runChunks state (SQLite.Script.split sql)

end SQLeanite.CoreSourceSQL
