import SQLeanite.SQLite.ColumnCatalog
import SQLeanite.SQLite.RenameTableCatalog
import SQLeanite.SQLite.AlterCatalog
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

/-- build.c reports the original schema token, including its quote style. -/
def pragmaSchemaToken (source : String) : Option String := do
  let chars := source.toList
  let tokens ← (SQLite.CreateCatalog.spans (chars.length+1) 0 chars []).toOption
  let rest ← SQLite.CreateCatalog.afterKeyword "PRAGMA" tokens
  match rest with
  | schema :: dot :: _ =>
      if dot.token == .symbol "." then
        some (String.ofList (chars.drop schema.start |>.take (schema.finish-schema.start)))
      else none
  | _ => none

/-- Source-aware SQL diagnostics preserve SQLite's identifier spelling and
ALTER context. The abstract Core operation and its error trace are unchanged. -/
def errorMessage (state : Core.State) (statement : Statement) (source message : String) : String :=
  match statement with
  | .pragma _ _ (some schema) =>
      if message == s!"unknown database {schema}" then
        match pragmaSchemaToken source with
        | some token => s!"unknown database {token}"
        | none => message
      else message
  | .createTable name .. | .createTableAs name .. =>
      if message == s!"table already exists: {name}" then
        match SQLite.CreateCatalog.nameToken source with
        | some token => s!"table {token} already exists"
        | none => message
      else message
  | .alterRenameTable _ newName =>
      if message == s!"table already exists: {newName}" then
        s!"there is already another table or index with this name: {newName}"
      else message
  | .alterRenameColumn name oldName newName =>
      if message == s!"duplicate column name: {newName}" then
        s!"error in table {CoreSQL.resolveTableName state name} after rename: {message}"
      else if message == s!"no such column: {oldName}" then
        s!"no such column: \"{oldName}\""
      else message
  | .alterDropColumn name oldName =>
      if message == s!"no such column: {oldName}" then
        s!"no such column: \"{oldName}\""
      else if message == "cannot drop a missing, last, primary-key or indexed column" then
        match state.database.findTable? (CoreSQL.resolveTableName state name) with
        | none => message
        | some table => match CoreSQL.indexColumn table.schema oldName with
          | .error _ => message
          | .ok position =>
              if position == table.schema.primaryKey || table.schema.declaredPrimaryKey? == some position then
                s!"cannot drop PRIMARY KEY column: \"{oldName}\""
              else if table.schema.catalogColumns.length == 1 then
                s!"cannot drop column \"{oldName}\": no other columns exist"
              else message
      else message
  | _ => message

theorem errorMessage_pragma_schema (state : Core.State) (name schema source token : String)
    (argument : Option Expr) (found : pragmaSchemaToken source = some token) :
    errorMessage state (.pragma name argument (some schema)) source
      s!"unknown database {schema}" = s!"unknown database {token}" := by
  simp [errorMessage, found]

/-- Adding a new CHECK makes SQLite scan the resulting table, including its
old CHECK clauses. Merely adding an unchecked column does not request that scan. -/
def executeCheckedAdd (state : Core.State) (name : String) (definition : ColumnDef) :
    Except String (Core.State × List Core.Result) := do
  let bare := { definition with check := none, earlierChecks := #[], references := none }
  let (next, results) ← CoreSQL.executeStatement state (.alterAddColumn name bare)
  let tableName := CoreSQL.resolveTableName state name
  let some before := state.database.findTable? tableName | throw "altered table is missing"
  let some after := next.database.findTable? tableName | throw "altered table is missing"
  if state.foreignKeys && definition.references.isSome && !before.rows.isEmpty then
    let position := before.schema.catalogColumns.length
    if after.rows.head?.any (fun row => row.value position != .null) then
      throw "Cannot add a REFERENCES column with non-NULL default value"
  if (CoreCheck.collect #[definition] #[]).isEmpty then return (next, results)
  let oldChecks ← match before.catalogSource with
    | none => pure []
    | some source => source.compiledChecks
  let checks := oldChecks ++ CoreCheck.collect #[definition] #[]
  match CoreCheck.validate after.schema checks with
  | .error message =>
      if message == "unsupported CHECK expression" then
        for check in checks do
          let expression := SQLite.Scalar.prepare (CoreCheck.bind after.schema check.expression)
          if let some diagnostic := CoreCheck.alterFunctionError tableName expression.height expression then throw diagnostic
      throw s!"error in table {tableName} after add column: {message}"
  | .ok _ => pure ()
  CoreCheck.requireRows after.schema checks after.rows
  return (next, results)

/-- CHECK declarations need their retained text before the first DML can run.
The source-free Core SQL entry point rejects them rather than silently dropping
constraints. Here only table construction is sanitized; the original source is
validated and retained by executeStatement before its result is returned. -/
def executeBase (state : Core.State) (statement : Statement) :
    Except String (Core.State × List Core.Result) := do
  match statement with
  | .createTable name columns constraints ifNotExists =>
      if (CoreCheck.collect columns constraints).isEmpty && columns.all (fun column => column.references.isNone) then
        CoreSQL.executeStatement state statement
      else do
        unless ← CoreSQL.prepareCreateTable state name ifNotExists do return (state, [{}])
        let _ ← CoreSQL.schema name columns constraints
        let columns := columns.map fun column => { column with check := none, earlierChecks := #[], references := none }
        let constraints := constraints.filter (fun constraint => constraint.check.isNone)
        CoreSQL.executeStatement state (.createTable name columns constraints ifNotExists)
  | .alterAddColumn name definition =>
      if (CoreCheck.collect #[definition] #[]).isEmpty && definition.references.isNone then
        CoreSQL.executeStatement state statement
      else executeCheckedAdd state name definition
  | _ => CoreSQL.executeStatement state statement

theorem executeBase_create_noop (state : Core.State) (name : String)
    (columns : Array ColumnDef) (constraints : Array TableConstraintDef) (ifNotExists : Bool)
    (skipped : CoreSQL.prepareCreateTable state name ifNotExists = .ok false) :
    executeBase state (.createTable name columns constraints ifNotExists) = .ok (state, [{}]) := by
  simp [executeBase, skipped, CoreSQL.executeStatement_createTable_noop state name columns constraints ifNotExists skipped,
    bind, Except.bind, pure, Except.pure]

def executeStatement (state : Core.State) (statement : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  let (next, results) ← match executeBase state statement with
    | .error message => .error (errorMessage state statement source message)
    | .ok result => .ok result
  match statement with
  | .createTable name _ _ _ =>
      if CoreSQL.schemaNoop state statement then return (next, results)
      let some sql := SQLite.CreateCatalog.table source |
        throw "cannot retain CREATE TABLE source"
      let retained ← retain next name sql
      return (retained, results)
  | .alterRenameColumn name oldName newName =>
      let tableName := CoreSQL.resolveTableName state name
      let some before := state.database.findTable? tableName | throw "altered table is missing"
      let position ← CoreSQL.indexColumn before.schema oldName
      let some sql := SQLite.ColumnCatalog.renameColumn before.catalogSQL source oldName newName position |
        throw "cannot retain renamed column source"
      let retained ← retain next tableName sql
      return (retained, results)
  | .alterDropColumn name oldName =>
      let tableName := CoreSQL.resolveTableName state name
      let some before := state.database.findTable? tableName | throw "altered table is missing"
      let position ← CoreSQL.indexColumn before.schema oldName
      let some sql := SQLite.ColumnCatalog.dropColumn before.catalogSQL position |
        throw "cannot retain dropped column source"
      let retained ← retain next tableName sql
      return (retained, results)
  | .alterRenameTable name newName =>
      let tableName := CoreSQL.resolveTableName state name
      let some before := state.database.findTable? tableName | throw "altered table is missing"
      let some sql := SQLite.RenameTableCatalog.rename before.catalogSQL newName |
        throw "cannot retain renamed table source"
      let retained ← retain next newName sql
      return (retained, results)
  | .alterAddColumn name _ =>
      let tableName := CoreSQL.resolveTableName state name
      let some before := state.database.findTable? tableName | throw "altered table is missing"
      let some sql := SQLite.AlterCatalog.addColumn before.catalogSQL source |
        throw s!"error in table {before.schema.name} after add column: incomplete input"
      let retained ← retain next tableName sql
      return (retained, results)
  | _ => return (next, results)

theorem executeStatement_create_noop (state : Core.State) (name source : String)
    (columns : Array ColumnDef) (constraints : Array TableConstraintDef) (ifNotExists : Bool)
    (skipped : CoreSQL.prepareCreateTable state name ifNotExists = .ok false) :
    executeStatement state (.createTable name columns constraints ifNotExists) source =
      .ok (state, [{}]) := by
  simp [executeStatement, executeBase_create_noop state name columns constraints ifNotExists skipped,
    CoreSQL.schemaNoop, skipped, Except.toOption, bind, Except.bind, pure, Except.pure]

theorem executeStatement_create_trace (state next : Core.State) (name source sql : String)
    (columns : Array ColumnDef) (constraints : Array TableConstraintDef) (ifNotExists : Bool)
    (results : List Core.Result)
    (executed : executeBase state (.createTable name columns constraints ifNotExists) = .ok (next, results))
    (fresh : CoreSQL.schemaNoop state (.createTable name columns constraints ifNotExists) = false)
    (normalized : SQLite.CreateCatalog.table source = some sql) :
    executeStatement state (.createTable name columns constraints ifNotExists) source =
      (do let retained ← retain next name sql; pure (retained, results)) := by
  simp [executeStatement, executed, fresh, normalized, bind, Except.bind, pure, Except.pure]

theorem executeStatement_error (state : Core.State) (statement : Statement) (source message : String)
    (failed : executeBase state statement = .error message) :
    executeStatement state statement source = .error (errorMessage state statement source message) := by
  simp [executeStatement, failed, bind, Except.bind]

/-- The column-data operation completes first; the retained SQL must independently
parse to its resulting schema before the source-aware result is published. -/
theorem executeStatement_add_trace (state next : Core.State) (name source sql : String)
    (definition : ColumnDef) (before : Core.Table) (results : List Core.Result)
    (executed : executeBase state (.alterAddColumn name definition) = .ok (next, results))
    (found : state.database.findTable? (CoreSQL.resolveTableName state name) = some before)
    (rewritten : SQLite.AlterCatalog.addColumn before.catalogSQL source = some sql) :
    executeStatement state (.alterAddColumn name definition) source =
      (do let retained ← retain next (CoreSQL.resolveTableName state name) sql; pure (retained, results)) := by
  simp [executeStatement, executed, found, rewritten, bind, Except.bind, pure, Except.pure]

theorem executeStatement_add_incomplete (state next : Core.State) (name source : String)
    (definition : ColumnDef) (before : Core.Table) (results : List Core.Result)
    (executed : executeBase state (.alterAddColumn name definition) = .ok (next, results))
    (found : state.database.findTable? (CoreSQL.resolveTableName state name) = some before)
    (incomplete : SQLite.AlterCatalog.addColumn before.catalogSQL source = none) :
    executeStatement state (.alterAddColumn name definition) source =
      .error s!"error in table {before.schema.name} after add column: incomplete input" := by
  simp [executeStatement, executed, found, incomplete, bind, Except.bind] <;> rfl

/-- Only the table-name token is changed in an admitted table definition.
The rewritten SQL is checked against the renamed schema before publication. -/
theorem executeStatement_renameTable_trace (state next : Core.State)
    (name newName source sql : String) (before : Core.Table) (results : List Core.Result)
    (executed : CoreSQL.executeStatement state (.alterRenameTable name newName) = .ok (next, results))
    (found : state.database.findTable? (CoreSQL.resolveTableName state name) = some before)
    (rewritten : SQLite.RenameTableCatalog.rename before.catalogSQL newName = some sql) :
    executeStatement state (.alterRenameTable name newName) source =
      (do let retained ← retain next newName sql; pure (retained, results)) := by
  simp [executeStatement, executeBase, executed, found, rewritten, bind, Except.bind, pure, Except.pure]

/-- Data/schema changes and source rewriting must both succeed before publication. -/
theorem executeStatement_renameColumn_trace (state next : Core.State)
    (name oldName newName source sql : String) (position : Nat) (before : Core.Table) (results : List Core.Result)
    (executed : CoreSQL.executeStatement state (.alterRenameColumn name oldName newName) = .ok (next, results))
    (found : state.database.findTable? (CoreSQL.resolveTableName state name) = some before)
    (located : CoreSQL.indexColumn before.schema oldName = .ok position)
    (rewritten : SQLite.ColumnCatalog.renameColumn before.catalogSQL source oldName newName position = some sql) :
    executeStatement state (.alterRenameColumn name oldName newName) source =
      (do let retained ← retain next (CoreSQL.resolveTableName state name) sql; pure (retained, results)) := by
  simp [executeStatement, executeBase, executed, found, located, rewritten, bind, Except.bind, pure, Except.pure]

/-- Data/schema changes and source rewriting must both succeed before publication. -/
theorem executeStatement_dropColumn_trace (state next : Core.State)
    (name oldName source sql : String) (position : Nat) (before : Core.Table) (results : List Core.Result)
    (executed : CoreSQL.executeStatement state (.alterDropColumn name oldName) = .ok (next, results))
    (found : state.database.findTable? (CoreSQL.resolveTableName state name) = some before)
    (located : CoreSQL.indexColumn before.schema oldName = .ok position)
    (rewritten : SQLite.ColumnCatalog.dropColumn before.catalogSQL position = some sql) :
    executeStatement state (.alterDropColumn name oldName) source =
      (do let retained ← retain next (CoreSQL.resolveTableName state name) sql; pure (retained, results)) := by
  simp [executeStatement, executeBase, executed, found, located, rewritten, bind, Except.bind, pure, Except.pure]

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
