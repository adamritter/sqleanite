import SQLeanite.CoreSQL.CreateTableAsCommands
import SQLeanite.SQLite.ColumnCatalog
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
  | .createTable name .. | .createStrictTable name .. | .createWithoutRowidTable name .. | .createTableAs name .. =>
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

/-- A new CHECK or a STRICT table requests a scan of the resulting rows.
STRICT checks DEFAULT types and retained CHECKs even for an unchecked addition. -/
def executeCheckedAdd (state : Core.State) (name : String) (definition : ColumnDef)
    (strictColumns : Option (List CoreStrictSyntax.Spec) := none) :
    Except String (Core.State × List Core.Result) := do
  let bare := { definition with check := none, earlierChecks := #[], references := none, generated := none, generatedStored := false, collation := "binary" }
  let (next, results) ← CoreSQL.executeStatement state (.alterAddColumn name bare)
  let tableName := CoreSQL.resolveTableName state name
  let some before := state.database.findTable? tableName | throw "altered table is missing"
  let some after := next.database.findTable? tableName | throw "altered table is missing"
  if state.foreignKeys && definition.references.isSome && !before.rows.isEmpty then
    let position := before.schema.catalogColumns.length
    if after.rows.head?.any (fun row => row.value position != .null) then
      throw "Cannot add a REFERENCES column with non-NULL default value"
  if (CoreCheck.collect #[definition] #[]).isEmpty && strictColumns.isNone then return (next, results)
  let oldChecks ← match before.catalogSource with
    | none => pure []
    | some source => source.compiledChecks
  let columns := match CoreSchemaSQL.statements before.catalogSQL with
    | some statements => match statements.toList with
        | [.createTable _ columns _ _] | [.createStrictTable _ columns _ _] => columns.push definition
        | _ => #[definition]
    | none => #[definition]
  let checks := oldChecks ++ (CoreCheck.collect #[definition] #[]).map fun check =>
    { check with expression := CoreCollationSyntax.forTable tableName columns check.expression }
  match CoreCheck.validate after.schema checks with
  | .error message =>
      if message == "unsupported CHECK expression" then
        for check in checks do
          let expression := SQLite.Scalar.prepare (CoreCheck.bind after.schema check.expression)
          if let some diagnostic := CoreCheck.alterFunctionError tableName expression.height expression then throw diagnostic
      throw s!"error in table {tableName} after add column: {message}"
  | .ok _ => pure ()
  if let some types := strictColumns then
    for row in after.rows do
      (CoreStrictSyntax.require tableName types row.values).mapError (fun _ => "type mismatch on DEFAULT")
      CoreCheck.requireRows after.schema checks [row]
  else CoreCheck.requireRows after.schema checks after.rows
  return (next, results)

/-- Validate a STRICT addition and retain its public type separately from
its no-affinity ANY storage representation. -/
def addedColumn (state : Core.State) (name : String) (definition : ColumnDef) :
    Except String (ColumnDef × Option (List CoreStrictSyntax.Spec)) := do
  let some table := CoreNames.table? state.database name | return (definition, none)
  let some source := table.catalogSource | return (definition, none)
  let some types ← source.compiledStrictColumns | return (definition, none)
  let lowered ← (CoreStrictSyntax.lowerColumn table.schema.name #[] definition).mapError fun message =>
    s!"error in table {table.schema.name} after add column: {message}"
  let typ ← CoreStrictSyntax.typeName table.schema.name definition
  return (lowered, some (types ++ [(definition.name, typ)]))

def requireStoredEmpty (table : Core.Table) : Except String Unit :=
  if table.rows.isEmpty then .ok () else .error "cannot add a STORED column"

theorem requireStoredEmpty_rejects_nonempty (table : Core.Table)
    (nonempty : table.rows.isEmpty = false) :
    requireStoredEmpty table = .error "cannot add a STORED column" := by
  simp [requireStoredEmpty, nonempty]

/-- Validate declarations before inspecting existing rows. A populated table
rejects STORED additions before expression binding or a physical NULL rebuild. -/
def executeGeneratedAdd (state : Core.State) (name : String) (definition : ColumnDef)
    (strictColumns : Option (List CoreStrictSyntax.Spec)) :
    Except String (Core.State × List Core.Result) := do
  let before ← CoreSQL.prepareAddColumn state name definition
  let some statements := CoreSchemaSQL.statements before.catalogSQL | throw "invalid generated table source"
  let (columns,constraints) ← match statements.toList with
    | [.createTable _ columns constraints _] | [.createStrictTable _ columns constraints _] => pure (columns,constraints)
    | _ => throw "invalid generated table declaration"
  CoreGeneratedSyntax.validateDeclarations (columns.push definition) constraints
  if definition.unique then throw "Cannot add a UNIQUE column"
  requireStoredEmpty before
  let result ← executeCheckedAdd state name definition strictColumns
  let some after := CoreNames.table? result.1.database name | throw "altered table is missing"
  if let some expression := definition.generated then
    (CoreGeneratedSyntax.validateExpression after.schema
      (SQLite.Scalar.prepare (CoreCheck.bind after.schema expression))).mapError fun message =>
        s!"error in table {before.schema.name} after add column: {message}"
  return result

def compoundKeys (constraints : Array TableConstraintDef) : Bool :=
  constraints.any (fun constraint => constraint.check.isNone && constraint.references.isNone && constraint.columns.size > 1)

/-- Source-aware compound constraints retain their certified programs after
constructing the actual row table. The source-free AST model rejects them. -/
def createCompound (state : Core.State) (name : String) (columns : Array ColumnDef)
    (constraints : Array TableConstraintDef) (ifNotExists : Bool) :
    Except String (Core.State × List Core.Result) := do
  unless ← CoreSQL.prepareCreateTable state name ifNotExists do return (state,[{}])
  let admitted ← CoreSQL.schema name columns constraints
  let (next,results) ← CoreSQL.executeCommand state (.createTable admitted)
  let indexes ← CoreSQL.automaticIndexes admitted columns constraints
  let table ← Core.Table.rebuild admitted indexes []
  let database ← next.database.updateTable table
  let next := { next with database }
  let next ← if admitted.autoIncrement then CoreAutoIncrement.ensure next else pure next
  return (next,results)

/-- Retained CHECK, REFERENCES and STRICT type programs are validated before
ordinary Core table construction; the original source is attached afterwards. -/
def executeBase (state : Core.State) (statement : Statement) :
    Except String (Core.State × List Core.Result) := do
  match statement with
  | .createWithoutRowidTable name columns constraints strict ifNotExists =>
      unless ← CoreSQL.prepareCreateTable state name ifNotExists do return (state,[{}])
      let admitted ← CoreSQL.withoutRowidSchema name columns constraints strict
      CoreSQL.executeCommand state (.createTable admitted)
  | .createStrictTable name columns constraints ifNotExists =>
      if compoundKeys constraints then
        return ← createCompound state name (← CoreStrictSyntax.lower name columns constraints) constraints ifNotExists
      unless ← CoreSQL.prepareCreateTable state name ifNotExists do return (state, [{}])
      let lowered ← CoreStrictSyntax.lower name columns constraints
      let _ ← CoreSQL.schema name lowered constraints
      let bare := lowered.map fun column => { column with check := none, earlierChecks := #[], references := none, generated := none, generatedStored := false, collation := "binary" }
      let constraints := constraints.filter (fun constraint => constraint.check.isNone && constraint.references.isNone)
      CoreSQL.executeStatement state (.createTable name bare constraints ifNotExists)
  | .createTable name columns constraints ifNotExists =>
      if compoundKeys constraints then return ← createCompound state name columns constraints ifNotExists
      if (CoreCheck.collect columns constraints).isEmpty && columns.all (fun column => column.references.isNone && column.generated.isNone && column.collation.toLower == "binary") &&
          constraints.all (fun constraint => constraint.references.isNone) then
        CoreSQL.executeStatement state statement
      else do
        unless ← CoreSQL.prepareCreateTable state name ifNotExists do return (state, [{}])
        let _ ← CoreSQL.schema name columns constraints
        let columns := columns.map fun column => { column with check := none, earlierChecks := #[], references := none, generated := none, generatedStored := false, collation := "binary" }
        let constraints := constraints.filter (fun constraint => constraint.check.isNone && constraint.references.isNone)
        CoreSQL.executeStatement state (.createTable name columns constraints ifNotExists)
  | .update name alias assignments condition conflict outputs => do
      if state.internalReturning then
        if let some table := CoreNames.table? state.database name then
          if table.withoutRowid then
            return ← CoreSQL.executeUpdateReturning state table.schema.name alias table assignments.toList condition conflict outputs
      if let some table := CoreNames.table? state.database name then
        if let some source := table.catalogSource then
          unless (← source.compiledGeneratedColumns).isEmpty do
            throw "generated writes require the production row executor"
      CoreSQL.executeStatement state statement
  | .delete name alias condition outputs => do
      if state.internalReturning then
        if let some table := CoreNames.table? state.database name then
          if table.withoutRowid then
            return ← CoreSQL.executeDeleteReturning state table.schema.name alias table condition outputs
      CoreSQL.executeStatement state statement
  | .insert name .. | .insertSelect name .. => do
      if let some table := CoreNames.table? state.database name then
        if let some source := table.catalogSource then
          unless (← source.compiledGeneratedColumns).isEmpty do
            throw "generated writes require the production row executor"
      CoreSQL.executeStatement state statement
  | .createIndex _ table expressions _ _ _ => do
      if let some stored := CoreNames.table? state.database table then
        if let some source := stored.catalogSource then
          let collations ← source.compiledCollations
          for expression in expressions do
            if let some column := CoreSQL.indexColumnName? expression then
              if collations.any (fun spec => spec.1.toLower == column.toLower) then
                throw "unsupported general verified-MVP SQL: declared collation index"
      CoreSQL.executeStatement state statement
  | .alterAddColumn name definition => do
      let (definition, strictColumns) ← addedColumn state name definition
      if definition.generated.isSome then executeGeneratedAdd state name definition strictColumns
      else if strictColumns.isSome then executeCheckedAdd state name definition strictColumns
      else if (CoreCheck.collect #[definition] #[]).isEmpty && definition.references.isNone && definition.collation.toLower == "binary" then
        CoreSQL.executeStatement state (.alterAddColumn name definition)
      else executeCheckedAdd state name definition
  | .alterDropColumn name oldName => do
      let result ← CoreSQL.executeStatement state statement
      if let some table := CoreNames.table? state.database name then
        if let some source := table.catalogSource then
          let generated ← source.compiledGeneratedColumns
          if let some position := table.schema.column? oldName then
            if !generated.isEmpty && !generated.any (fun spec => spec.position == position) &&
                table.schema.catalogColumns.length == generated.length + 1 then
              throw s!"error in table {table.schema.name} after drop column: must have at least one non-generated column"
            if generated.any (fun spec => spec.position != position && spec.dependencies.contains position) then
              throw s!"error in table {table.schema.name} after drop column: no such column: {oldName}"
        if let some statements := CoreSchemaSQL.statements table.catalogSQL then
          let constraints := match statements.toList with
            | [.createTable _ _ constraints _] | [.createStrictTable _ _ constraints _] => constraints
            | _ => #[]
          for constraint in constraints do
              if constraint.references.isSome then
                if let some target := constraint.columns.find? (fun column => column.toLower == oldName.toLower) then
                  throw s!"error in table {table.schema.name} after drop column: unknown column \"{target}\" in foreign key definition"
      return result
  | _ => CoreSQL.executeStatement state statement

theorem executeBase_create_noop (state : Core.State) (name : String)
    (columns : Array ColumnDef) (constraints : Array TableConstraintDef) (ifNotExists : Bool)
    (skipped : CoreSQL.prepareCreateTable state name ifNotExists = .ok false) :
    executeBase state (.createTable name columns constraints ifNotExists) = .ok (state, [{}]) := by
  simp [executeBase, createCompound, skipped, CoreSQL.executeStatement_createTable_noop state name columns constraints ifNotExists skipped,
    bind, Except.bind, pure, Except.pure]

def executeStatement (state : Core.State) (statement : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  let (next, results) ← match executeBase state statement with
    | .error message => .error (errorMessage state statement source message)
    | .ok result => .ok result
  match statement with
  | .createTable name _ _ _ | .createStrictTable name _ _ _ | .createWithoutRowidTable name _ _ _ _ =>
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

/-- A successful source-aware STRICT construction publishes only the original
catalog text after it is checked against the lowered storage schema. -/
theorem executeStatement_strict_trace (state next : Core.State) (name source sql : String)
    (columns : Array ColumnDef) (constraints : Array TableConstraintDef) (ifNotExists : Bool)
    (results : List Core.Result)
    (executed : executeBase state (.createStrictTable name columns constraints ifNotExists) = .ok (next, results))
    (fresh : CoreSQL.schemaNoop state (.createStrictTable name columns constraints ifNotExists) = false)
    (normalized : SQLite.CreateCatalog.table source = some sql) :
    executeStatement state (.createStrictTable name columns constraints ifNotExists) source =
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
    (executed : executeBase state (.alterDropColumn name oldName) = .ok (next, results))
    (found : state.database.findTable? (CoreSQL.resolveTableName state name) = some before)
    (located : CoreSQL.indexColumn before.schema oldName = .ok position)
    (rewritten : SQLite.ColumnCatalog.dropColumn before.catalogSQL position = some sql) :
    executeStatement state (.alterDropColumn name oldName) source =
      (do let retained ← retain next (CoreSQL.resolveTableName state name) sql; pure (retained, results)) := by
  simp [executeStatement, executed, found, located, rewritten, bind, Except.bind, pure, Except.pure]

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
