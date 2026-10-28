import SQLeanite.CoreHeaderPragma
import SQLeanite.CoreIndexPrepare
import SQLeanite.CoreSQL.ObserveSingleSelect
import SQLeanite.CoreSavepoint
import SQLeanite.CoreSchemaAdd
import SQLeanite.CoreSchemaDrop
import SQLeanite.CoreSchemaDropColumn
import SQLeanite.CoreSchemaRename
import SQLeanite.SQLite.CtasCatalog

namespace SQLeanite
namespace CoreSQL

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

def prepareCreateIndex (state : Core.State) (name : String) (ifNotExists : Bool)
    (table : String := "") : Except String Bool :=
  CoreIndexPrepare.prepareCreateIndex state name ifNotExists table

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
  if state.catalog.current.filteredIndexes.any (fun index => index.definition.name.toLower == name.toLower) then return true
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
      if constraints.any (fun constraint => constraint.check.isNone && constraint.references.isNone && constraint.columns.size > 1) then
        unsupported "composite declaration requires retained SQL source"
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
