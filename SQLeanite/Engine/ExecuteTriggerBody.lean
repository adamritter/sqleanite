import SQLeanite.Engine.ConstantDefault

namespace SQLeanite

def executeTriggerBody (db : Database) (context : Env)
    (body : Array Statement) : Except String Database := do
  if body.any Statement.callsDirectOnly then throw "unsafe use of testdirectonly()"
  let mut state := db
  for action in body do
    match action with
    | .insert target columns rows conflict =>
      let values ← rows.mapM fun row => row.mapM (evalWithDb state context)
      let (next, _) ← insertValueRowsBase state target columns values conflict
      state := next
    | .insertSelect target columns query conflict =>
      let rows ← evalMiniSelect state context query
      let (next, _) ← insertValueRowsBase state target columns rows conflict
      state := next
    | .delete target alias where_ _ =>
      let targetTable ← optionOr (findTable? state target) s!"no such table: {target}"
      let targetRef : TableRef := { name := target, alias }
      let mut victims := #[]
      for row in targetTable.rows do
        let env := makeBindings targetRef targetTable row ++ context.map Binding.outerScoped
        if ← matchesWhere state env where_ then victims := victims.push row
      unless victims.isEmpty do
        let retained := targetTable.retainRows fun row => !victims.any (·.rowid == row.rowid)
        state := replaceTable state retained
        state ← applyDeleteEffects state targetTable victims
    | .update target alias assignments where_ _ =>
      let mut targetTable ← optionOr (findTable? state target) s!"no such table: {target}"
      let targetRef : TableRef := { name := target, alias }
      let originals := targetTable.rows
      for row in originals do
        let env := makeBindings targetRef targetTable row ++ context.map Binding.outerScoped
        if ← matchesWhere state env where_ then
          let mut values := row.values
          let mut rowid := row.rowid
          for (column, expression) in assignments do
            let value ← evalWithDb state env expression
            if isRowidName column then rowid ← optionOr value.toInt? "datatype mismatch"
            else
              let index ← optionOr (targetTable.columns.findIdx? fun candidate =>
                nameEq candidate.name column) s!"no such column: {column}"
              if targetTable.columns[index]!.generated.isSome then
                throw s!"cannot UPDATE generated column \"{column}\""
              values := values.set! index (targetTable.columns[index]!.applyAffinity value)
          values ← evaluateGeneratedColumns targetTable rowid values
          let rows := targetTable.rows.map fun candidate =>
            if candidate.rowid == row.rowid then { row with values, rowid } else candidate
          let advanced := { targetTable with
            nextRowid := max targetTable.nextRowid (rowid + 1) }
          targetTable ← advanced.withRowsChecked rows
      state := replaceTable state targetTable
    | .select query =>
      if query.columns.any (fun result => match result.expr with
          | .call name _ _ => nameEq name "raise"
          | _ => false) then
        let shouldRun ← matchesWhere state context query.where_
        if shouldRun then
          for result in query.columns do
            if let .call name args _ := result.expr then
              if nameEq name "raise" then
                let message ← match args[1]? with
                  | some expression => evalWithDb state context expression
                  | none => pure (.text "constraint failed")
                throw (toString message)
      discard <| evalMiniSelect state context query
    | _ => pure ()
  pure state

def fireInsertTriggers (db : Database) (table : Table)
    (inserted : Array StoredRow) : Except String Database := do
  let mut state := db
  for row in inserted do
    let context := makeBindings { name := table.name, alias := some "new" } table row
    for trigger in state.triggers do
      if nameEq trigger.table table.name && trigger.event == .insert then
        let enabled ← match trigger.when_ with
          | none => pure true
          | some condition => pure ((← evalWithDb state context condition).truth == .true)
        if enabled then state ← executeTriggerBody state context trigger.body
  pure state

def fireUpdateTriggers (db : Database) (table : Table)
    (updated : Array (StoredRow × StoredRow)) (timing : TriggerTiming) : Except String Database := do
  let mut state := db
  for (old, new) in updated do
    let oldEnv := makeBindings { name := table.name, alias := some "old" } table old
    let newEnv := makeBindings { name := table.name, alias := some "new" } table new
    let context := oldEnv ++ newEnv
    for trigger in state.triggers do
      if nameEq trigger.table table.name && trigger.event == .update && trigger.timing == timing then
        let enabled ← match trigger.when_ with
          | none => pure true
          | some condition => pure ((← evalWithDb state context condition).truth == .true)
        if enabled then state ← executeTriggerBody state context trigger.body
  pure state

def insertValueRows (db : Database) (tableName : String) (names : Option (Array String))
    (rows : Array (Array Value)) (conflict : ConflictAction := .default) : Except String (Database × QueryResult) := do
  if (findView? db tableName).isSome then throw s!"cannot modify {tableName} because it is a view"
  if conflict != .replace then insertValueRowsBase db tableName names rows conflict
  else
    let mut state := db
    let mut table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
    let mut changes := 0
    for values in rows do
      let candidate ← makeInsertedRow table names values
      let (row, skip) ← enforceNotNull table candidate conflict
      if skip then continue
      if ← enforceChecks state table row conflict then continue
      validateForeignKeys state table row
      let conflicts := if !table.hasDeclaredUniqueness && row.rowid >= table.nextRowid then #[] else
        table.rows.filterMap fun old => (conflictTarget? table row old).map (old, ·)
      if !conflicts.isEmpty then
        let victims := conflicts.map (·.1)
        if state.recursiveTriggers then
          -- REPLACE runs BEFORE DELETE programs while the victim is still
          -- visible. Their writes can therefore consume the pending rowid.
          state ← fireDeleteTriggers state table victims (some .before)
          table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
        table := table.retainRows fun old => !victims.any (·.rowid == old.rowid)
        state := replaceTable state table
        state ← applyDeleteEffects state table victims state.recursiveTriggers
        table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
      let remaining := table.rows.findSome? fun old => (conflictTarget? table row old).map (old, ·)
      if let some (_, target) := remaining then throw (conflictMessage table target)
      table ← table.insertChecked row
      state := replaceTable state table
      state := recordAutoincrement state table row.rowid
      state := { state with lastInsertRowid := row.rowid }
      changes := changes + 1
    if rows.isEmpty then state := recordAutoincrement state table 0
    pure (state, mutationResult db changes)

def executeCreateTable (db : Database) (name : String)
    (defs : Array ColumnDef) (constraints : Array TableConstraintDef)
    (ifNotExists : Bool) : Except String (Database × QueryResult) := do
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    else if findTable? db name |>.isSome then
      if ifNotExists then pure (db, {}) else throw s!"table {name} already exists"
    else if db.indexes.any (fun index => nameEq index.name name) then
      throw s!"there is already an index named {name}"
    else
      let primaryKeyCount := defs.foldl (init := 0) (fun count definition =>
          count + if definition.primaryKey then 1 else 0) +
        constraints.foldl (init := 0) (fun count constraint =>
          count + if constraint.primaryKey then 1 else 0)
      if primaryKeyCount > 1 then
        throw s!"table \"{unqualifiedName name}\" has more than one primary key"
      let mut columns ← defs.mapM fun (d : ColumnDef) => do
        if d.defaultValue.any (fun expression => expression.hasParameter ||
            defaultReferencesColumn defs expression || expression.containsSubquery ||
            expression.defaultHasNonconstantFunction) then
          throw s!"default value of column [{d.name}] is not constant"
        let defaultValue ← constantDefault d.defaultValue
        pure (Column.mk d.name d.declaredType defaultValue d.generated d.notNull d.notNullConflict d.primaryKey
          d.unique d.conflict d.collation d.references d.check d.defaultSql d.autoIncrement)
      for constraint in constraints do
        if constraint.autoIncrement && (!constraint.primaryKey || constraint.columns.size != 1) then
          throw "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"
        if constraint.primaryKey && constraint.columns.size == 1 then
          let columnName := constraint.columns[0]!
          let index ← optionOr (columns.findIdx? fun column => nameEq column.name columnName)
            s!"no such column: {columnName}"
          let column := columns[index]!
          columns := columns.set! index { column with
            primaryKey := true, conflict := constraint.conflict,
            autoIncrement := constraint.autoIncrement }
      if columns.any (fun column => column.autoIncrement &&
          (!column.primaryKey || !nameEq column.declaredType.trimAscii.toString "integer")) then
        throw "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"
      let mut uniqueIndexes : Array UniqueIndex := #[]
      for index in [:columns.size] do
        let column := columns[index]!
        if (column.unique || column.primaryKey) &&
            !(column.primaryKey && nameEq column.declaredType "integer") then
          uniqueIndexes := uniqueIndexes.push {
            columns := #[index], conflict := column.conflict, primaryKey := column.primaryKey }
      for constraint in constraints do
        if constraint.check.isNone then
          let indices ← constraint.columns.mapM fun column => optionOr
            (columns.findIdx? fun candidate => nameEq candidate.name column) s!"no such column: {column}"
          match uniqueIndexes.find? (fun index => index.columns == indices) with
          | some existing =>
            if existing.conflict == constraint.conflict then pure ()
            else if existing.primaryKey || constraint.primaryKey then
              throw "conflicting ON CONFLICT clauses specified"
            else uniqueIndexes := uniqueIndexes.push {
              columns := indices, conflict := constraint.conflict,
              primaryKey := constraint.primaryKey }
          | none => uniqueIndexes := uniqueIndexes.push {
              columns := indices, conflict := constraint.conflict,
              primaryKey := constraint.primaryKey }
      let checks := (columns.filterMap (·.check) ++ constraints.filterMap (·.check)).map fun check =>
        { check with expression := check.expression.withCheckQualifier }
      let table : Table := { name, columns, uniqueIndexes, checks }
      let validationRow : StoredRow := { rowid := 0, values := columns.map fun _ => .null }
      let validationEnv := makeBindings { name } table validationRow
      for check in checks do
        if check.expression.containsSubquery then
          throw "subqueries prohibited in CHECK constraints"
        if check.expression.hasParameter then
          throw "parameters prohibited in CHECK constraints"
        match evalWithDb db validationEnv check.expression with
        | .ok _ => pure ()
        | .error message =>
          if message.startsWith "no such function: " && message.endsWith "()" then
            throw (message.take (message.length - 2)).toString
          else throw message
      let automaticIndexes := uniqueIndexes.mapIdx fun index uniqueIndex => ({
        name := s!"sqlite_autoindex_{unqualifiedName name}_{index + 1}"
        table := name
        columns := uniqueIndex.columns.map fun column => columns[column]!.name
        expressions := uniqueIndex.columns.map fun column => Expr.column none columns[column]!.name
        unique := true
        automatic := true
      } : SchemaIndex)
      let withTable := { db with
        tables := db.tables ++ [table], indexes := db.indexes ++ automaticIndexes.toList }
      pure (if table.usesAutoincrement then ensureSequenceTable withTable else withTable, {})

end SQLeanite
