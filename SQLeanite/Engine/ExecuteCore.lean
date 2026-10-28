import SQLeanite.Engine.ExecuteTriggerBody

namespace SQLeanite

def executeCore (db : Database) : Statement → Except String (Database × QueryResult)
  | .createWithoutRowidTable .. => .error "WITHOUT ROWID uses the production Core executor"
  | .createStrictTable .. => .error "STRICT uses the production Core executor"
  | .upsert .. => .error "UPSERT uses the production Core executor"
  | .createTable name defs constraints ifNotExists =>
      executeCreateTable db name defs constraints ifNotExists
  | .createTableAs name query ifNotExists => do
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    if (findTable? db name).isSome then
      if ifNotExists then return (db, {}) else throw s!"table {name} already exists"
    let selected ← executeSelect db query
    let columns := selected.columns.map fun column => { name := column }
    let table : Table := { name, columns }
    let withTable := { db with tables := db.tables ++ [table] }
    insertValueRows withTable name none selected.rows
  | .createView name columns query ifNotExists temporary sourceSql => do
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    if query.hasParameter then throw "parameters are not allowed in views"
    if ifNotExists && nameEq name "if" then
      throw "malformed database schema (IF) - near \"AS\": syntax error"
    if let some source := query.sources.find? (fun source =>
        source.name.toList.contains '.' &&
          let schema := source.name.splitOn "." |>.head?.getD "main"
          !nameEq schema "main" && !nameEq schema "temp") then
      let schema := source.name.splitOn "." |>.head?.getD "main"
      throw s!"view {name} cannot reference objects in database {schema}"
    let occupied := if temporary then
        db.views.any (fun view => view.temporary && nameEq view.name name)
      else (findTable? db name).isSome || db.views.any (fun view => !view.temporary && nameEq view.name name)
    if occupied then
      if ifNotExists then pure (db, {}) else throw s!"view {name} already exists"
    else do
      let actual := (selectColumnSchema db query).size
      unless columns.all (fun (names : Array String) => names.size == actual) do
        let expected := columns.map Array.size |>.getD 0
        throw s!"expected {expected} columns for '{name}' but got {actual}"
      pure ({ db with views := db.views ++ [{ name, columns, query, temporary, sourceSql }] }, {})
  | .dropTable name ifExists =>
    if nameEq name "sqlite_sequence" then throw "table sqlite_sequence may not be dropped"
    else if findTable? db name |>.isSome then
      let removed := removeAutoincrementRecord (removeTable db name) name
      pure ({ removed with
        triggers := db.triggers.filter fun t => !nameEq t.table name
        indexes := db.indexes.filter fun index => !nameEq index.table name }, {})
    else if (findView? db name).isSome then throw s!"use DROP VIEW to delete view {name}"
    else if ifExists then pure (db, {}) else throw s!"no such table: {name}"
  | .dropView name ifExists =>
    if let some target := findView? db name then
      pure ({ db with views := db.views.filter fun view =>
        !(nameEq view.name target.name && view.temporary == target.temporary) }, {})
    else if (findTable? db name).isSome then throw s!"use DROP TABLE to delete table {name}"
    else if ifExists then pure (db, {}) else throw s!"no such view: {name}"
  | .createIndex name table expressions unique where_ ifNotExists => do
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    if db.indexes.any (fun index => nameEq index.name name) then
      if ifNotExists then return (db, {}) else throw s!"index {name} already exists"
    if db.tables.any (fun candidate => nameEq (unqualifiedName candidate.name) (unqualifiedName name)) then
      throw s!"there is already a table named {unqualifiedName name}"
    if nameEq table "sqlite_master" || nameEq table "sqlite_schema" then
      throw "table sqlite_master may not be indexed"
    if nameEq table "sqlite_sequence" then throw "table sqlite_sequence may not be indexed"
    if (findView? db table).isSome then throw "views may not be indexed"
    let target ← optionOr (findTable? db table) s!"no such table: main.{table}"
    if name.toLower.startsWith "temp." && !target.name.toLower.startsWith "temp." then
      throw s!"cannot create a TEMP index on non-TEMP table \"{unqualifiedName table}\""
    if expressions.any Expr.containsSubquery then throw "subqueries prohibited in index expressions"
    if let some message := expressions.findSome? Expr.indexNondeterminism? then throw message
    let columns := expressions.filterMap Expr.baseColumnName?
    let directColumns := expressions.filterMap Expr.directColumnName?
    let indices ← directColumns.mapM fun column => optionOr
      (target.columns.findIdx? (fun candidate => nameEq candidate.name column))
      s!"no such column: {column}"
    let validationRow : StoredRow := { rowid := 0, values := target.columns.map fun _ => .null }
    let validationEnv := makeBindings { name := table } target validationRow
    for expression in expressions do discard <| evalWithDb db validationEnv expression
    for row in target.rows do
      let env := makeBindings { name := table } target row
      for expression in expressions do discard <| evalWithDb db env expression
    let schemaIndex : SchemaIndex := { name, table, columns, expressions, unique }
    let withSchema := { db with indexes := db.indexes ++ [schemaIndex] }
    if unique then
      let indexedExpressions := if directColumns.size == expressions.size then #[] else expressions
      let index : UniqueIndex := { columns := indices, expressions := indexedExpressions, where_, name }
      let validationTable := { target with uniqueIndexes := #[index] }
      for left in [:target.rows.size] do
        for right in [left + 1:target.rows.size] do
          if let some conflict := conflictTarget? validationTable target.rows[left]! target.rows[right]! then
            throw (conflictMessage target conflict)
      pure (replaceTable withSchema { target with uniqueIndexes := target.uniqueIndexes.push index }, {})
    else pure (withSchema, {})
  | .dropIndex name ifExists => do
    match db.indexes.find? fun index => nameEq index.name name with
    | none => if ifExists then pure (db, {}) else throw s!"no such index: {name}"
    | some index =>
      if index.automatic then
        throw "index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped"
      let withoutSchema := { db with indexes := db.indexes.filter (fun candidate =>
        !nameEq candidate.name name) }
      let table ← optionOr (findTable? withoutSchema index.table) s!"no such table: {index.table}"
      let table := { table with uniqueIndexes := table.uniqueIndexes.filter (fun candidate =>
        !nameEq candidate.name name) }
      pure (replaceTable withoutSchema table, {})
  | .createTrigger name table event timing when_ body ifNotExists temporary displayName sourceSql => do
    let trigger := Trigger.mk name table event timing when_ body temporary sourceSql
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    else if db.triggers.any (fun trigger => nameEq trigger.name name && trigger.temporary == temporary) then
      if ifNotExists then pure (db, {}) else
        throw s!"trigger {if displayName.isEmpty then name else displayName} already exists"
    else if nameEq table "sqlite_master" || nameEq table "sqlite_schema" then
      throw "cannot create trigger on system table"
    else if (findView? db table).isSome then
      if timing == .insteadOf then
        pure ({ db with triggers := db.triggers ++ [trigger] }, {})
      else throw s!"cannot create {if timing == .before then "BEFORE" else "AFTER"} trigger on view: {table}"
    else if (findTable? db table).isSome then
      if timing == .insteadOf then throw s!"cannot create INSTEAD OF trigger on table: {table}"
      else pure ({ db with triggers := db.triggers ++ [trigger] }, {})
    else throw s!"no such table: {if temporary then "" else "main."}{table}"
  | .dropTrigger name ifExists =>
    if db.triggers.any (fun trigger => nameEq trigger.name name) then
      pure ({ db with triggers := db.triggers.filter fun trigger => !nameEq trigger.name name }, {})
    else if ifExists then pure (db, {}) else throw s!"no such trigger: {name}"
  | .alterDropColumn .. => throw "ALTER TABLE DROP COLUMN is implemented by the production Core engine"
  | .alterAddColumn tableName definition => do
    let table ← optionOr (findTable? db tableName) s!"no such table: {tableName}"
    if table.columns.any (fun column => nameEq column.name definition.name) then
      throw s!"duplicate column name: {definition.name}"
    let defaultValue ← constantDefault definition.defaultValue
    let column := Column.mk definition.name definition.declaredType defaultValue definition.generated
      definition.notNull definition.notNullConflict definition.primaryKey definition.unique definition.conflict
      definition.collation definition.references definition.check definition.defaultSql definition.autoIncrement
    let expanded := table.addColumn column
    let rows ← expanded.rows.mapM fun row => do
      let values ← evaluateGeneratedColumns expanded row.rowid row.values
      pure { row with values := values }
    let expanded ← expanded.withRowsChecked rows
    pure (replaceTable db expanded, {})
  | .alterRenameTable .. => throw "ALTER TABLE RENAME is implemented by the production Core engine"
  | .alterRenameColumn tableName oldName newName => do
    let table ← optionOr (findTable? db tableName) s!"no such table: {tableName}"
    unless table.columns.any (fun column => nameEq column.name oldName) do
      throw s!"no such column: {oldName}"
    if table.columns.any (fun column => nameEq column.name newName) then
      throw s!"duplicate column name: {newName}"
    let renamedColumns := table.columns.map (fun column =>
      if nameEq column.name oldName then { column with name := newName } else column)
    let renamedTable ← table.withColumnsChecked renamedColumns
    let renamedTriggers := db.triggers.map fun trigger =>
      if nameEq trigger.table tableName then
        { trigger with
          sourceSql := trigger.sourceSql.replace ("new." ++ oldName) ("new." ++ newName)
            |>.replace ("old." ++ oldName) ("old." ++ newName) }
      else trigger
    pure ({ (replaceTable db renamedTable) with triggers := renamedTriggers }, {})
  | .insert table names exprRows conflict returning => do
    unless returning.isEmpty do throw "INSERT RETURNING is implemented by the production Core engine"
    let rows ← exprRows.mapM fun row => row.mapM (evalWithDb db #[])
    if let some first := rows[0]? then
      unless rows.all (fun row => row.size == first.size) do
        throw "all VALUES must have the same number of terms"
    if (findView? db table).isSome || nameEq table "sqlite_master" || nameEq table "sqlite_schema" then
      insertValueRows db table names rows conflict
    else
      let before ← optionOr (findTable? db table) s!"no such table: {table}"
      let (state, result) ← insertValueRows db table names rows conflict
      let after ← optionOr (findTable? state table) s!"no such table: {table}"
      let inserted := after.rows.filter fun row => !before.rows.any (fun old => old.rowid == row.rowid)
      pure (← fireInsertTriggers state after inserted, result)
  | .insertSelect table names query conflict returning => do
    unless returning.isEmpty do throw "INSERT RETURNING is implemented by the production Core engine"
    let selected ← executeSelect db query
    if (findView? db table).isSome || nameEq table "sqlite_master" || nameEq table "sqlite_schema" then
      insertValueRows db table names selected.rows conflict
    else
      let before ← optionOr (findTable? db table) s!"no such table: {table}"
      let (state, result) ← insertValueRows db table names selected.rows conflict
      let after ← optionOr (findTable? state table) s!"no such table: {table}"
      let inserted := after.rows.filter fun row => !before.rows.any (fun old => old.rowid == row.rowid)
      pure (← fireInsertTriggers state after inserted, result)
  | .delete name alias where_ returning => do
    if nameEq name "sqlite_master" || nameEq name "sqlite_schema" then
      throw "table sqlite_master may not be modified"
    if (findView? db name).isSome then throw s!"cannot modify {name} because it is a view"
    let table ← optionOr (findTable? db name) s!"no such table: {name}"
    let ref : TableRef := { name, alias }
    let validationRow : StoredRow := { rowid := 0, values := table.columns.map fun _ => .null }
    if let some condition := where_ then
      discard <| evalWithDb db (makeBindings ref table validationRow) condition
    let mut kept := #[]
    let mut deleted := #[]
    let mut changes := 0
    for row in table.rows do
      if ← matchesWhere db (makeBindings ref table row) where_ then
        changes := changes + 1
        deleted := deleted.push row
      else kept := kept.push row
    let retained ← table.withRowsChecked kept
    let changed := replaceTable db retained
    let next ← applyDeleteEffects changed table deleted
    if returning.isEmpty then pure (next, mutationResult db changes)
    else
      let rows ← deleted.mapM fun row => expandResult db (makeBindings ref table row) returning
      let representative := makeBindings ref table (deleted[0]?.getD validationRow)
      let columns := resultNames db representative returning
      let result : QueryResult := { columns, rows, changes, reportsChanges := true }
      pure (next, result)
  | .update name alias assignments where_ conflict returning => do
    unless returning.isEmpty do throw "UPDATE RETURNING is implemented by the production Core engine"
    if nameEq name "sqlite_master" || nameEq name "sqlite_schema" then
      if !db.writableSchema then throw "table sqlite_master may not be modified"
      let sqlAssignment ← optionOr (assignments.find? fun assignment => nameEq assignment.1 "sql")
        "writable schema UPDATE must assign sql"
      let schemaSql ← evalWithDb db #[] sqlAssignment.2
      let updated ← replaceTableSchemaSql db (toString schemaSql)
      return (updated, mutationResult db 1)
    if (findView? db name).isSome then throw s!"cannot modify {name} because it is a view"
    let mut table ← optionOr (findTable? db name) s!"no such table: {name}"
    let mut state := db
    let evaluationDb := db
    for (column, _) in assignments do
      unless isRowidName column || table.columns.any (fun c => nameEq c.name column) do
        throw s!"no such column: {column}"
    let ref : TableRef := { name, alias }
    let validationRow : StoredRow := { rowid := 0, values := table.columns.map fun _ => .null }
    let validationEnv := makeBindings ref table validationRow
    if let some condition := where_ then discard <| evalWithDb state validationEnv condition
    for (_, expression) in assignments do discard <| evalWithDb state validationEnv expression
    for trigger in state.triggers do
      if nameEq trigger.table name && trigger.event == .update then
        if let some condition := trigger.when_ then
          let oldEnv := makeBindings { name, alias := some "old" } table validationRow
          let newEnv := makeBindings { name, alias := some "new" } table validationRow
          discard <| evalWithDb state (validationEnv ++ oldEnv.map Binding.outerScoped ++
            newEnv.map Binding.outerScoped) condition
    -- A rowid-only update over the whole table can be evaluated as one
    -- immutable array transformation. Besides being equivalent when no
    -- callbacks or foreign keys are involved, this avoids quadratic scans.
    if where_.isNone && conflict == .default && (integerPrimaryKey? table).isNone &&
        assignments.all (fun assignment => isRowidName assignment.1) &&
        !state.foreignKeys && !state.triggers.any (fun trigger => nameEq trigger.table name) then
      let mut seen := Std.HashSet.emptyWithCapacity (capacity := table.rows.size)
      let mut rows : Array StoredRow := Array.mkEmpty table.rows.size
      for row in table.rows do
        let env := makeBindings ref table row
        let mut rowid := row.rowid
        for (_, expression) in assignments do
          rowid ← optionOr (← evalWithDb evaluationDb env expression).toInt? "datatype mismatch"
        if seen.contains rowid then throw s!"UNIQUE constraint failed: {table.name}.rowid"
        seen := seen.insert rowid
        let values ← evaluateGeneratedColumns table rowid row.values
        rows := rows.push { row with rowid := rowid, values := values }
      let nextRowid := rows.foldl (init := table.nextRowid) fun next row =>
        max next (row.rowid + 1)
      let updatedTable ← ({ table with nextRowid }).withRowsChecked rows
      return (replaceTable state updatedTable, mutationResult db rows.size)
    let mut changes := 0
    let mut updatedRows : Array (StoredRow × StoredRow) := #[]
    let originals := table.rows
    for row in originals do
      let env := makeBindings ref table row
      if ← matchesWhere evaluationDb env where_ then
        let mut updated := row.values
        let mut assignedRowid := row.rowid
        for (column, expr) in assignments do
          let value ← evalWithDb evaluationDb env expr
          if isRowidName column then
            assignedRowid ← optionOr value.toInt? "datatype mismatch"
          else
            let idx := table.columns.findIdx? (fun c => nameEq c.name column) |>.getD 0
            if table.columns[idx]!.generated.isSome then
              throw s!"cannot UPDATE generated column \"{column}\""
            updated := updated.set! idx (table.columns[idx]!.applyAffinity value)
        let mut updatedRow := { row with values := updated, rowid := assignedRowid }
        if let some pk := integerPrimaryKey? table then
          if !(updated[pk]! matches .null) then
            let id ← optionOr updated[pk]!.toInt? "datatype mismatch"
            updatedRow := { updatedRow with rowid := id, values := updated.set! pk (.integer id) }
        let generatedValues ← evaluateGeneratedColumns table updatedRow.rowid updatedRow.values
        updatedRow := { updatedRow with values := generatedValues }
        state ← fireUpdateTriggers state table #[(row, updatedRow)] .before
        table ← optionOr (findTable? state name) s!"no such table: {name}"
        if let some current := table.rows.find? (fun candidate => candidate.rowid == row.rowid) then
          let mut merged := current.values
          for (column, _) in assignments do
            unless isRowidName column do
              let idx := table.columns.findIdx? (fun candidate => nameEq candidate.name column) |>.getD 0
              merged := merged.set! idx updatedRow.values[idx]!
          updatedRow := { current with values := merged, rowid := updatedRow.rowid }
        let generatedValues ← evaluateGeneratedColumns table updatedRow.rowid updatedRow.values
        updatedRow := { updatedRow with values := generatedValues }
        let (checkedRow, skipNotNull) ← enforceNotNull table updatedRow conflict
        updatedRow := checkedRow
        if skipNotNull then continue
        if conflict == .fail && !state.ignoreCheckConstraints then
          if let some check := table.checks.find? (fun check =>
              (violatesCheck state table updatedRow check).toOption.getD true) then
            let result := mutationResult db changes
            return (state, { result with deferredError := some s!"CHECK constraint failed: {check.diagnostic}" })
        if ← enforceChecks state table updatedRow conflict then continue
        validateForeignKeys state table updatedRow
        let withoutOld := table.rows.filter (fun r => r.rowid != row.rowid)
        let conflicts := withoutOld.filterMap fun old => (conflictTarget? table updatedRow old).map (old, ·)
        if conflicts.isEmpty then
          let rows := table.rows.map fun existing =>
            if existing.rowid == row.rowid then updatedRow else existing
          let advanced := { table with nextRowid := max table.nextRowid (updatedRow.rowid + 1) }
          table ← advanced.withRowsChecked rows
          state := replaceTable state table
          changes := changes + 1
          updatedRows := updatedRows.push (row, updatedRow)
        else
          let resolution := conflict.resolve conflicts[0]!.2.action
          match resolution with
          | .default => throw (conflictMessage table conflicts[0]!.2)
          | .abort => throw (conflictMessage table conflicts[0]!.2)
          | .fail =>
            let result := mutationResult db changes
            return (state, { result with deferredError := some (conflictMessage table conflicts[0]!.2) })
          | .rollback => throw (rollbackConflictPrefix ++ conflictMessage table conflicts[0]!.2)
          | .ignore => pure ()
          | .replace =>
            let reentrant := state.triggers.any fun trigger =>
              nameEq trigger.table name && trigger.event == .delete && trigger.body.any fun action =>
                match action with
                | .update target _ _ _ _ => nameEq target name
                | _ => false
            if reentrant then throw "constraint failed"
            let victims := conflicts.map (·.1)
            table ← table.withRowsChecked
              (withoutOld.filter fun old => !victims.any (·.rowid == old.rowid))
            state := replaceTable state table
            state ← applyDeleteEffects state table victims
            table ← optionOr (findTable? state name) s!"no such table: {name}"
            if let some (_, target) := table.rows.findSome? fun old =>
                (conflictTarget? table updatedRow old).map (old, ·) then
              throw (conflictMessage table target)
            table ← table.insertChecked updatedRow
            state := replaceTable state table
            changes := changes + 1
            updatedRows := updatedRows.push (row, updatedRow)
    state ← fireUpdateTriggers state table updatedRows .after
    if nameEq name "sqlite_sequence" then state := applySequenceHighWater state
    pure (state, mutationResult db changes)
  | .withRecursive name columnNames seedQuery step all body _ => do
    let seedResult ← executeSelect db seedQuery
    let seed := seedResult.rows
    let width := seed[0]?.map Array.size |>.getD columnNames.size
    unless seed.all (fun row => row.size == width) do
      throw "all VALUES must have the same number of terms"
    let names := if columnNames.isEmpty then valuesColumnNames width else columnNames
    unless names.size == width do throw s!"table {name} has {names.size} values for {width} columns"
    let columns : Array Column := names.map fun column => { name := column }
    let original := findTable? db name
    let install (state : Database) (rows : Array (Array Value)) : Except String Database := do
      let stored := rows.mapIdx fun i values => StoredRow.mk (Int.ofNat (i + 1)) values
      let rowStore ← RowStore.checked stored columns.size
      let temporary := Table.mk name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[]
      pure { state with tables := (state.tables.filter fun table => !nameEq table.name name) ++ [temporary] }
    let mut state := db
    let mut accumulated := seed
    let mut work := seed
    let mut iterations := 0
    while !work.isEmpty && iterations < 100000 do
      state ← install state work
      let selected ← executeSelect state step
      let mut next := selected.rows
      unless all do next := next.filter fun row => !accumulated.contains row
      accumulated := accumulated ++ next
      work := next
      iterations := iterations + 1
    if iterations == 100000 then throw "recursive CTE query limit exceeded"
    state ← install state accumulated
    let (after, result) ← executeCore state body
    let withoutCte := { after with tables := after.tables.filter fun table => !nameEq table.name name }
    let restored := match original with
      | some table => { withoutCte with tables := withoutCte.tables ++ [table] }
      | none => withoutCte
    pure (restored, result)
  | .withCte name columnNames source body _ => do
    let (_, materialized) ← executeCore db source
    let width := materialized.rows[0]?.map Array.size |>.getD materialized.columns.size
    unless materialized.rows.all (fun row => row.size == width) do
      throw "all rows of a common table expression must have the same width"
    let inferred : Array Column := match source with
      | .select query => selectColumnSchema db query
      | .values rows => match rows[0]? with
        | some expressions => expressions.mapIdx fun i expression =>
            { name := materialized.columns[i]?.getD s!"column{i + 1}",
              declaredType := expressionDeclaredType expression }
        | none => #[]
      | _ => materialized.columns.map fun column => { name := column }
    let names := if columnNames.isEmpty then materialized.columns else columnNames
    unless names.size == width do
      throw s!"table {name} has {names.size} values for {width} columns"
    let columns : Array Column := names.mapIdx fun i column =>
      (inferred[i]?.getD ({ name := column } : Column)).renamed column
    let stored := materialized.rows.mapIdx fun i values => StoredRow.mk (Int.ofNat (i + 1)) values
    let rowStore ← RowStore.checked stored columns.size
    let cte := Table.mk name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[]
    let original := findTable? db name
    let installed := { db with tables := (db.tables.filter fun table => !nameEq table.name name) ++ [cte] }
    let (after, result) ← executeCore installed body
    let withoutCte := { after with tables := after.tables.filter fun table => !nameEq table.name name }
    let restored := match original with
      | some table => { withoutCte with tables := withoutCte.tables ++ [table] }
      | none => withoutCte
    pure (restored, result)
  | .select query => do pure (db, ← executeSelect db query)
  | .values exprRows => do
    let rows ← exprRows.mapM fun row => row.mapM (evalWithDb db #[])
    let width := rows[0]?.map Array.size |>.getD 0
    unless rows.all (fun row => row.size == width) do
      throw "all VALUES must have the same number of terms"
    pure (db, { columns := valuesColumnNames width, rows })
  | .begin =>
    if db.transactionSnapshot.isSome then throw "cannot start a transaction within a transaction"
    else pure ({ db with transactionSnapshot := some {
      tables := db.tables, views := db.views, triggers := db.triggers, indexes := db.indexes } }, {})
  | .commit =>
    if db.transactionSnapshot.isNone then throw "cannot commit - no transaction is active"
    else pure ({ db with transactionSnapshot := none }, {})
  | .rollback =>
    match db.transactionSnapshot with
    | none => throw "cannot rollback - no transaction is active"
    | some snapshot => pure (db.restoreSnapshot snapshot, {})
  | .savepoint _ | .release _ | .rollbackTo _ => throw "SAVEPOINT is supported by the production Core engine"
  | .reindex => pure (db, {})
  | .pragma name argument _schema =>
    let enabled := match argument with
      | some (.literal (.integer i) _) => i != 0
      | some (.literal (.text s) _) | some (.column none s) =>
        ["on", "true", "yes", "1"].contains s.toLower
      | _ => false
    let shortName := name.splitOn "." |>.getLast?.getD name
    if nameEq shortName "short_column_names" then pure ({ db with shortColumnNames := enabled }, {})
    else if nameEq shortName "full_column_names" then pure ({ db with fullColumnNames := enabled }, {})
    else if nameEq shortName "foreign_keys" then pure ({ db with foreignKeys := enabled }, {})
    else if nameEq shortName "count_changes" then pure ({ db with countChanges := enabled }, {})
    else if nameEq shortName "recursive_triggers" then pure ({ db with recursiveTriggers := enabled }, {})
    else if nameEq shortName "ignore_check_constraints" then
      pure ({ db with ignoreCheckConstraints := enabled }, {})
    else if nameEq shortName "writable_schema" then pure ({ db with writableSchema := enabled }, {})
    else if nameEq shortName "lean_check_myfunc_enabled" then
      pure ({ db with checkMyfuncEnabled := enabled }, {})
    else if nameEq shortName "lean_readonly" then pure ({ db with readOnly := enabled }, {})
    else if nameEq shortName "lean_views_enabled" then pure ({ db with viewsEnabled := enabled }, {})
    else if nameEq shortName "lean_dqs_dml" then pure ({ db with doubleQuotedStrings := enabled }, {})
    else if nameEq shortName "lean_view_depth_limit" then
      let limit := match argument with
        | some (.literal (.integer value) _) => (max 1 value).toNat
        | _ => 1000
      pure ({ db with viewDepthLimit := limit }, {})
    else if nameEq shortName "lean_current_time" then
      let timestamp := match argument with
        | some (.literal (.integer value) _) => value
        | _ => 0
      pure ({ db with currentTime := timestamp }, {})
    else if nameEq shortName "lean_record_sizes" then
      let rootpage : Int := match argument with
        | some (.literal (.integer value) _) => value
        | _ => 0
      let rows := if rootpage < 2 then #[] else
        match db.tables[(rootpage - 2).toNat]? with
        | none => #[]
        | some table => table.rows.map fun row => #[.integer (Int.ofNat (sqliteRecordSize row.values))]
      pure (db, { columns := #["record_size"], rows })
    else if nameEq shortName "lean_analyze" then
      if (findTable? db "sqlite_stat1").isSome then pure (db, {})
      else
        let columns : Array Column := #[{ name := "tbl" }, { name := "idx" }, { name := "stat" }]
        let statistics : Table := { name := "sqlite_stat1", columns }
        pure ({ db with tables := db.tables ++ [statistics] }, {})
    else if nameEq shortName "encoding" then
      pure (db, { columns := #[name], rows := #[#[.text "UTF-8"]] })
    else if nameEq shortName "table_info" then do
      let objectName? := match argument with
        | some (.column none objectName) | some (.literal (.text objectName) _) => some objectName
        | _ => none
      let columns ← match objectName? with
        | none => pure #[]
        | some objectName =>
          if let some table := findTable? db objectName then pure table.columns
          else if let some view := findView? db objectName then
            let inferred := selectColumnSchema db view.query
            pure <| match view.columns with
              | none => inferred
              | some names => inferred.mapIdx fun i column =>
                  { column with name := names[i]?.getD column.name }
          else pure #[]
      let rows := columns.mapIdx fun i column => #[.integer i, .text column.name,
        .text column.declaredType, .integer (if column.notNull then 1 else 0),
        column.defaultSql.map Value.text |>.getD .null,
        .integer (if column.primaryKey then 1 else 0)]
      pure (db, { columns := #["cid", "name", "type", "notnull", "dflt_value", "pk"], rows })
    else if nameEq shortName "integrity_check" || nameEq shortName "quick_check" then
      let broken := if db.ignoreCheckConstraints then none else db.tables.find? fun table =>
        table.rows.any fun row => table.checks.any fun check =>
          (violatesCheck db table row check).toOption.getD true
      let message := broken.map (fun table => s!"CHECK constraint failed in {unqualifiedName table.name}")
        |>.getD "ok"
      pure (db, { columns := #[name], rows := #[#[.text message]] })
    else if nameEq shortName "locking_mode" then
      pure (db, { columns := #[name], rows := #[#[.text "normal"]] })
    else pure (db, {})

end SQLeanite
