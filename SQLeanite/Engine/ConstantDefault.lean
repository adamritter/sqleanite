import SQLeanite.Engine.SourceEnvs

namespace SQLeanite

def constantDefault (expr : Option Expr) : Except String Value :=
  match expr with
  | none => pure .null
  | some (.column none name) => pure (.text name)
  | some call@(.call name _ _) =>
      match evalExpr #[] call with
      | .ok value => pure value
      | .error message =>
        if message.startsWith "no such function: " then
          pure (.text (unknownDefaultPrefix ++ name))
        else throw message
  | some e => evalExpr #[] e

def replaceTableSchemaSql (db : Database) (sql : String) : Except String Database := do
  let statements ← parseLegacy sql
  match (statements[0]? : Option Statement) with
  | Option.some (Statement.createTable tableName definitions _ _) =>
    let table ← optionOr (findTable? db tableName) s!"no such table: {tableName}"
    let columns ← definitions.mapM fun definition => do
      let defaultValue ← constantDefault definition.defaultValue
      pure (Column.mk definition.name definition.declaredType defaultValue definition.generated
        definition.notNull definition.notNullConflict definition.primaryKey definition.unique
        definition.conflict definition.collation definition.references definition.check
        definition.defaultSql definition.autoIncrement)
    unless columns.size == table.columns.size do throw "malformed database schema"
    let updated ← table.withColumnsChecked columns
    pure (replaceTable db updated)
  | _ => throw "malformed database schema"

def isRowidName (name : String) : Bool :=
  nameEq name "rowid" || nameEq name "_rowid_" || nameEq name "oid"

def integerPrimaryKey? (table : Table) : Option Nat :=
  table.columns.findIdx? fun c => c.primaryKey && nameEq c.declaredType "integer"

def Table.hasDeclaredUniqueness (table : Table) : Bool :=
  table.columns.any (fun column => column.primaryKey || column.unique) ||
    !table.uniqueIndexes.isEmpty

def generatedColumnEnv (table : Table) (rowid : Int) (values : Array Value) : Env :=
  let visible := table.columns.mapIdx fun i column =>
    { table := table.name, alias := table.name, column := column.name,
      value := values[i]?.getD .null, collation := column.collation,
      declaredType := column.declaredType }
  let hidden := #["rowid", "_rowid_", "oid"].map fun name =>
    Binding.mk table.name table.name name (.integer rowid) true 0 "binary" "LEAN_HIDDEN"
  visible ++ hidden

def replaceColumnValue (values : Array Value) (index : Nat) (value : Value) : Array Value :=
  values.set! index value

theorem replaceColumnValue_preserves_width (values : Array Value) (index : Nat) (value : Value) :
    (replaceColumnValue values index value).size = values.size := by
  simp [replaceColumnValue, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

def evaluateGeneratedColumns (table : Table) (rowid : Int)
    (values : Array Value) : Except String (Array Value) := do
  let mut result := values
  -- Repeating at most once per column resolves acyclic dependencies even when
  -- a generated column refers to one declared later in the schema.
  for _ in [:table.columns.size] do
    for i in [:table.columns.size] do
      if let some expression := table.columns[i]!.generated then
        let value ← evalExpr (generatedColumnEnv table rowid result) expression
        result := replaceColumnValue result i (table.columns[i]!.applyAffinity value)
  pure result

/-- Choose the implicit rowid SQLite will assign to the next inserted row.
AUTOINCREMENT tables retain their high-water mark; ordinary tables may reuse
the smallest dense successor after rows have been deleted. -/
def Table.nextImplicitRowid (table : Table) : Int :=
  let denseNext := Int.ofNat (table.rows.size + 1)
  if table.columns.any (·.autoIncrement) then table.nextRowid
  else if table.nextRowid == denseNext then table.nextRowid
  else table.rows.foldl (init := 0) (fun highest row => max highest row.rowid) + 1

theorem Table.nextImplicitRowid_of_autoincrement (table : Table)
    (enabled : table.columns.any (·.autoIncrement) = true) :
    table.nextImplicitRowid = table.nextRowid := by
  simp [Table.nextImplicitRowid, enabled]

def makeInsertedRow (table : Table) (names : Option (Array String))
    (values : Array Value) : Except String StoredRow := do
  let writable := (Array.range table.columns.size).filter fun i => table.columns[i]!.generated.isNone
  let mut rowValues : Array Value ← match names with
  | none =>
    if values.isEmpty then pure (table.columns.map (·.defaultValue))
    else if values.size != writable.size then
      throw s!"table {table.name} has {writable.size} columns but {values.size} values were supplied"
    else
      let mut row := table.columns.map (·.defaultValue)
      for i in [:writable.size] do row := row.set! writable[i]! values[i]!
      pure row
  | some names =>
    if names.size != values.size then throw s!"{values.size} values for {names.size} columns"
    let mut row := table.columns.map (·.defaultValue)
    let mut assigned : Array Nat := #[]
    for i in [:names.size] do
      let name := names[i]!
      unless isRowidName name do
        let idx ← optionOr (table.columns.findIdx? (fun c => nameEq c.name name))
          s!"table {table.name} has no column named {name}"
        if table.columns[idx]!.generated.isSome then
          throw s!"cannot INSERT into generated column \"{name}\""
        unless assigned.contains idx do
          row := row.set! idx values[i]!
          assigned := assigned.push idx
    pure row
  for value in rowValues do
    if let .text source := value then
      if source.startsWith unknownDefaultPrefix then
        throw s!"unknown function: {source.drop unknownDefaultPrefix.length}()"
  let affinityValues := rowValues.mapIdx fun i value => table.columns[i]!.applyAffinity value
  let mut explicitRowid : Option Int := none
  match names with
  | some names =>
    for i in [:names.size] do
      if isRowidName names[i]! then explicitRowid := values[i]!.toInt?
  | none => pure ()
  match integerPrimaryKey? table with
  | some pk =>
    if !(affinityValues[pk]! matches .null) then
      match affinityValues[pk]!.toInt? with
      | some id => explicitRowid := some id
      | none => throw "datatype mismatch"
  | none => pure ()
  let implicitRowid := table.nextImplicitRowid
  if explicitRowid.isNone && table.usesAutoincrement && implicitRowid > 9223372036854775807 then
    throw "database or disk is full"
  let rowid := explicitRowid.getD implicitRowid
  let finalValues := match integerPrimaryKey? table with
    | some pk => affinityValues.set! pk (.integer rowid)
    | none => affinityValues
  pure { rowid, values := ← evaluateGeneratedColumns table rowid finalValues }

inductive ConflictTarget where
  | rowid
  | columns (indices : Array Nat) (action : ConflictAction := .abort)
  | index (name : String)
  deriving Inhabited

def ConflictTarget.action : ConflictTarget → ConflictAction
  | .rowid => .abort
  | .columns _ action => action
  | .index _ => .abort

def conflictTarget? (table : Table) (new old : StoredRow) : Option ConflictTarget :=
  let indices := table.columns.mapIdx (fun i c => (i, c.primaryKey || c.unique)) |>.filter (·.2) |>.map (·.1)
  match indices.findSome? (fun i =>
      let a := new.values[i]?.getD .null
      let b := old.values[i]?.getD .null
      if !(a matches .null) && a.sqlEq b == .true then some (.columns #[i] table.columns[i]!.conflict) else none) with
  | some target => some target
  | none =>
    let ref : TableRef := { name := table.name }
    let applies (row : StoredRow) (predicate : Option Expr) :=
      match predicate with
      | none => true
      | some e => match evalExpr (makeBindings ref table row) e with
        | .ok value => value.truth == .true
        | .error _ => false
    match table.uniqueIndexes.findSome? (fun index =>
        let expressionValuesMatch := !index.expressions.isEmpty && index.expressions.all (fun expression =>
          let newEnv := makeBindings ref table new
          let oldEnv := makeBindings ref table old
          match evalExpr newEnv expression, evalExpr oldEnv expression with
          | .ok a, .ok b => !(a matches .null) &&
              collatedCompare (expression.collationIn newEnv) a b == .eq
          | _, _ => false)
        let columnValuesMatch := index.expressions.isEmpty && index.columns.all (fun i =>
              let a := new.values[i]?.getD .null
              let b := old.values[i]?.getD .null
              !(a matches .null) && a.sqlEq b == .true)
        if applies new index.where_ && applies old index.where_ &&
            (expressionValuesMatch || columnValuesMatch)
        then some (if index.expressions.isEmpty then .columns index.columns index.conflict
          else .index index.name)
        else none) with
    | some target => some target
    | none =>
      if new.rowid == old.rowid then
        match integerPrimaryKey? table with
        | some i => some (.columns #[i] table.columns[i]!.conflict)
        | none => some .rowid
      else none

def conflictMessage (table : Table) : ConflictTarget → String
  | .rowid => s!"UNIQUE constraint failed: {table.name}.rowid"
  | .columns indices _ => "UNIQUE constraint failed: " ++ String.intercalate ", "
      (indices.toList.map fun i => s!"{table.name}.{table.columns[i]!.name}")
  | .index name => s!"UNIQUE constraint failed: index '{name}'"

def referencedColumnIndex (table : Table) (reference : ForeignKeyDef) : Except String Nat :=
  match reference.column with
  | some name => optionOr (table.columns.findIdx? fun column => nameEq column.name name)
      s!"foreign key mismatch - no such column {table.name}.{name}"
  | none => optionOr (table.columns.findIdx? (·.primaryKey))
      s!"foreign key mismatch - {table.name} has no primary key"

def validateForeignKeys (db : Database) (table : Table) (row : StoredRow) : Except String Unit := do
  unless db.foreignKeys do return ()
  for index in [:table.columns.size] do
    if let some reference := table.columns[index]!.references then
      let value := row.values[index]?.getD .null
      unless value matches .null do
        let parent ← optionOr (findTable? db reference.table) s!"no such table: main.{reference.table}"
        let parentIndex ← referencedColumnIndex parent reference
        unless parent.rows.any (fun candidate =>
            value.sqlEq (candidate.values[parentIndex]?.getD .null) == .true) do
          throw "FOREIGN KEY constraint failed"

def mutationResult (db : Database) (changes : Nat) : QueryResult :=
  if db.countChanges then
    { columns := #["rows affected"], rows := #[#[.integer changes]], changes, reportsChanges := true }
  else { changes, reportsChanges := true }

def rollbackConflictPrefix := "\u0000sqleanite-rollback:"

def enforceNotNull (table : Table) (candidate : StoredRow)
    (statementConflict : ConflictAction) : Except String (StoredRow × Bool) := do
  let mut row := candidate
  for index in [:table.columns.size] do
    let column := table.columns[index]!
    if column.notNull && row.values[index]! matches .null then
      let resolution := statementConflict.resolve column.notNullConflict
      match resolution with
      | .ignore => return (row, true)
      | .replace =>
        if column.defaultValue matches .null then
          throw s!"NOT NULL constraint failed: {table.name}.{column.name}"
        row := { row with values := row.values.set! index (column.applyAffinity column.defaultValue) }
      | .rollback =>
        throw (rollbackConflictPrefix ++ s!"NOT NULL constraint failed: {table.name}.{column.name}")
      | .default | .abort | .fail => throw s!"NOT NULL constraint failed: {table.name}.{column.name}"
  pure (row, false)

def violatesCheck (db : Database) (table : Table) (row : StoredRow)
    (check : CheckDef) : Except String Bool := do
  let value ← evalWithDb db (makeBindings { name := table.name } table row) check.expression
  pure (!value.truth.satisfiesCheck)

def checkEvaluationError (message : String) : String :=
  if message.startsWith "no such function: " then "unknown function: " ++ (message.drop 18).toString else message

def enforceChecks (db : Database) (table : Table) (row : StoredRow)
    (statementConflict : ConflictAction) : Except String Bool := do
  if db.ignoreCheckConstraints then return false
  for check in table.checks do
    let violation ← match violatesCheck db table row check with
      | .ok value => pure value
      | .error message => throw (checkEvaluationError message)
    if violation then
      match statementConflict with
      | .ignore => return true
      | .rollback => throw (rollbackConflictPrefix ++ s!"CHECK constraint failed: {check.diagnostic}")
      | .default | .abort | .fail | .replace => throw s!"CHECK constraint failed: {check.diagnostic}"
  pure false

mutual
def insertValueRowsBaseFuel : Nat → Database → String → Option (Array String) →
    Array (Array Value) → ConflictAction → Except String (Database × QueryResult)
  | 0, _, _, _, _, _ => throw "too many levels of trigger recursion"
  | fuel + 1, db, tableName, names, rows, conflict => do
    if nameEq tableName "sqlite_master" || nameEq tableName "sqlite_schema" then
      throw "table sqlite_master may not be modified"
    if (findView? db tableName).isSome then throw s!"cannot modify {tableName} because it is a view"
    let mut state := db
    let mut table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
    let mut changes := 0
    for values in rows do
      let candidate ← makeInsertedRow table names values
      let (row, skip) ← enforceNotNull table candidate conflict
      if skip then continue
      if ← enforceChecks state table row conflict then continue
      validateForeignKeys (replaceTable db table) table row
      let conflicts := if !table.hasDeclaredUniqueness && row.rowid >= table.nextRowid then #[] else
        table.rows.filterMap fun old => (conflictTarget? table row old).map (old, ·)
      if conflicts.isEmpty then
        table ← table.insertChecked row
        state := { state with lastInsertRowid := row.rowid }
        state := replaceTable state table
        state := recordAutoincrement state table row.rowid
        changes := changes + 1
      else
        let resolution := conflict.resolve conflicts[0]!.2.action
        match resolution with
        | .default => throw (conflictMessage table conflicts[0]!.2)
        | .abort => throw (conflictMessage table conflicts[0]!.2)
        | .fail => throw (conflictMessage table conflicts[0]!.2)
        | .rollback => throw (rollbackConflictPrefix ++ conflictMessage table conflicts[0]!.2)
        | .ignore => pure ()
        | .replace =>
          let victimIds := conflicts.map (·.1.rowid)
          let victims := table.rows.filter fun old => victimIds.contains old.rowid
          if state.recursiveTriggers then
            state := replaceTable state table
            state ← fireDeleteTriggersFuel fuel state table victims none
            table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
          table := table.retainRows fun old => !victimIds.contains old.rowid
          if let some target := table.rows.findSome? fun old => conflictTarget? table row old then
            throw (conflictMessage table target)
          table ← table.insertChecked row
          state := { state with lastInsertRowid := row.rowid }
          state := replaceTable state table
          state := recordAutoincrement state table row.rowid
          changes := changes + 1
    state := replaceTable state table
    if rows.isEmpty then state := recordAutoincrement state table 0
    pure (state, mutationResult state changes)

def fireDeleteTriggersFuel : Nat → Database → Table → Array StoredRow →
    Option TriggerTiming → Except String Database
  | 0, _, _, _, _ => throw "too many levels of trigger recursion"
  | fuel + 1, db, table, deleted, onlyTiming => do
    let mut state := db
    for old in deleted do
      let oldEnv := makeBindings { name := table.name, alias := some "old" } table old
      for trigger in state.triggers do
        if nameEq trigger.table table.name && trigger.event == .delete &&
            onlyTiming.all (trigger.timing == ·) then
          let enabled ← match trigger.when_ with
            | none => pure true
            | some condition => pure ((← evalWithDb state oldEnv condition).truth == .true)
          if enabled then
            for action in trigger.body do
              match action with
              | .insert target columns rows conflict =>
                let values ← rows.mapM fun row => row.mapM (evalWithDb state oldEnv)
                let (next, _) ← insertValueRowsBaseFuel fuel state target columns values conflict
                state := next
              | .insertSelect target columns query conflict =>
                let selected ← executeSelect state query
                let (next, _) ← insertValueRowsBaseFuel fuel state target columns selected.rows conflict
                state := next
              | .update target alias assignments where_ conflict =>
                let mut targetTable ← optionOr (findTable? state target) s!"no such table: {target}"
                let evaluationState := state
                let targetRef : TableRef := { name := target, alias }
                let originals := targetTable.rows
                for targetRow in originals do
                  let targetEnv := makeBindings targetRef targetTable targetRow ++ oldEnv.map Binding.outerScoped
                  if ← matchesWhere evaluationState targetEnv where_ then
                    let mut values := targetRow.values
                    let mut rowid := targetRow.rowid
                    for (column, expression) in assignments do
                      let value ← evalWithDb evaluationState targetEnv expression
                      if isRowidName column then
                        rowid ← optionOr value.toInt? "datatype mismatch"
                      else
                        let index ← optionOr (targetTable.columns.findIdx? fun c => nameEq c.name column)
                          s!"no such column: {column}"
                        if targetTable.columns[index]!.generated.isSome then
                          throw s!"cannot UPDATE generated column \"{column}\""
                        values := values.set! index value
                    values ← evaluateGeneratedColumns targetTable rowid values
                    let updated := { targetRow with values, rowid }
                    validateForeignKeys state targetTable updated
                    let withoutOld := targetTable.rows.filter fun row => row.rowid != targetRow.rowid
                    match withoutOld.findSome? fun row =>
                        (conflictTarget? targetTable updated row).map (row, ·) with
                    | some (_, target) =>
                      let resolution := conflict.resolve target.action
                      if resolution == .ignore then pure () else throw (conflictMessage targetTable target)
                    | none =>
                      let rows := targetTable.rows.map fun row =>
                        if row.rowid == targetRow.rowid then updated else row
                      let advanced := { targetTable with
                        nextRowid := max targetTable.nextRowid (updated.rowid + 1) }
                      targetTable ← advanced.withRowsChecked rows
                state := replaceTable state targetTable
              | .delete target alias where_ _ =>
                let targetTable ← optionOr (findTable? state target) s!"no such table: {target}"
                let targetRef : TableRef := { name := target, alias }
                let mut victims : Array Int := #[]
                for targetRow in targetTable.rows do
                  let targetEnv := makeBindings targetRef targetTable targetRow ++ oldEnv.map Binding.outerScoped
                  if ← matchesWhere state targetEnv where_ then victims := victims.push targetRow.rowid
                state := replaceTable state (targetTable.retainRows fun row => !victims.contains row.rowid)
              | .select query =>
                let shouldRun ← matchesWhere state oldEnv query.where_
                if shouldRun then
                  for result in query.columns do
                    if let .call name args _ := result.expr then
                      if nameEq name "raise" then
                        let message ← match args[1]? with
                          | some expression => evalWithDb state oldEnv expression
                          | none => pure (.text "constraint failed")
                        throw (toString message)
                discard <| executeSelect state query
              | _ => pure ()
    pure state
end

def triggerRecursionDepth : Nat := 1000

def insertValueRowsBase (db : Database) (tableName : String)
    (names : Option (Array String)) (rows : Array (Array Value))
    (conflict : ConflictAction := .default) : Except String (Database × QueryResult) :=
  insertValueRowsBaseFuel (Nat.succ triggerRecursionDepth) db tableName names rows conflict

def fireDeleteTriggers (db : Database) (table : Table)
    (deleted : Array StoredRow) (onlyTiming : Option TriggerTiming := none) : Except String Database :=
  fireDeleteTriggersFuel (Nat.succ triggerRecursionDepth) db table deleted onlyTiming

def applyDeleteEffectsFuel : Nat → Database → Table → Array StoredRow → Bool →
    Except String Database
  | 0, _, _, _, _ => throw "too many levels of cascading deletes"
  | fuel + 1, db, table, deleted, beforeAlreadyFired => do
    let mut state := db
    if state.foreignKeys then
      for childSchema in state.tables do
        let child ← optionOr (findTable? state childSchema.name) s!"no such table: {childSchema.name}"
        let mut victimIds : Array Int := #[]
        for childIndex in [:child.columns.size] do
          if let some reference := child.columns[childIndex]!.references then
            if reference.onDeleteCascade && nameEq reference.table table.name then
              let parentIndex ← referencedColumnIndex table reference
              for childRow in child.rows do
                let childValue := childRow.values[childIndex]?.getD .null
                if !(childValue matches .null) && deleted.any (fun parentRow =>
                    childValue.sqlEq (parentRow.values[parentIndex]?.getD .null) == .true) then
                  unless victimIds.contains childRow.rowid do victimIds := victimIds.push childRow.rowid
        unless victimIds.isEmpty do
          let victims := child.rows.filter fun row => victimIds.contains row.rowid
          let retained := child.retainRows fun row => !victimIds.contains row.rowid
          state := replaceTable state retained
          state ← applyDeleteEffectsFuel fuel state child victims false
    fireDeleteTriggers state table deleted (if beforeAlreadyFired then some .after else none)

def deleteCascadeDepth : Nat := 1000

def applyDeleteEffects (db : Database) (table : Table)
    (deleted : Array StoredRow) (beforeAlreadyFired : Bool := false) : Except String Database :=
  applyDeleteEffectsFuel (Nat.succ deleteCascadeDepth) db table deleted beforeAlreadyFired

end SQLeanite
