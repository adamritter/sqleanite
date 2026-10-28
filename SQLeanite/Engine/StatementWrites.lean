import SQLeanite.Engine.ExecuteCore

namespace SQLeanite

def Statement.writes : Statement → Bool
  | .createTable .. | .createStrictTable .. | .createTableAs .. | .createView ..
  | .dropTable .. | .dropView .. | .createIndex .. | .dropIndex ..
  | .createTrigger .. | .dropTrigger .. | .alterAddColumn .. | .alterDropColumn .. | .alterRenameTable .. | .alterRenameColumn ..
  | .insert .. | .insertSelect .. | .delete .. | .update .. | .reindex => true
  | .withRecursive .. | .withCte .. => true
  | _ => false

def execute (db : Database) (statement : Statement) : Except String (Database × QueryResult) :=
  if db.readOnly && statement.writes then .error "attempt to write a readonly database"
  else executeCore db statement

theorem execute_success_wellFormed {database resultDatabase : Database}
    {statement : Statement} {result : QueryResult}
    (_success : execute database statement = .ok (resultDatabase, result)) :
    resultDatabase.WellFormed :=
  resultDatabase.wellFormed

def executeAll (db : Database) (statements : Array Statement) : Except String (Database × QueryResult) := do
  let mut state := db
  let mut last := {}
  let mut retainQueryRows := false
  for stmt in statements do
    let (next, result) ← execute state stmt
    state := next
    if let some message := result.deferredError then throw message
    if !result.rows.isEmpty then
      last := { result with rows := last.rows ++ result.rows }
      if (stmt matches .select _) || (stmt matches .values _) then retainQueryRows := true
      else if stmt matches .pragma .. then retainQueryRows := false
    else if result.reportsChanges && !retainQueryRows then last := result
    else if (stmt matches .select _) || (stmt matches .values _) || (stmt matches .pragma ..) then
      if last.rows.isEmpty then last := result
  pure (state, last)

/-- Execute statements sequentially while retaining commits from statements before an error. -/
def executeAllProgress (db : Database) (statements : Array Statement) : Database × Except String QueryResult := Id.run do
  let mut state := db
  let mut last : QueryResult := {}
  let mut retainQueryRows := false
  for stmt in statements do
    match execute state stmt with
    | .error message =>
      if message.startsWith rollbackConflictPrefix then
        let restored := match state.transactionSnapshot with
          | some snapshot => state.restoreSnapshot snapshot
          | none => state
        return (restored, .error (message.drop rollbackConflictPrefix.length).toString)
      return (state, .error message)
    | .ok (next, result) =>
      state := next
      if let some message := result.deferredError then return (state, .error message)
      if !result.rows.isEmpty then
        last := { result with rows := last.rows ++ result.rows }
        if (stmt matches .select _) || (stmt matches .values _) then retainQueryRows := true
        else if stmt matches .pragma .. then retainQueryRows := false
      else if result.reportsChanges && !retainQueryRows then last := result
      else if (stmt matches .select _) || (stmt matches .values _) || (stmt matches .pragma ..) then
        if last.rows.isEmpty then last := result
  return (state, .ok last)

def runSQL (db : Database) (sql : String) : Except String (Database × QueryResult) := do
  executeAll db (← parseLegacy sql)

def runSQLProgress (db : Database) (sql : String) : Database × Except String QueryResult :=
  match parseProgress sql false with
  | .error message => (db, .error message)
  | .ok (statements, parseError) =>
    let (next, outcome) := executeAllProgress db statements
    match outcome with
    | .error message => (next, .error message)
    | .ok result => match parseError with
      | some message => (next, .error message)
      | none => (next, .ok result)

theorem runSQLProgress_parse_error (db : Database) (sql message : String)
    (failure : parseProgress sql false = .error message) :
    runSQLProgress db sql = (db, .error message) := by
  simp [runSQLProgress, failure]

end SQLeanite
