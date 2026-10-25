import SQLeanite.CoreWALFileAdapter
import SQLeanite.CoreFileEngine
import SQLeanite.CoreOptimizerBridge

/-!
# WAL-backed execution for arbitrary Core schemas

The arbitrary-schema counterpart of `LegacyWALFileEngine`. Writers are
serialized by the caller; readers take no process lock because they never
publish, and a reader observes a whole committed image or the main file, never
a partial write.

Statement dispatch and the persistence decision are shared with
`CoreFileEngine`, so WAL and rollback-journal execution cannot drift apart on
when a commit is required.
-/

namespace SQLeanite
namespace CoreWALFileEngine

private def executeStatement (state : Core.State) (statement : Statement) :
    Except String (Core.State × List Core.Result) :=
  match statement with
  | .select select =>
      match CoreSQL.simpleQuery? state select with
      | some (tableName, query) =>
          let optimized := CoreOptimizerBridge.optimize tableName query
          (Core.execute state (.query tableName optimized)).map
            fun result => (result.1, [result.2])
      | none => CoreSQL.executeStatement state statement
  | _ => CoreSQL.executeStatement state statement

def needsWriter (statements : List Statement) : Bool :=
  statements.any CoreFileEngine.statementWrites

theorem needsWriter_false_member (statements : List Statement)
    (readOnly : needsWriter statements = false) {statement : Statement}
    (member : statement ∈ statements) :
    CoreFileEngine.statementWrites statement = false := by
  unfold needsWriter at readOnly
  rw [List.any_eq_false] at readOnly
  cases writes : CoreFileEngine.statementWrites statement with
  | false => rfl
  | true => exact False.elim (readOnly statement member writes)

private def runStatementsGo (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) : Core.State → List Statement →
      List Core.Result → IO (Core.State × Except String (List Core.Result))
  | state, [], reversed => pure (state, .ok reversed.reverse)
  | state, statement :: statements, reversed => do
      if CoreFileEngine.statementWrites statement && !CoreSQL.schemaNoop state statement then
        CoreWALFileAdapter.requireWritableFormat paths
      match executeStatement state statement with
      | .error message => pure (state, .error message)
      | .ok (next, results) => do
          let persisted ←
            if CoreFileEngine.requiresPersistence state statement &&
                !CoreSQL.schemaNoop state statement then do
              let reopened ← CoreWALFileAdapter.commit syncOps paths next.database
              unless CoreFileEngine.databaseContents reopened ==
                  CoreFileEngine.databaseContents next.database do
                throw (IO.userError "WAL commit reopened different logical contents")
              pure { next with database := reopened }
            else pure next
          runStatementsGo syncOps paths persisted statements
            (results.foldl (fun acc result => result :: acc) reversed)

/-- Stack-safe execution of a WAL statement batch. -/
private def runStatements (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) (state : Core.State)
    (statements : List Statement) :
    IO (Core.State × Except String (List Core.Result)) :=
  runStatementsGo syncOps paths state statements []

/-- Execute SQL against one immutable WAL snapshot. -/
def execute (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) (sql : String) :
    IO (Except String (List Core.Result)) := do
  let database ← CoreWALFileAdapter.reopen paths
  match CoreTokenGrammar.parseStatements sql with
  | .error message => return .error message
  | .ok statements =>
      let (_, result) ← runStatements syncOps paths
        { database := database } statements.toList
      return result

def checkpoint (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) : IO Unit := do
  let _ ← CoreWALFileAdapter.checkpoint syncOps paths

end CoreWALFileEngine
end SQLeanite
