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

private def executeStatement (state : Core.State) (statement : Statement) (source : String) :
    Except String (Core.State × List Core.Result) :=
  match statement with
  | .select select =>
      match CoreSQL.simpleQuery? state select with
      | some (tableName, query) =>
          let optimized := CoreOptimizerBridge.optimize tableName query
          (Core.execute state (.query tableName optimized)).map
            fun result => (result.1, [result.2])
      | none => CoreSourceSQL.executeStatement state statement source
  | _ => CoreSourceSQL.executeStatement state statement source

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
    (paths : CoreWALFileAdapter.Paths) (onResults : List Core.Result → IO Unit) (source : String) : Core.State → List Statement →
      List Core.Result → IO (Core.State × Except String (List Core.Result))
  | state, [], reversed => pure (state, .ok reversed.reverse)
  | state, statement :: statements, reversed => do
      if CoreFileEngine.requiresWriteAccess state statement then
        CoreFileAdapter.requireWritableAccess paths.main
        CoreWALFileAdapter.requireWritableFormat paths
      let execution ← match statement with
        | .select select =>
            match CoreSQL.observeReadSelect? state select with
            | none => pure (executeStatement state statement source)
            | some observed =>
                match observed.toExcept with
                | .error message => do
                    onResults [observed.execution.result]
                    pure (.error message)
                | .ok result => pure (.ok (result.state, [result.result]))
        | _ => pure (executeStatement state statement source)
      match execution with
      | .error message => pure (state, .error message)
      | .ok (next, results) => do
          let persisted ←
            if CoreFileEngine.requiresPersistence state statement &&
                !CoreSQL.schemaNoop state statement &&
                !CoreFileEngine.dataWriteNoop state next statement results then do
              let reopened ← CoreWALFileAdapter.commit syncOps paths next.database (some next.headers.main)
              unless CoreFileEngine.databaseContents reopened ==
                  CoreFileEngine.databaseContents next.database do
                throw (IO.userError "WAL commit reopened different logical contents")
              pure { next with database := reopened }
            else pure next
          runStatementsGo syncOps paths onResults source persisted statements
            (results.foldl (fun acc result => result :: acc) reversed)

/-- Stack-safe execution of a WAL statement batch. -/
private def runStatements (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) (onResults : List Core.Result → IO Unit) (state : Core.State)
    (statements : List Statement) (source : String) :
    IO (Core.State × Except String (List Core.Result)) :=
  runStatementsGo syncOps paths onResults source state statements []

/-- Preserve the executed prefix when a later source statement fails admission.
The transaction state is carried between chunks until commit, rollback or error. -/
private def runChunks (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) (onResults : List Core.Result → IO Unit) : Core.State → List String → List Core.Result →
      IO (Core.State × Except String (List Core.Result))
  | state, [], reversed => pure (state, .ok reversed.reverse)
  | state, chunk :: chunks, reversed => do
      match CoreTokenGrammar.parseStatements chunk with
      | .error message => pure (state, .error message)
      | .ok statements =>
          let (next, result) ← runStatements syncOps paths onResults state statements.toList chunk
          match result with
          | .error message => pure (next, .error message)
          | .ok results => do
              onResults results
              runChunks syncOps paths onResults next chunks
                (results.foldl (fun acc result => result :: acc) reversed)

/-- Run each source chunk against one WAL snapshot, retaining live transaction
state. Callers may observe completed results before a later failure. A result is observed only after its required publication. -/
def executeObserved (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) (sql : String)
    (onResults : List Core.Result → IO Unit) :
    IO (Except String (List Core.Result)) := do
  let (database, metadata) ← CoreWALFileAdapter.reopenWithMetadata paths
  let (_, result) ← runChunks syncOps paths onResults
    { database := database, headers := { main := metadata } } (SQLite.Script.split sql) []
  return result

/-- Execute SQL against one immutable WAL snapshot. -/
def execute (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) (sql : String) :
    IO (Except String (List Core.Result)) :=
  executeObserved syncOps paths sql (fun _ => pure ())

def checkpoint (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) : IO Unit := do
  let _ ← CoreWALFileAdapter.checkpoint syncOps paths

end CoreWALFileEngine
end SQLeanite
