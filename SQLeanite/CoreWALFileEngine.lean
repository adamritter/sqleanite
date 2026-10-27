import SQLeanite.CoreDerivedSQL
import SQLeanite.CoreWALFileAdapter
import SQLeanite.SQLite.IndexCatalog
import SQLeanite.CoreFileEngine
import SQLeanite.CoreOptimizerBridge

/-!
# WAL-backed execution for arbitrary Core schemas

The arbitrary-schema counterpart of `LegacyWALFileEngine`. Shared SQLite
byte-range locks serialize writers across both engines. Read-only batches copy
a protected snapshot, then release the file locks before evaluating SQL.

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
      if CoreDerivedSQL.hasDerived select.compoundHeight select then
        CoreDerivedSQL.executeStatement state statement source
      else
      let select := CoreConnectionSQL.select state select.compoundHeight select
      match CoreSQL.simpleQuery? state select with
      | some (tableName, query) =>
          let optimized := CoreOptimizerBridge.optimize tableName query
          (Core.execute state (.query tableName optimized)).map
            fun result => (result.1, [result.2])
      | none => CoreDerivedSQL.executeStatement state statement source
  | _ => CoreDerivedSQL.executeStatement state statement source

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
    (session : CoreWALFileAdapter.Session) (catalog : IO.Ref SQLite.IndexCatalog.State)
    (onResults : List Core.Result → IO Unit) (source : String) : Core.State → List Statement →
      List Core.Result → IO (Core.State × Except String (List Core.Result))
  | state, [], reversed => pure (state, .ok reversed.reverse)
  | state, statement :: statements, reversed => do
      if CoreFileEngine.requiresWriteAccess state statement then
        CoreFileAdapter.requireWritableAccess session.paths.main
        CoreWALFileAdapter.requireWritableFormat session
      let execution ← match statement with
        | .select select =>
            if CoreSchemaRead.uses select.compoundHeight select then do
              let records ← CoreWALFileAdapter.schemaRows session
              pure (CoreSchemaRead.execute state select records)
            else if CoreDerivedSQL.hasDerived select.compoundHeight select then
              pure (executeStatement state statement source)
            else
            let select := CoreConnectionSQL.select state select.compoundHeight select
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
          let retained ← match SQLite.IndexCatalog.track (← catalog.get) state next statement source with
            | .ok value => pure value
            | .error message => throw (IO.userError message)
          catalog.set retained
          let declarations : List CoreDecode.CatalogEntry := retained.sources.map fun entry => {
            kind := "index", name := entry.name, table := entry.table,
            rootPage := 0, sql := some entry.sql }
          let persisted ←
            if CoreFileEngine.requiresPersistence state statement &&
                !CoreSQL.schemaNoop state statement &&
                !CoreFileEngine.dataWriteNoop state next statement results then do
              let reopened ← CoreWALFileAdapter.commitInSession syncOps session next.database (some next.headers.main) declarations
              unless CoreFileEngine.databaseContents reopened ==
                  CoreFileEngine.databaseContents next.database do
                throw (IO.userError "WAL commit reopened different logical contents")
              pure { next with database := reopened }
            else pure next
          runStatementsGo syncOps session catalog onResults source persisted statements
            (results.foldl (fun acc result => result :: acc) reversed)

/-- Stack-safe execution of a WAL statement batch. -/
private def runStatements (syncOps : CoreWALFileAdapter.SyncOps)
    (session : CoreWALFileAdapter.Session) (catalog : IO.Ref SQLite.IndexCatalog.State)
    (onResults : List Core.Result → IO Unit) (state : Core.State)
    (statements : List Statement) (source : String) :
    IO (Core.State × Except String (List Core.Result)) :=
  runStatementsGo syncOps session catalog onResults source state statements []

/-- Preserve the executed prefix when a later source statement fails admission.
The transaction state is carried between chunks until commit, rollback or error. -/
private def runChunks (syncOps : CoreWALFileAdapter.SyncOps)
    (session : CoreWALFileAdapter.Session) (catalog : IO.Ref SQLite.IndexCatalog.State)
    (onResults : List Core.Result → IO Unit) : Core.State → List String → List Core.Result →
      IO (Core.State × Except String (List Core.Result))
  | state, [], reversed => pure (state, .ok reversed.reverse)
  | state, chunk :: chunks, reversed => do
      match CoreTokenGrammar.parseStatements chunk with
      | .error message => pure (state, .error message)
      | .ok statements =>
          let (next, result) ← runStatements syncOps session catalog onResults state statements.toList chunk
          match result with
          | .error message => pure (next, .error message)
          | .ok results => do
              onResults results
              runChunks syncOps session catalog onResults next chunks
                (results.foldl (fun acc result => result :: acc) reversed)

/-- Run each source chunk against one WAL snapshot, retaining live transaction
state. Callers may observe completed results before a later failure. A result is observed only after its required publication. -/
def executeObserved (syncOps : CoreWALFileAdapter.SyncOps)
    (paths : CoreWALFileAdapter.Paths) (sql : String)
    (onResults : List Core.Result → IO Unit) :
    IO (Except String (List Core.Result)) := do
  let chunks := SQLite.Script.split sql
  let statements := chunks.flatMap fun source =>
    ((CoreTokenGrammar.parseStatements source).toOption.getD #[]).toList
  let writable := needsWriter statements
  let run := fun (session : CoreWALFileAdapter.Session)
      (opened : Core.Database × CoreMultiFreelist.HeaderMetadata) => do
    let catalog ← IO.mkRef ({} : SQLite.IndexCatalog.State)
    let (_, result) ← runChunks syncOps session catalog onResults
      { database := opened.1, headers := { main := opened.2 } } chunks []
    return result
  if writable then
    SQLite.WALShared.withSession paths true fun session => do
      run session (← CoreWALFileAdapter.reopenInSession session)
  else
    let opened ← CoreWALFileAdapter.reopenWithMetadata paths
    -- No statement on this branch can publish; this value is never used for IO.
    run { paths, nativeBigEndian := false, firstConnection := false, writable := false } opened

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
