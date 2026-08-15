import SQLeanite.CoreFileAdapter
import SQLeanite.CoreOptimizerBridge
import Std.Sync.Mutex

namespace SQLeanite
namespace CoreFileEngine

inductive FileProvenance where
  | generated
  | foreign
  deriving DecidableEq

structure Connection where
  paths : CoreFileAdapter.Paths
  syncOps : CoreFileAdapter.SyncOps
  private state : Std.Mutex Core.State
  private pageState : IO.Ref (Option CoreChunkPageState.State)
  private validatedOpen : IO.Ref (Option CoreFileAdapter.ValidatedOpenState)
  -- `none` means not yet loaded; `some []` means loaded and genuinely empty.
  -- Testing emptiness instead re-read and re-decoded the whole main file on
  -- every query whenever certification legitimately produced nothing.
  private indexCertificates : IO.Ref (Option (List CoreFileAdapter.StoredIntegerIndex))
  private provenance : IO.Ref FileProvenance

def databaseContents (database : Core.Database) :=
  database.contents

def reopen (syncOps : CoreFileAdapter.SyncOps)
    (paths : CoreFileAdapter.Paths) : IO Connection := do
  CoreFileAdapter.recoverInPlace syncOps paths
  -- Supported physical trees are decoded once into both the logical database
  -- and their persistent page identities.  Wider external SQLite trees retain
  -- the general compatibility decoder and independent validating loader.
  let opened ← CoreFileAdapter.loadOpenState paths
  let generated ← CoreFileAdapter.generatedImageStamp paths
  let (database, pageState) ← match opened with
    | some validated => pure (validated.state.database, some validated.state)
    | none => do
        let database ← CoreFileAdapter.reopen paths
        let pageState ← CoreFileAdapter.loadPageState paths database
        pure (database, pageState)
  return {
    paths
    syncOps
    state := ← Std.Mutex.new { database := database }
    pageState := ← IO.mkRef pageState
    validatedOpen := ← IO.mkRef opened
    -- Index certificates are needed only by secondary-index SELECTs. Loading
    -- them here made every write-only connection decode every index twice.
    indexCertificates := ← IO.mkRef none
    provenance := ← IO.mkRef (if generated then .generated else .foreign) }

def create (syncOps : CoreFileAdapter.SyncOps)
    (paths : CoreFileAdapter.Paths) : IO Connection := do
  CoreFileAdapter.create syncOps paths Core.Database.empty
  reopen syncOps paths

def statementWrites : Statement → Bool
  | .createTable .. | .createIndex .. | .insert .. | .delete .. | .update .. => true
  | _ => false

def requiresPersistence (state : Core.State) (statement : Statement) : Bool :=
  match statement with
  | .commit => state.transactionSnapshot.isSome
  | _ => statementWrites statement && state.transactionSnapshot.isNone

theorem requiresPersistence_write_in_transaction (state : Core.State)
    (statement : Statement) (writes : statementWrites statement = true)
    (active : state.transactionSnapshot.isSome = true) :
    requiresPersistence state statement = false := by
  have inactiveFalse : state.transactionSnapshot.isNone = false := by
    cases snapshot : state.transactionSnapshot <;> simp_all
  cases statement <;> simp_all [requiresPersistence, statementWrites]

private def commitFull (connection : Connection) (next : Core.State) :
    IO Core.State := do
  let (validated, _) ← CoreFileAdapter.commit connection.syncOps
    connection.paths next.database
  let reopened := validated.state.database
  unless databaseContents reopened == databaseContents next.database do
    throw (IO.userError "general MVP commit reopened different logical contents")
  connection.pageState.set (some validated.state)
  connection.validatedOpen.set (some validated)
  connection.indexCertificates.set none
  connection.provenance.set .generated
  return { next with database := reopened }

private def persistIfNeeded (connection : Connection) (current next : Core.State)
    (statement : Statement) : IO Core.State := do
  if requiresPersistence current statement then
    let physical ← connection.pageState.get
    let localized := physical.bind fun state =>
      CoreChunkPageDelta.updateStateCandidate? state next.database
    match localized with
    | some delta =>
        if sufficient : delta.table.tablePagesSufficient then
          let validated := (← connection.validatedOpen.get).bind fun current =>
            current.retarget? delta sufficient
          match CoreChunkPageDelta.beforeWrites delta.table,
              CoreChunkPageDelta.writes delta.table with
          | some expectedBefore, some writes =>
              match ← CoreFileAdapter.commitLocalized connection.syncOps
                  connection.paths expectedBefore writes delta.after.freePages with
              | some _ =>
                  connection.pageState.set (some delta.after)
                  connection.validatedOpen.set validated
                  -- Retarget only what was already loaded. A `none` here means
                  -- nothing was cached, and must stay `none` rather than
                  -- becoming a loaded-and-empty result.
                  connection.indexCertificates.modify fun cached =>
                    cached.map fun certificates =>
                      CoreFileAdapter.retargetIntegerIndexCertificates certificates
                        next.database
                  return next
              | none => commitFull connection next
          | _, _ =>
              throw (IO.userError "proved page delta contained page zero")
        else
          let validation ← connection.validatedOpen.get
          let input ← IO.FS.readBinFile connection.paths.main
          let prepared := validation.bind fun validated =>
            if delta.table.after.table.rows.length <
                delta.table.before.table.rows.length then
              -- The append and insertion preparations both reject a shrinking
              -- table.  Dispatch directly instead of decoding the header and
              -- catalog three times before reaching deletion.
              match CoreFileAdapter.preparePageDirectedIndexDelete? validated
                  input delta with
              | some directed => some directed
              | none => CoreFileAdapter.prepareLocalizedLastIndex? validated
                  input.data.toList delta
            else
              match CoreFileAdapter.prepareAppendedIndex? validated input delta with
              | some appended => some appended
              | none =>
                  match CoreFileAdapter.preparePageDirectedIndexInsert? validated
                      input delta with
                  | some directed => some directed
                  | none => CoreFileAdapter.prepareLocalizedLastIndex? validated
                      input.data.toList delta
          match prepared with
          | some prepared =>
              match ← CoreFileAdapter.commitLocalized connection.syncOps
                  connection.paths prepared.expectedBefore prepared.writes
                    prepared.state.freePages with
              | some _ =>
                  connection.pageState.set (some prepared.state)
                  connection.validatedOpen.set (some prepared.validated)
                  -- This path changes the physical index image, so retained
                  -- certificates must be rebuilt on the next indexed read.
                  connection.indexCertificates.set none
                  return next
              | none => commitFull connection next
          | none => commitFull connection next
    | none => commitFull connection next
  else return next

/-- Whether to attempt the certified index lookup for this table.

`CoreFileAdapter.lookupCertifiedIndexCandidates` requires
`stored.table.rows = table.rows`, a structural comparison of every row, so the
attempt costs O(table) per query whether or not it succeeds. Measured marginal
cost per read at 512-byte rows: 0.76 ms at 250 rows rising linearly to 8.64 ms at
2000. The verified in-memory executor that runs when the attempt misses is
strictly cheaper, so above this size the certified attempt is pure overhead --
dropping the index outright made the same hundred reads run 116 ms instead of
651 ms.

**This is a stopgap with a named deletion condition.** Delete this function, and
attempt the certified path unconditionally, once the certificate carries its own
validity rather than re-deriving it: either the table holds its index
certificate as proof-carrying state, or the lookup validates only the candidates
it returns. Both make the check independent of table size, and neither is a
heuristic. Until then a size gate is the honest choice, because the certified
path as built cannot beat a scan at any size. -/
private def certifiedLookupWorthAttempting (table : Core.Table) : Bool :=
  table.rows.length ≤ 256

private def executeStatement (connection : Connection) (state : Core.State)
    (statement : Statement) : IO (Except String (Core.State × List Core.Result)) := do
  match statement with
  | .select select =>
      match CoreSQL.simpleQuery? state select with
      | some (tableName, query) =>
          match state.database.findTable? tableName with
          | some table =>
              let optimized := CoreOptimizerBridge.optimize tableName query
              let certificates ← match table.chooseAccessPath optimized.predicate with
                | .equalityIndex _ | .rangeIndex _ =>
                    if certifiedLookupWorthAttempting table then do
                      match ← connection.indexCertificates.get with
                      | some retained => pure retained
                      | none =>
                          let loaded ← CoreFileAdapter.loadIntegerIndexCertificates
                            connection.paths state.database
                          connection.indexCertificates.set (some loaded)
                          pure loaded
                    else pure []
                | _ => pure ((← connection.indexCertificates.get).getD [])
              match CoreFileAdapter.lookupCertifiedIndexCandidates certificates
                  table optimized with
              | some lookup =>
                  return .ok (state, [lookup.result])
              | none =>
                  match ← CoreFileAdapter.lookupIndexCandidates
                      connection.paths table optimized with
                  | some lookup =>
                      match ← connection.provenance.get with
                      | .generated =>
                          -- Generated images are connected to the encoder
                          -- refinement. A certificate miss is only an
                          -- optimization miss, so execute the verified plan
                          -- directly without the foreign-byte comparison.
                          return (Core.execute state (.query tableName optimized)).map
                            fun result => (result.1, [result.2])
                      | .foreign =>
                          -- This is the sole validating comparison boundary:
                          -- arbitrary external bytes carry no encoder witness.
                          return (Core.executeUncertifiedQueryWithCandidates state
                            tableName optimized lookup.candidates).map fun result =>
                              (result.1, [result.2])
                  | none =>
                      return (Core.execute state (.query tableName optimized)).map
                        fun result => (result.1, [result.2])
          | none => return CoreSQL.executeStatement state statement
      | none => return CoreSQL.executeStatement state statement
  | _ => return CoreSQL.executeStatement state statement

private def runStatements (connection : Connection) : Core.State →
    List Statement → IO (Core.State × Except String (List Core.Result))
  | state, [] => pure (state, .ok [])
  | state, statement :: statements => do
      match ← executeStatement connection state statement with
      | .error message => pure (state, .error message)
      | .ok (next, results) => do
          let persisted ← persistIfNeeded connection state next statement
          let (finalState, tail) ← runStatements connection persisted statements
          match tail with
          | .error message => pure (finalState, .error message)
          | .ok remaining => pure (finalState, .ok (results ++ remaining))

def execute (connection : Connection) (sql : String) :
    IO (Except String (List Core.Result)) :=
  connection.state.atomically do
    let current ← get
    match parse sql with
    | .error message => return .error message
    | .ok statements =>
        let (finalState, result) ← runStatements connection current statements.toList
        set finalState
        return result

def snapshot (connection : Connection) : IO Core.State :=
  connection.state.atomically get

end CoreFileEngine
end SQLeanite
