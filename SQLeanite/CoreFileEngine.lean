import SQLeanite.CoreFileAdapter
import SQLeanite.CoreOptimizerBridge
import Std.Sync.Mutex

namespace SQLeanite
namespace CoreFileEngine

inductive FileProvenance where
  | generated
  | foreign
  deriving DecidableEq

/-- Logical connection state and its optional physical-index certificates.
The dependent cache cannot be paired with a different database: every stored
certificate carries membership in `state.database`.  Statement transitions
retarget the cache through a checked constructor before the new state can be
installed. -/
structure LiveState where
  state : Core.State
  certificates : Option
    (List (CoreFileAdapter.StoredIntegerIndex state.database)) := none

def LiveState.retarget (live : LiveState) (state : Core.State) : LiveState := {
  state
  certificates := live.certificates.map fun certificates =>
    CoreFileAdapter.retargetIntegerIndexCertificates certificates state.database }

structure Connection where
  paths : CoreFileAdapter.Paths
  syncOps : CoreFileAdapter.SyncOps
  private state : Std.Mutex LiveState
  private pageState : IO.Ref (Option CoreChunkPageState.State)
  private validatedOpen : IO.Ref (Option CoreFileAdapter.ValidatedOpenState)
  -- Page count and catalog, decoded once rather than per statement. Cleared
  -- alongside the other caches on every write.
  private fileGeometry : IO.Ref (Option CoreFileAdapter.FileGeometry)
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
    state := ← Std.Mutex.new { state := { database := database } }
    pageState := ← IO.mkRef pageState
    validatedOpen := ← IO.mkRef opened
    fileGeometry := ← IO.mkRef none
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
  connection.fileGeometry.set none
  connection.provenance.set .generated
  return { next with database := reopened }

private def persistIfNeeded (connection : Connection) (current next : Core.State)
    (statement : Statement) : IO Core.State := do
  if requiresPersistence current statement then
    let physical ← connection.pageState.get
    match candidate : physical.bind fun state =>
        CoreChunkPageDelta.updateStateCandidate? state next.database with
    | some delta =>
        if sufficient : delta.table.tablePagesSufficient then
          match physical with
          | some state =>
            have candidateState :
                CoreChunkPageDelta.updateStateCandidate? state next.database =
                  some delta := by
              simpa using candidate
            match CoreFileAdapter.prepareOrdinaryDelta? state next.database
                delta candidateState sufficient with
            | some prepared =>
              let validated := (← connection.validatedOpen.get).bind fun current =>
                current.retarget? delta sufficient
              match ← CoreFileAdapter.commitLocalized connection.syncOps
                  connection.paths prepared.expectedBefore prepared.writes
                    delta.after.freePages with
              | some _ =>
                  connection.pageState.set (some delta.after)
                  connection.validatedOpen.set validated
                  return next
              | none => commitFull connection next
            | none => commitFull connection next
          | none => False.elim (by simp at candidate)
        else
          have canonicalCandidate :
              CoreChunkPageDelta.updateStateCandidate? delta.before
                delta.after.database = some delta := by
            cases physical with
            | none => simp at candidate
            | some state =>
              have candidateState :
                  CoreChunkPageDelta.updateStateCandidate? state next.database =
                    some delta := by
                simpa using candidate
              have endpoints :=
                CoreChunkPageDelta.updateStateCandidate?_endpoints candidateState
              rw [endpoints.1, endpoints.2]
              exact candidateState
          let validation ← connection.validatedOpen.get
          let input ← IO.FS.readBinFile connection.paths.main
          let prepared := validation.bind fun validated =>
            if delta.table.after.table.rows.length <
                delta.table.before.table.rows.length then
              -- The append and insertion preparations both reject a shrinking
              -- table.  Dispatch directly instead of decoding the header and
              -- catalog three times before reaching deletion.
              match CoreFileAdapter.preparePageDirectedIndexDelete? validated
                  input delta canonicalCandidate with
              | some directed => some directed
              | none => CoreFileAdapter.prepareLocalizedLastIndex? validated
                  input.data.toList delta canonicalCandidate
            else
              match CoreFileAdapter.prepareAppendedIndex? validated input delta
                  canonicalCandidate with
              | some appended => some appended
              | none =>
                  match CoreFileAdapter.preparePageDirectedIndexInsert? validated
                      input delta canonicalCandidate with
                  | some directed => some directed
                  | none => CoreFileAdapter.prepareLocalizedLastIndex? validated
                      input.data.toList delta canonicalCandidate
          match prepared with
          | some prepared =>
              match ← CoreFileAdapter.commitLocalized connection.syncOps
                  connection.paths prepared.expectedBefore prepared.writes
                    prepared.state.freePages with
              | some _ =>
                  connection.pageState.set (some prepared.state)
                  connection.validatedOpen.set (some prepared.validated)
                  connection.fileGeometry.set none
                  return next
              | none => commitFull connection next
          | none => commitFull connection next
    | none => commitFull connection next
  else return next

private def executeStatement (connection : Connection) (live : LiveState)
    (statement : Statement) :
    IO (LiveState × Except String (Core.State × List Core.Result)) := do
  let state := live.state
  match statement with
  | .select select =>
      match CoreSQL.simpleQuery? state select with
      | some (tableName, query) =>
          match found : state.database.findTable? tableName with
          | some table =>
              have tableMember : table ∈ state.database.tables :=
                state.database.findTable?_mem found
              let optimized := CoreOptimizerBridge.optimize tableName query
              let (certificates, live) ←
                match table.chooseAccessPath optimized.predicate with
                | .equalityIndex _ | .rangeIndex _ =>
                    match live.certificates with
                    | some retained => pure (retained, live)
                    | none => do
                        let loaded ← CoreFileAdapter.loadIntegerIndexCertificates
                          connection.paths state.database
                        let loadedLive : LiveState := {
                          live with certificates := some loaded }
                        pure (loaded, loadedLive)
                | _ => pure (live.certificates.getD [], live)
              match CoreFileAdapter.lookupCertifiedIndexCandidates certificates
                  table tableMember optimized with
              | some lookup =>
                  return (live, .ok (state, [lookup.result]))
              | none =>
                  let geometry ← match ← connection.fileGeometry.get with
                    | some cached => pure (some cached)
                    | none => do
                        let decoded ← CoreFileAdapter.readFileGeometry
                          connection.paths
                        connection.fileGeometry.set decoded
                        pure decoded
                  match ← (match geometry with
                    | none => pure none
                    | some geometry =>
                        CoreFileAdapter.lookupIndexCandidatesWith geometry
                          connection.paths table optimized) with
                  | some lookup =>
                      match ← connection.provenance.get with
                      | .generated =>
                          -- Generated images are connected to the encoder
                          -- refinement. A certificate miss is only an
                          -- optimization miss, so execute the verified plan
                          -- directly without the foreign-byte comparison.
                          return (live,
                            (Core.execute state (.query tableName optimized)).map
                              fun result => (result.1, [result.2]))
                      | .foreign =>
                          -- This is the sole validating comparison boundary:
                          -- arbitrary external bytes carry no encoder witness.
                          return (live,
                            (Core.executeUncertifiedQueryWithCandidates state
                              tableName optimized lookup.candidates).map fun result =>
                                (result.1, [result.2]))
                  | none =>
                      return (live,
                        (Core.execute state (.query tableName optimized)).map
                          fun result => (result.1, [result.2]))
          | none => return (live, CoreSQL.executeStatement state statement)
      | none => return (live, CoreSQL.executeStatement state statement)
  | _ => return (live, CoreSQL.executeStatement state statement)

private def runStatements (connection : Connection) : LiveState →
    List Statement → IO (LiveState × Except String (List Core.Result))
  | live, [] => pure (live, .ok [])
  | live, statement :: statements => do
      let (cached, execution) ← executeStatement connection live statement
      match execution with
      | .error message => pure (cached, .error message)
      | .ok (next, results) => do
          let persisted ← persistIfNeeded connection live.state next statement
          let advanced := cached.retarget persisted
          let (finalState, tail) ← runStatements connection advanced statements
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
  connection.state.atomically do return (← get).state

end CoreFileEngine
end SQLeanite
