import SQLeanite.SQLite.Script
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

/-- A write changes the logical index image, so retaining a read certificate
would require comparing that entire image with the post-state.  Drop the cache
instead; the physical wide-state certificate is maintained independently by
the write path and the read certificate is reloaded only if a later query can
use it. -/
def LiveState.invalidateCertificates (state : Core.State) : LiveState := {
  state
  -- `none` means "not loaded" and would make the next indexed read rescan the
  -- physical index to rebuild certificates.  `some []` means deliberately
  -- invalidated: use the generated-image page-directed path instead.
  certificates := some [] }

structure WideLiveState where
  state : CoreWidePageState.State
  textState : Option state.SingleIndexTextCertificate

/-- Existential keepalive for an invalidated decoded-index certificate.  Lean's
deterministic reference counting would otherwise free the entire old index on
the first write after a read batch, charging that O(index) destructor walk to
the write's tail latency.  At most one retired generation is retained. -/
structure RetiredIndexCertificates where
  database : Core.Database
  certificates : List (CoreFileAdapter.StoredIntegerIndex database)

def WideLiveState.ofState (state : CoreWidePageState.State) : WideLiveState := {
  state
  textState := state.singleIndexValuesText? }

structure Connection where
  paths : CoreFileAdapter.Paths
  syncOps : CoreFileAdapter.SyncOps
  private state : Std.Mutex LiveState
  private pageState : IO.Ref (Option CoreChunkPageState.State)
  private widePageState : IO.Ref (Option WideLiveState)
  private validatedOpen : IO.Ref (Option CoreFileAdapter.ValidatedOpenState)
  -- Page count and catalog, decoded once rather than per statement. Cleared
  -- alongside the other caches on every write.
  private fileGeometry : IO.Ref (Option CoreFileAdapter.FileGeometry)
  private provenance : IO.Ref FileProvenance
  private retiredCertificates : IO.Ref (Option RetiredIndexCertificates)

def databaseContents (database : Core.Database) :=
  database.contents

def reopen (syncOps : CoreFileAdapter.SyncOps)
    (paths : CoreFileAdapter.Paths) : IO Connection := do
  CoreFileAdapter.recoverInPlace syncOps paths
  CoreFileAdapter.requireReadable paths.main
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
  let widePageState ← CoreFileAdapter.loadWidePageState paths database
  return {
    paths
    syncOps
    state := ← Std.Mutex.new { state := { database := database } }
    pageState := ← IO.mkRef pageState
    widePageState := ← IO.mkRef (widePageState.map fun loaded =>
      WideLiveState.ofState loaded.state)
    validatedOpen := ← IO.mkRef opened
    fileGeometry := ← IO.mkRef none
    provenance := ← IO.mkRef (if generated then .generated else .foreign)
    retiredCertificates := ← IO.mkRef none }

def create (syncOps : CoreFileAdapter.SyncOps)
    (paths : CoreFileAdapter.Paths) : IO Connection := do
  CoreFileAdapter.create syncOps paths Core.Database.empty
  reopen syncOps paths

def statementWrites : Statement → Bool
  | .createTableAs .. | .createTable .. | .createIndex .. | .dropTable .. | .dropIndex .. | .insert .. | .insertSelect .. | .delete .. | .update .. | .alterRenameTable .. | .alterRenameColumn .. | .alterAddColumn .. | .alterDropColumn .. => true
  | _ => false

/-- A read-only transaction has no durable delta. Comparing logical contents
also avoids publishing changes canceled by a named rollback. -/
def transactionChanged (state : Core.State) : Bool :=
  state.transactionSnapshot.any (fun snapshot => state.database.contents != snapshot.contents)

theorem transactionChanged_equivalent (state : Core.State) (snapshot : Core.Database)
    (active : state.transactionSnapshot = some snapshot)
    (same : state.database.Equiv snapshot) : transactionChanged state = false := by
  simp [transactionChanged, active, Core.Database.Equiv] at *
  exact same

/-- Shared dispatch guard for both file engines. Schema no-ops do not require
write access, even when their statement form normally writes. -/
def requiresWriteAccess (state : Core.State) (statement : Statement) : Bool :=
  statementWrites statement && !CoreSQL.schemaNoop state statement

theorem requiresWriteAccess_readOnly (state : Core.State) (statement : Statement)
    (readOnly : statementWrites statement = false) : requiresWriteAccess state statement = false := by
  simp [requiresWriteAccess, readOnly]

theorem requiresWriteAccess_schemaNoop (state : Core.State) (statement : Statement)
    (noop : CoreSQL.schemaNoop state statement = true) : requiresWriteAccess state statement = false := by
  simp [requiresWriteAccess, noop]

def requiresPersistence (state : Core.State) (statement : Statement) : Bool :=
  match statement with
  | .commit => transactionChanged state
  | .release name => CoreSavepoint.releasesTransaction state name && transactionChanged state
  | _ => statementWrites statement && state.transactionSnapshot.isNone

/-- A zero-row DML statement need not publish an unchanged database. The
content comparison is necessary even with zero reported changes: AUTOINCREMENT
may still initialize or advance sqlite_sequence. Transaction controls are not
DML and must retain their snapshot-based publication decision. -/
def dataWriteNoop (current next : Core.State) (statement : Statement)
    (results : List Core.Result) : Bool :=
  match statement with
  | .insert .. | .insertSelect .. | .update .. | .delete .. =>
      !(results.any (fun result => result.changes != 0)) &&
        current.database.contents == next.database.contents
  | _ => false

theorem dataWriteNoop_insertSelect (current next : Core.State) (table : String)
    (columns : Option (Array String)) (query : Select) (conflict : ConflictAction)
    (returning : Array ResultColumn) (results : List Core.Result)
    (zeroChanges : results.any (fun result => result.changes != 0) = false)
    (same : current.database.Equiv next.database) :
    dataWriteNoop current next (.insertSelect table columns query conflict returning) results = true := by
  simp [dataWriteNoop, zeroChanges, Core.Database.Equiv] at *
  exact same

theorem dataWriteNoop_commit (current next : Core.State) (results : List Core.Result) :
    dataWriteNoop current next .commit results = false := rfl

theorem dataWriteNoop_release (current next : Core.State) (name : String)
    (results : List Core.Result) :
    dataWriteNoop current next (.release name) results = false := rfl

theorem requiresPersistence_commit_unchanged (state : Core.State)
    (unchanged : transactionChanged state = false) :
    requiresPersistence state .commit = false := by simp [requiresPersistence, unchanged]

theorem requiresPersistence_release_unchanged (state : Core.State) (name : String)
    (unchanged : transactionChanged state = false) :
    requiresPersistence state (.release name) = false := by simp [requiresPersistence, unchanged]

theorem requiresPersistence_write_in_transaction (state : Core.State)
    (statement : Statement) (writes : statementWrites statement = true)
    (active : state.transactionSnapshot.isSome = true) :
    requiresPersistence state statement = false := by
  have inactiveFalse : state.transactionSnapshot.isNone = false := by
    cases snapshot : state.transactionSnapshot <;> simp_all
  cases statement <;> simp_all [requiresPersistence, statementWrites]

private def commitFull (connection : Connection) (next : Core.State) :
    IO Core.State := do
  if ← CoreFileAdapter.needsPageSizeConversion connection.paths then
    let validated ← CoreFileAdapter.convertPageSize connection.syncOps connection.paths next.database
    let reopened := validated.state.database
    unless databaseContents reopened == databaseContents next.database do
      throw (IO.userError "converted image retained different logical contents")
    connection.pageState.set (some validated.state)
    connection.widePageState.set none
    connection.validatedOpen.set (some validated)
    connection.fileGeometry.set none
    connection.provenance.set .generated
    return { next with database := reopened }
  match ← CoreFileAdapter.commitWide connection.syncOps connection.paths
      next.database with
  | some (wideState, _) =>
      connection.widePageState.set (some (WideLiveState.ofState wideState.state))
      connection.pageState.set none
      connection.validatedOpen.set none
      connection.fileGeometry.set none
      connection.provenance.set .generated
      return next
  | none =>
      let (validated, _) ← CoreFileAdapter.commit connection.syncOps
        connection.paths next.database
      let reopened := validated.state.database
      unless databaseContents reopened == databaseContents next.database do
        throw (IO.userError "general MVP commit reopened different logical contents")
      connection.pageState.set (some validated.state)
      connection.widePageState.set none
      connection.validatedOpen.set (some validated)
      connection.fileGeometry.set none
      connection.provenance.set .generated
      return { next with database := reopened }

private def persistWideInsert? (connection : Connection) (current : Core.State)
    (statement : Statement) : IO (Option Core.State) := do
  let some wide ← connection.widePageState.get | return none
  match statement with
  | .insert table columns rows conflict =>
      unless conflict == .default || conflict == .abort do return none
      let [expressions] := rows.toList | return none
      let tableName := CoreNames.tableName wide.state.database table
      let some stored := wide.state.database.findTable? tableName | return none
      if stored.schema.autoIncrement then return none
      let .ok values := CoreSQL.rowValues stored.schema columns expressions |
        return none
      let some textState := wide.textState | return none
      let some executed := CoreWidePageDelta.executeInsert? wide.state
        current.transactionSnapshot tableName values | return none
      let some prepared ← CoreFileAdapter.prepareWideAppendIO?
          connection.paths.main executed textState.exact |
        return none
      match ← CoreFileAdapter.commitLocalizedCertified connection.syncOps
          connection.paths prepared.expectedBefore prepared.writes with
      | none => return none
      | some _ =>
          connection.widePageState.set (some {
            state := prepared.state
            textState := some ⟨prepared.textState⟩ })
          connection.pageState.set none
          connection.validatedOpen.set none
          connection.fileGeometry.set none
          connection.provenance.set .generated
          return some executed.next
  | _ => return none

private def persistIfNeeded (connection : Connection) (current next : Core.State)
    (statement : Statement) : IO Core.State := do
  if requiresPersistence current statement && !CoreSQL.schemaNoop current statement then
    match ← persistWideInsert? connection current statement with
    | some persisted => return persisted
    | none => pure ()
    let physical ← connection.pageState.get
    match candidate : physical.bind fun state =>
        CoreChunkPageDelta.updateStateCandidate? state next.database with
    | some delta =>
        if sufficient : delta.table.tablePagesSufficient then
          match physicalResult : physical with
          | some state =>
            have candidateState :
                CoreChunkPageDelta.updateStateCandidate? state next.database =
                  some delta := by
              simpa [physicalResult] using candidate
            match CoreFileAdapter.prepareOrdinaryDelta? state next.database
                delta candidateState sufficient with
            | some prepared =>
              let validated := (← connection.validatedOpen.get).bind fun current =>
                current.retarget? delta sufficient
              match ← CoreFileAdapter.commitLocalizedCertified connection.syncOps
                  connection.paths prepared.expectedBefore prepared.writes
                    delta.after.freePages with
              | some _ =>
                  connection.pageState.set (some delta.after)
                  connection.validatedOpen.set validated
                  return next
              | none => commitFull connection next
            | none => commitFull connection next
          | none => False.elim (by simp [physicalResult] at candidate)
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
              match ← CoreFileAdapter.commitLocalizedCertified connection.syncOps
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
    IO (LiveState × Except String (LiveState × List Core.Result)) := do
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
                  return (live, .ok (live, [lookup.result]))
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
                              fun result => (live, [result.2]))
                      | .foreign =>
                          -- This is the sole validating comparison boundary:
                          -- arbitrary external bytes carry no encoder witness.
                          return (live,
                            (Core.executeUncertifiedQueryWithCandidates state
                              tableName optimized lookup.candidates).map fun result =>
                                (live, [result.2]))
                  | none =>
                      return (live,
                        (Core.execute state (.query tableName optimized)).map
                          fun result => (live, [result.2]))
          | none =>
              return (live, (CoreSQL.executeStatement state statement).map
                fun result => (live.retarget result.1, result.2))
      | none =>
          return (live, (CoreSQL.executeStatement state statement).map
            fun result => (live.retarget result.1, result.2))
  | _ =>
      match CoreSQL.executeStatement state statement with
      | .error message => return (live, .error message)
      | .ok result =>
          match live.certificates with
          | some certificates =>
              unless certificates.isEmpty do
                connection.retiredCertificates.set (some {
                  database := state.database
                  certificates })
          | none => pure ()
          return (live, .ok
            (LiveState.invalidateCertificates result.1, result.2))

private def runStatementsGo (connection : Connection) : LiveState →
    List Statement → List Core.Result →
      IO (LiveState × Except String (List Core.Result))
  | live, [], reversed => pure (live, .ok reversed.reverse)
  | live, statement :: statements, reversed => do
      if requiresWriteAccess live.state statement then
        CoreFileAdapter.requireWritableAccess connection.paths.main
        CoreFileAdapter.requireWritableFormat connection.paths.main
      let (cached, execution) ← executeStatement connection live statement
      match execution with
      | .error message => pure (cached, .error message)
      | .ok (executed, results) => do
          let advanced ← if requiresPersistence live.state statement &&
              !dataWriteNoop live.state executed.state statement results then
            let persisted ← persistIfNeeded connection live.state
              executed.state statement
            pure (executed.retarget persisted)
          else
            -- Read-only statements already return a `LiveState` whose
            -- dependent certificates name their unchanged database.  Keep it
            -- verbatim: retargeting here would re-compare every logical index
            -- entry after every SELECT, turning a routed lookup back into an
            -- O(table) operation.
            pure executed
          runStatementsGo connection advanced statements
            (results.foldl (fun acc result => result :: acc) reversed)

/-- Stack-safe execution of a statement batch.  `runStatementsGo` accumulates
results in reverse order, so it does no work after its recursive IO call. -/
private def runStatements (connection : Connection) (live : LiveState)
    (statements : List Statement) :
    IO (LiveState × Except String (List Core.Result)) :=
  runStatementsGo connection live statements []

/-- Admit and execute one source statement at a time. A later parse error
returns the live state after the completed prefix, including an open transaction. -/
private def runChunks (connection : Connection) : LiveState → List String →
    List Core.Result → IO (LiveState × Except String (List Core.Result))
  | live, [], reversed => pure (live, .ok reversed.reverse)
  | live, chunk :: chunks, reversed => do
      match CoreTokenGrammar.parseStatements chunk with
      | .error message => pure (live, .error message)
      | .ok statements =>
          let (next, result) ← runStatements connection live statements.toList
          match result with
          | .error message => pure (next, .error message)
          | .ok results => runChunks connection next chunks (results.foldl (fun acc result => result :: acc) reversed)

def execute (connection : Connection) (sql : String) :
    IO (Except String (List Core.Result)) :=
  connection.state.atomically do
    let current ← get
    let (finalState, result) ← runChunks connection current (SQLite.Script.split sql) []
    set finalState
    return result

def snapshot (connection : Connection) : IO Core.State :=
  connection.state.atomically do return (← get).state

end CoreFileEngine
end SQLeanite
