import SQLeanite.CoreChunkPageState.TableStateBuildTable
import SQLeanite.CoreDecode.ValidateCanonicalIndexGroupsFromEncodeOverflowIndexTableGroups
import SQLeanite.CorePageLoad.LoadFreelist

namespace SQLeanite
namespace CorePageLoad

theorem retargetOpenTables?_withoutIndexes :
    ∀ {initial : List CoreChunkPageState.TableState}
      {tables : List Core.Table}
      {result : { states : List CoreChunkPageState.TableState //
        states.map (fun state => state.table) = tables }},
      retargetOpenTables? initial tables = some result →
      result.val.map (fun state => state.table.withoutIndexes) =
        initial.map (fun state => state.table.withoutIndexes)
  | [], [], result, retargeted => by
      simp only [retargetOpenTables?, Option.some.injEq] at retargeted
      subst result
      rfl
  | initial :: initials, table :: tables, result, retargeted => by
      simp only [retargetOpenTables?] at retargeted
      split at retargeted
      next equivalent =>
        simp only [Option.bind_eq_bind, Option.bind] at retargeted
        cases tailResult : retargetOpenTables? initials tables with
        | none => simp [tailResult] at retargeted
        | some tail =>
          simp only [tailResult, Option.some.injEq] at retargeted
          subst result
          simp only [List.map_cons,
            CoreChunkPageState.TableState.retargetData_table,
            List.cons.injEq]
          exact ⟨equivalent.withoutIndexes_eq.symm,
            retargetOpenTables?_withoutIndexes tailResult⟩
      next => contradiction
  | [], _ :: _, result, retargeted => by simp [retargetOpenTables?] at retargeted
  | _ :: _, [], result, retargeted => by simp [retargetOpenTables?] at retargeted

/-- One-pass validating open for the physical 2-3-tree representation.
Logical tables and persistent page identities come from the same decoded
nodes; indexes and freelist state remain independently checked. -/
def open? (source : CoreDecode.PageSource) :
    Option CoreChunkPageState.State := do
  let firstPage ← source.readPage 1
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPage
  let catalog ← CoreDecode.decodeCatalogForOpen firstPage
  let tableEntries := catalog.filter (fun entry => entry.kind == "table")
  let indexEntries := catalog.filter (fun entry => entry.kind == "index")
  let initialStates ← loadOpenTables? source tableEntries
  let base ← (Core.Database.rebuild
    (initialStates.map (fun state => state.table))).toOption
  let database ← CoreDecode.applyIndexesForOpen source base indexEntries
  let states ← retargetOpenTables? initialStates database.tables
  let freePages ← loadFreelist source (source.pageCount + 1)
    header.freelistPageCount.val header.firstFreelistTrunk.val
  some {
    database
    tables := states.val
    tables_eq := states.property
    nextPage := source.pageCount + 1
    freePages }

/-- A successful validating open is not merely a well-typed in-memory tree:
the public logical page decoder returns the exact same database. -/
theorem open?_decode {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.State}
    (opened : open? source = some state) :
    CoreDecode.decodeFromPageSource source = some state.database := by
  unfold open? at opened
  cases firstResult : source.readPage 1 with
  | none => simp [firstResult] at opened
  | some firstPage =>
    simp only [firstResult, Option.bind_eq_bind, Option.bind] at opened
    cases headerResult : FileFormat.decodeDatabaseHeader firstPage with
    | none => simp [headerResult] at opened
    | some headerAndSuffix =>
      rcases headerAndSuffix with ⟨header, headerSuffix⟩
      simp only [headerResult] at opened
      cases catalogResult : CoreDecode.decodeCatalogForOpen firstPage with
      | none => simp [catalogResult] at opened
      | some catalog =>
        simp only [catalogResult] at opened
        let tableEntries := catalog.filter (fun entry => entry.kind == "table")
        let indexEntries := catalog.filter (fun entry => entry.kind == "index")
        cases tablesResult : loadOpenTables? source tableEntries with
        | none => simp [tableEntries, tablesResult] at opened
        | some initialStates =>
          simp only [tableEntries, tablesResult] at opened
          cases baseResult : (Core.Database.rebuild
              (initialStates.map (fun state => state.table))).toOption with
          | none => simp [baseResult] at opened
          | some base =>
            simp only [baseResult] at opened
            cases databaseResult : CoreDecode.applyIndexesForOpen source base
                indexEntries with
            | none => simp [indexEntries, databaseResult] at opened
            | some database =>
              simp only [indexEntries, databaseResult] at opened
              cases statesResult : retargetOpenTables? initialStates
                  database.tables with
              | none => simp [statesResult] at opened
              | some states =>
                simp only [statesResult] at opened
                cases freeResult : loadFreelist source (source.pageCount + 1)
                    header.freelistPageCount.val
                    header.firstFreelistTrunk.val with
                | none => simp [freeResult] at opened
                | some freePages =>
                  simp only [freeResult, Option.some.injEq] at opened
                  subst state
                  unfold CoreDecode.decodeFromPageSource
                  have catalogRead : source.readPage 1 >>= CoreDecode.decodeCatalogForOpen = some catalog := by
                    rw [firstResult]
                    simp only [Option.bind_eq_bind,Option.bind]
                    exact catalogResult
                  rw [CoreDecode.catalogFromPageSource_shallow source catalog catalogRead]
                  simp only [Option.bind_eq_bind, Option.bind]
                  change (do
                    let tables ← tableEntries.mapM
                      (CoreDecode.decodeTableFrom source)
                    let rebuilt ← (Core.Database.rebuild tables).toOption
                    CoreDecode.applyIndexesForOpen source rebuilt
                      indexEntries) = some database
                  rw [loadOpenTables?_decode source tablesResult]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [baseResult]
                  exact databaseResult

/-- The validating loader exposes the same catalog/table/index equations used
by the executable decoder.  This is the initial component certificate that a
localized writer can preserve one table and index run at a time. -/
theorem open?_pageSourceDecodes {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.State}
    (opened : open? source = some state) :
    CoreDecode.PageSourceDecodes source state.database := by
  unfold open? at opened
  cases firstResult : source.readPage 1 with
  | none => simp [firstResult] at opened
  | some firstPage =>
    simp only [firstResult, Option.bind_eq_bind, Option.bind] at opened
    cases headerResult : FileFormat.decodeDatabaseHeader firstPage with
    | none => simp [headerResult] at opened
    | some headerAndSuffix =>
      rcases headerAndSuffix with ⟨header, headerSuffix⟩
      simp only [headerResult] at opened
      cases catalogResult : CoreDecode.decodeCatalogForOpen firstPage with
      | none => simp [catalogResult] at opened
      | some catalog =>
        simp only [catalogResult] at opened
        let tableEntries := catalog.filter (fun entry => entry.kind == "table")
        let indexEntries := catalog.filter (fun entry => entry.kind == "index")
        cases tablesResult : loadOpenTables? source tableEntries with
        | none => simp [tableEntries, tablesResult] at opened
        | some initialStates =>
          simp only [tableEntries, tablesResult] at opened
          cases baseResult : (Core.Database.rebuild
              (initialStates.map (fun state => state.table))).toOption with
          | none => simp [baseResult] at opened
          | some base =>
            simp only [baseResult] at opened
            cases databaseResult : CoreDecode.applyIndexesForOpen source base
                indexEntries with
            | none => simp [indexEntries, databaseResult] at opened
            | some database =>
              simp only [indexEntries, databaseResult] at opened
              cases statesResult : retargetOpenTables? initialStates
                  database.tables with
              | none => simp [statesResult] at opened
              | some states =>
                simp only [statesResult] at opened
                cases freeResult : loadFreelist source (source.pageCount + 1)
                    header.freelistPageCount.val
                    header.firstFreelistTrunk.val with
                | none => simp [freeResult] at opened
                | some freePages =>
                  simp only [freeResult, Option.some.injEq] at opened
                  subst state
                  have decodedTables := loadOpenTables?_decode source tablesResult
                  have initialWithout :=
                    loadOpenTables?_withoutIndexes source tablesResult
                  have retargetedWithout :=
                    retargetOpenTables?_withoutIndexes statesResult
                  have targetTables :
                      database.tables.map Core.Table.withoutIndexes =
                        initialStates.map (fun state => state.table) := by
                    calc
                      database.tables.map Core.Table.withoutIndexes =
                          (states.val.map (fun state => state.table)).map
                            Core.Table.withoutIndexes :=
                        congrArg (List.map Core.Table.withoutIndexes)
                          states.property.symm
                      _ =
                          states.val.map
                            (fun state => state.table.withoutIndexes) := by
                        rw [List.map_map]
                        rfl
                      _ = initialStates.map
                          (fun state => state.table.withoutIndexes) :=
                        retargetedWithout
                      _ = initialStates.map (fun state => state.table) :=
                        initialWithout
                  have baseTables : base.tables =
                      initialStates.map (fun state => state.table) := by
                    unfold Except.toOption at baseResult
                    split at baseResult
                    next value rebuilt =>
                      injection baseResult with equal
                      subst base
                      exact Core.Database.rebuild_tables rebuilt
                    next => contradiction
                  have baseExact : base = database.withoutIndexes := by
                    cases base with
                    | mk baseTableList baseWellFormed =>
                      cases database with
                      | mk databaseTableList databaseWellFormed =>
                        simp only [Core.Database.withoutIndexes]
                          at targetTables ⊢
                        simp only at baseTables
                        have tablesEqual : baseTableList =
                            databaseTableList.map Core.Table.withoutIndexes :=
                          baseTables.trans targetTables.symm
                        cases tablesEqual
                        rfl
                  exact .intro catalog (by
                    simp only [firstResult, Option.bind_eq_bind, Option.bind]
                    exact catalogResult) (by
                    change tableEntries.mapM
                        (CoreDecode.decodeTableFrom source) = _
                    rw [targetTables]
                    exact decodedTables) (by
                    change CoreDecode.applyIndexesForOpen source
                        database.withoutIndexes indexEntries = _
                    rw [← baseExact]
                    exact databaseResult)

theorem open?_pageSourceRepresents {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.State}
    (opened : open? source = some state)
    (fixed : state.database.canonicalize = state.database) :
    CoreDecode.PageSourceRepresents source state.database :=
  (open?_pageSourceDecodes opened).represents fixed

theorem open?_represents {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.State}
    (_opened : open? source = some state) :
    state.Represents state.database :=
  state.represents_self

/-- Fast validating open for a Lean-generated image.  The generated stamp is
invalidated by an ordinary SQLite writer. While it is present, the encoder
refinement and localized-commit certificates establish the physical index
contents, so reopening needs only reconstruct canonical index metadata from
the catalog; table rows and their persistent page identities are still decoded
and checked in full. -/
def openGenerated? (source : CoreDecode.PageSource) :
    Option CoreChunkPageState.State := do
  let firstPage ← source.readPage 1
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPage
  if _generated : CoreFile.hasGeneratedImageStamp header then
    let catalog ← CoreDecode.decodeCatalogForOpen firstPage
    let tableEntries := catalog.filter (fun entry => entry.kind == "table")
    let indexEntries := catalog.filter (fun entry => entry.kind == "index")
    let initialStates ← loadOpenTables? source tableEntries
    let base ← (Core.Database.rebuild
      (initialStates.map (fun state => state.table))).toOption
    let database ← CoreDecode.rebuildCanonicalDatabase base.tables indexEntries
    let states ← retargetOpenTables? initialStates database.tables
    let freePages ← loadFreelist source (source.pageCount + 1)
      header.freelistPageCount.val header.firstFreelistTrunk.val
    some {
      database
      tables := states.val
      tables_eq := states.property
      nextPage := source.pageCount + 1
      freePages }
  else none

theorem openGenerated?_represents {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.State}
    (_opened : openGenerated? source = some state) :
    state.Represents state.database :=
  state.represents_self

def load? (source : CoreDecode.PageSource) (database : Core.Database) :
    Option CoreChunkPageState.State := do
  let firstPage ← source.readPage 1
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPage
  let catalog ← CoreDecode.decodeCatalog firstPage
  let tables ← loadTablesState? source catalog database.tables
  let freePages ← loadFreelist source (source.pageCount + 1)
    header.freelistPageCount.val header.firstFreelistTrunk.val
  some {
    database
    tables := tables.val
    tables_eq := tables.property
    nextPage := source.pageCount + 1
    freePages }

theorem load?_represents {source : CoreDecode.PageSource}
    {database : Core.Database} {state : CoreChunkPageState.State}
    (loaded : load? source database = some state) :
    state.tables.map (fun table => table.table) = database.tables := by
  have databaseEqual : state.database = database := by
    unfold load? at loaded
    cases firstResult : source.readPage 1 with
    | none => simp [firstResult] at loaded
    | some firstPage =>
        simp only [firstResult, Option.bind_eq_bind, Option.bind] at loaded
        cases headerResult : FileFormat.decodeDatabaseHeader firstPage with
        | none => simp [headerResult] at loaded
        | some header =>
            simp only [headerResult] at loaded
            cases catalogResult : CoreDecode.decodeCatalog firstPage with
            | none => simp [catalogResult] at loaded
            | some catalog =>
                simp only [catalogResult] at loaded
                cases tablesResult : loadTablesState? source catalog database.tables with
                | none => simp [tablesResult] at loaded
                | some tables =>
                    simp only [tablesResult] at loaded
                    cases freeResult : loadFreelist source (source.pageCount + 1)
                        header.1.freelistPageCount.val
                        header.1.firstFreelistTrunk.val with
                    | none => simp [freeResult] at loaded
                    | some freePages =>
                        simp only [freeResult, Option.some.injEq] at loaded
                        subst state
                        rfl
  rw [state.tables_eq, databaseEqual]

end CorePageLoad

end SQLeanite
