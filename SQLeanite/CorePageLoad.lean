import SQLeanite.CoreChunkPageState
import SQLeanite.CoreDecode

namespace SQLeanite
namespace CorePageLoad

/-!
# Recovering the proof-carrying representation from physical pages

This loader accepts the binary 2-3-tree shape emitted by `CorePageCodec` and
also accepts compatible externally modified files.  Wider SQLite interior
pages return `none`; callers then retain the general decoder and bulk-commit
fallback.  Successful construction rechecks both the recursive tree invariant
and the exact abstraction equation in Lean before manufacturing any proof
field.
-/

/-- Decode SQLite's linked freelist trunks.  The saved count is fuel as well as
an exact accounting check, so cycles, duplicate over-counting, and truncated
trunks are rejected. Page numbers remain SQLite's one-based numbers. -/
def loadFreelist (source : CoreDecode.PageSource) :
    Nat → Nat → Nat → Option (List Nat)
  | _, 0, 0 => some []
  | _, 0, _ + 1 => none
  | 0, _ + 1, _ => none
  | fuel + 1, remaining + 1, trunk => do
      if _trunkValid : 1 < trunk ∧ trunk ≤ source.pageCount then
        let page ← source.readPage trunk
        let (next, afterNext) ← FileFormat.decodeUnsignedFixed 4 page
        let (leafCount, afterCount) ←
          FileFormat.decodeUnsignedFixed 4 afterNext
        if _countFits : leafCount ≤ remaining then
          let (leaves, _) ← FileFormat.decodeU32Values leafCount afterCount
          let leafNumbers := leaves.map (fun page => page.val)
          if _leavesValid : leafNumbers.all
              (fun page => decide (1 < page ∧ page ≤ source.pageCount)) then
            let rest := remaining - leafCount
            if _finished : rest = 0 then
              if _end : next = 0 then some (trunk :: leafNumbers) else none
            else
              if _continues : next = 0 then none
              else do
                let tail ← loadFreelist source fuel rest next
                some (trunk :: leafNumbers ++ tail)
          else none
        else none
      else none

def minimumKey? (node : PersistentPageTree.Node
    CoreChunkPageState.Chunk) : Option Nat :=
  node.erase.toList.head?.map (fun entry => entry.1)

def loadNode (schema : Core.Schema) (source : CoreDecode.PageSource) :
    Nat → Nat → Option (PersistentPageTree.Node CoreChunkPageState.Chunk)
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match CoreDecode.interiorChildren? page with
      | some [leftPage, rightPage] => do
          let left ← loadNode schema source fuel leftPage
          let right ← loadNode schema source fuel rightPage
          let separator ← minimumKey? right
          some (.branch2 pageNumber left separator right)
      | some [leftPage, middlePage, rightPage] => do
          let left ← loadNode schema source fuel leftPage
          let middle ← loadNode schema source fuel middlePage
          let right ← loadNode schema source fuel rightPage
          let firstSeparator ← minimumKey? middle
          let secondSeparator ← minimumKey? right
          some (.branch3 pageNumber left firstSeparator middle
            secondSeparator right)
      | some _ => none
      | none => do
          let rows ← CoreDecode.decodeRowsFrom schema source page
          match rows.getLast? with
          | none => some (.leaf pageNumber [])
          | some last => some (.leaf pageNumber [(last.treeKey, rows)])

/-- The persistent-tree loader and the logical row decoder traverse the same
physical pages and recover the same ordered row stream.  This prevents the
write-open capability from being a validation token detached from the public
decoder semantics. -/
theorem loadNode_decodes (schema : Core.Schema)
    (source : CoreDecode.PageSource) :
    ∀ {fuel pageNumber : Nat}
      {node : PersistentPageTree.Node CoreChunkPageState.Chunk},
      loadNode schema source fuel pageNumber = some node →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel pageNumber =
        some (CoreChunkPageState.Node.rows node)
  | 0, _, node, loaded => by simp [loadNode] at loaded
  | fuel + 1, pageNumber, node, loaded => by
      simp only [loadNode] at loaded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at loaded
      | some page =>
        simp only [pageResult, Option.bind_eq_bind, Option.bind] at loaded
        cases interiorResult : CoreDecode.interiorChildren? page with
        | none =>
          simp only [interiorResult] at loaded
          cases rowsResult : CoreDecode.decodeRowsFrom schema source page with
          | none => simp [rowsResult] at loaded
          | some rows =>
            simp only [rowsResult] at loaded
            cases lastResult : rows.getLast? with
            | none =>
              simp only [lastResult, Option.some.injEq] at loaded
              subst node
              have empty : rows = [] := List.getLast?_eq_none_iff.mp lastResult
              subst rows
              simp [CoreDecode.decodeSubtreeRowsFrom, pageResult,
                interiorResult, rowsResult, CoreChunkPageState.Node.rows,
                PersistentPageTree.Node.erase, RecursiveBPlusTree.Node.toList]
            | some last =>
              simp only [lastResult, Option.some.injEq] at loaded
              subst node
              simp [CoreDecode.decodeSubtreeRowsFrom, pageResult,
                interiorResult, rowsResult, CoreChunkPageState.Node.rows,
                PersistentPageTree.Node.erase, RecursiveBPlusTree.Node.toList]
        | some children =>
          simp only [interiorResult] at loaded
          match children with
          | [leftPage, rightPage] =>
              simp only [Option.bind_eq_bind, Option.bind] at loaded
              cases leftResult : loadNode schema source fuel leftPage with
              | none => simp [leftResult] at loaded
              | some left =>
                simp only [leftResult] at loaded
                cases rightResult : loadNode schema source fuel rightPage with
                | none => simp [rightResult] at loaded
                | some right =>
                  simp only [rightResult] at loaded
                  cases separatorResult : minimumKey? right with
                  | none => simp [separatorResult] at loaded
                  | some separator =>
                    simp only [separatorResult, Option.some.injEq] at loaded
                    subst node
                    have leftDecoded := loadNode_decodes schema source leftResult
                    have rightDecoded := loadNode_decodes schema source rightResult
                    simp [CoreDecode.decodeSubtreeRowsFrom, pageResult,
                      interiorResult, leftDecoded, rightDecoded,
                      CoreChunkPageState.Node.rows,
                      PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList]
          | [leftPage, middlePage, rightPage] =>
              simp only [Option.bind_eq_bind, Option.bind] at loaded
              cases leftResult : loadNode schema source fuel leftPage with
              | none => simp [leftResult] at loaded
              | some left =>
                simp only [leftResult] at loaded
                cases middleResult : loadNode schema source fuel middlePage with
                | none => simp [middleResult] at loaded
                | some middle =>
                  simp only [middleResult] at loaded
                  cases rightResult : loadNode schema source fuel rightPage with
                  | none => simp [rightResult] at loaded
                  | some right =>
                    simp only [rightResult] at loaded
                    cases firstResult : minimumKey? middle with
                    | none => simp [firstResult] at loaded
                    | some first =>
                      simp only [firstResult] at loaded
                      cases secondResult : minimumKey? right with
                      | none => simp [secondResult] at loaded
                      | some second =>
                        simp only [secondResult, Option.some.injEq] at loaded
                        subst node
                        have leftDecoded :=
                          loadNode_decodes schema source leftResult
                        have middleDecoded :=
                          loadNode_decodes schema source middleResult
                        have rightDecoded :=
                          loadNode_decodes schema source rightResult
                        simp [CoreDecode.decodeSubtreeRowsFrom, pageResult,
                          interiorResult, leftDecoded, middleDecoded,
                          rightDecoded, CoreChunkPageState.Node.rows,
                          PersistentPageTree.Node.erase,
                          RecursiveBPlusTree.Node.toList, List.append_assoc]
          | [] => simp at loaded
          | [_] => simp at loaded
          | _ :: _ :: _ :: _ :: _ => simp at loaded

def loadTable? (source : CoreDecode.PageSource) (rootPage : Nat)
    (table : Core.Table) : Option CoreChunkPageState.TableState := do
  let root ← loadNode table.schema source (source.pageCount + 1) rootPage
  if valid : root.erase.checkRootValid then
    let tree : PersistentPageTree.Store CoreChunkPageState.Chunk := {
      root
      nextPage := source.pageCount + 1
      rootValid := (RecursiveBPlusTree.Node.checkRootValid_iff root.erase).mp valid }
    if represents : CoreChunkPageState.Store.rows tree = table.rows then
      let capacity := CoreChunkPageState.legacyChunkCapacityFor
        table.schema table.rows
      some ⟨table, tree, represents, capacity,
        CoreChunkPageState.legacyChunkCapacityFor_pos table.schema table.rows⟩
    else none
  else none

theorem loadTable?_table {source : CoreDecode.PageSource} {rootPage : Nat}
    {table : Core.Table} {state : CoreChunkPageState.TableState}
    (loaded : loadTable? source rootPage table = some state) :
    state.table = table := by
  unfold loadTable? at loaded
  cases nodeResult : loadNode table.schema source (source.pageCount + 1)
      rootPage with
  | none => simp [nodeResult] at loaded
  | some root =>
      simp only [nodeResult, Option.bind_eq_bind, Option.bind] at loaded
      split at loaded
      next =>
        split at loaded
        next =>
          injection loaded with equal
          subst state
          rfl
        next => contradiction
      next => contradiction

def loadTableState? (source : CoreDecode.PageSource) (rootPage : Nat)
    (table : Core.Table) :
    Option { state : CoreChunkPageState.TableState // state.table = table } :=
  match result : loadTable? source rootPage table with
  | none => none
  | some state => some ⟨state, loadTable?_table result⟩

def rootPageFor? (catalog : List CoreDecode.CatalogEntry)
    (table : Core.Table) : Option Nat := do
  let entry ← catalog.find? fun entry =>
    entry.kind == "table" && entry.name == table.schema.name
  some entry.rootPage

def loadTables? (source : CoreDecode.PageSource)
    (catalog : List CoreDecode.CatalogEntry) :
    List Core.Table → Option (List CoreChunkPageState.TableState)
  | [] => some []
  | table :: tables => do
      let rootPage ← rootPageFor? catalog table
      let head ← loadTable? source rootPage table
      let tail ← loadTables? source catalog tables
      some (head :: tail)

theorem loadTables?_tables (source : CoreDecode.PageSource)
    (catalog : List CoreDecode.CatalogEntry) :
    ∀ (tables : List Core.Table) (states : List CoreChunkPageState.TableState),
      loadTables? source catalog tables = some states →
      states.map (fun state => state.table) = tables
  | [], states, loaded => by
      simp only [loadTables?, Option.some.injEq] at loaded
      subst states
      rfl
  | table :: tables, states, loaded => by
      simp only [loadTables?, Option.bind_eq_bind, Option.bind] at loaded
      cases rootResult : rootPageFor? catalog table with
      | none => simp [rootResult] at loaded
      | some rootPage =>
          simp only [rootResult] at loaded
          cases tableResult : loadTable? source rootPage table with
          | none => simp [tableResult] at loaded
          | some head =>
              simp only [tableResult] at loaded
              cases tailResult : loadTables? source catalog tables with
              | none => simp [tailResult] at loaded
              | some tail =>
                  simp only [tailResult, Option.some.injEq] at loaded
                  subst states
                  simp only [List.map_cons, List.cons.injEq]
                  exact ⟨loadTable?_table tableResult,
                    loadTables?_tables source catalog tables tail tailResult⟩

def loadTablesState? (source : CoreDecode.PageSource)
    (catalog : List CoreDecode.CatalogEntry) :
    (tables : List Core.Table) →
      Option { states : List CoreChunkPageState.TableState //
        states.map (fun state => state.table) = tables }
  | [] => some ⟨[], rfl⟩
  | table :: tables => do
      let rootPage ← rootPageFor? catalog table
      let head ← loadTableState? source rootPage table
      let tail ← loadTablesState? source catalog tables
      some ⟨head.val :: tail.val, by simp [head.property, tail.property]⟩

/-- Decode one catalog table directly into both its logical row tree and its
persistent physical page tree.  The older validating open decoded the same
row cells once for each representation. -/
def loadOpenTable? (source : CoreDecode.PageSource)
    (entry : CoreDecode.CatalogEntry) :
    Option CoreChunkPageState.TableState := do
  if _isTable : entry.kind = "table" then
    let sql ← entry.sql
    let schema ← CoreDecode.parseTableSchema sql
    if _nameMatches : schema.name = entry.name then
      let root ← loadNode schema source (source.pageCount + 1) entry.rootPage
      if valid : root.erase.checkRootValid then
        let tree : PersistentPageTree.Store CoreChunkPageState.Chunk := {
          root
          nextPage := source.pageCount + 1
          rootValid :=
            (RecursiveBPlusTree.Node.checkRootValid_iff root.erase).mp valid }
        match rebuilt : Core.Table.rebuildFromCatalog schema []
            (CoreChunkPageState.Store.rows tree) sql with
        | .error _ => none
        | .ok table =>
            some {
              table
              tree
              represents := (Core.Table.rebuildFromCatalog_exact rebuilt).2.2.symm
              capacity := CoreChunkPageState.legacyChunkCapacityFor
                table.schema table.rows
              capacity_pos := CoreChunkPageState.legacyChunkCapacityFor_pos
                table.schema table.rows }
      else none
    else none
  else none

theorem loadOpenTable?_exact
    {source : CoreDecode.PageSource} {entry : CoreDecode.CatalogEntry}
    {state : CoreChunkPageState.TableState}
    (loaded : loadOpenTable? source entry = some state) :
    CoreDecode.decodeTableFrom source entry = some state.table ∧
      state.table.withoutIndexes = state.table := by
  unfold loadOpenTable? at loaded
  split at loaded
  next isTable =>
    cases sqlResult : entry.sql with
    | none => simp [sqlResult] at loaded
    | some sql =>
      simp only [sqlResult, Option.bind_eq_bind, Option.bind] at loaded
      cases schemaResult : CoreDecode.parseTableSchema sql with
      | none => simp [schemaResult] at loaded
      | some schema =>
        simp only [schemaResult] at loaded
        split at loaded
        next nameMatches =>
          cases rootResult : loadNode schema source (source.pageCount + 1)
              entry.rootPage with
          | none => simp [rootResult] at loaded
          | some root =>
            simp only [rootResult] at loaded
            split at loaded
            next valid =>
              split at loaded
              next message rebuilt => contradiction
              next table rebuilt =>
                injection loaded with equal
                subst state
                have rebuilt' : Core.Table.rebuildFromCatalog schema []
                    (CoreChunkPageState.Node.rows root) sql = .ok table := by
                  simpa [CoreChunkPageState.Store.rows] using rebuilt
                constructor
                · unfold CoreDecode.decodeTableFrom
                  rw [dif_pos isTable, sqlResult]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [schemaResult]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [dif_pos nameMatches]
                  rw [loadNode_decodes schema source rootResult]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [rebuilt']
                  rfl
                · exact Core.Table.rebuildFromCatalog_withoutIndexes_fixed
                    rebuilt'
            next => contradiction
        next => contradiction
  next => contradiction

theorem loadOpenTable?_decode
    {source : CoreDecode.PageSource} {entry : CoreDecode.CatalogEntry}
    {state : CoreChunkPageState.TableState}
    (loaded : loadOpenTable? source entry = some state) :
    CoreDecode.decodeTableFrom source entry = some state.table :=
  (loadOpenTable?_exact loaded).1

theorem loadOpenTable?_withoutIndexes
    {source : CoreDecode.PageSource} {entry : CoreDecode.CatalogEntry}
    {state : CoreChunkPageState.TableState}
    (loaded : loadOpenTable? source entry = some state) :
    state.table.withoutIndexes = state.table :=
  (loadOpenTable?_exact loaded).2

def loadOpenTables? (source : CoreDecode.PageSource) :
    List CoreDecode.CatalogEntry →
      Option (List CoreChunkPageState.TableState)
  | [] => some []
  | entry :: entries => do
      let head ← loadOpenTable? source entry
      let tail ← loadOpenTables? source entries
      some (head :: tail)

theorem loadOpenTables?_decode (source : CoreDecode.PageSource) :
    ∀ {entries : List CoreDecode.CatalogEntry}
      {states : List CoreChunkPageState.TableState},
      loadOpenTables? source entries = some states →
      entries.mapM (CoreDecode.decodeTableFrom source) =
        some (states.map (fun state => state.table))
  | [], states, loaded => by
      simp only [loadOpenTables?, Option.some.injEq] at loaded
      subst states
      rfl
  | entry :: entries, states, loaded => by
      simp only [loadOpenTables?, Option.bind_eq_bind, Option.bind] at loaded
      cases headResult : loadOpenTable? source entry with
      | none => simp [headResult] at loaded
      | some head =>
        simp only [headResult] at loaded
        cases tailResult : loadOpenTables? source entries with
        | none => simp [tailResult] at loaded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at loaded
          subst states
          simp only [List.mapM_cons, loadOpenTable?_decode headResult,
            Option.bind_eq_bind, Option.bind, loadOpenTables?_decode source
              tailResult, List.map_cons]
          rfl

theorem loadOpenTables?_withoutIndexes
    (source : CoreDecode.PageSource) :
    ∀ {entries : List CoreDecode.CatalogEntry}
      {states : List CoreChunkPageState.TableState},
      loadOpenTables? source entries = some states →
      states.map (fun state => state.table.withoutIndexes) =
        states.map (fun state => state.table)
  | [], states, loaded => by
      simp only [loadOpenTables?, Option.some.injEq] at loaded
      subst states
      rfl
  | entry :: entries, states, loaded => by
      simp only [loadOpenTables?, Option.bind_eq_bind, Option.bind] at loaded
      cases headResult : loadOpenTable? source entry with
      | none => simp [headResult] at loaded
      | some head =>
        simp only [headResult] at loaded
        cases tailResult : loadOpenTables? source entries with
        | none => simp [tailResult] at loaded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at loaded
          subst states
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨loadOpenTable?_withoutIndexes headResult,
            loadOpenTables?_withoutIndexes source tailResult⟩

/-- Reattach index metadata after its physical trees have been checked.  The
dependent result pins the state list to the final database order. -/
def retargetOpenTables? : List CoreChunkPageState.TableState →
    (tables : List Core.Table) →
    Option { states : List CoreChunkPageState.TableState //
      states.map (fun state => state.table) = tables }
  | [], [] => some ⟨[], rfl⟩
  | state :: states, table :: tables => do
      if equivalent : CoreChunkPageState.TableState.DataEquiv
          state.table table then
        let tail ← retargetOpenTables? states tables
        let head := state.retargetData table equivalent
        some ⟨head :: tail.val, by simp [head, tail.property]⟩
      else none
  | _, _ => none

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
                  rw [firstResult]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [catalogResult]
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
