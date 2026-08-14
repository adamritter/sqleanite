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

def loadTable? (source : CoreDecode.PageSource) (rootPage : Nat)
    (table : Core.Table) : Option CoreChunkPageState.TableState := do
  let root ← loadNode table.schema source (source.pageCount + 1) rootPage
  if valid : root.erase.checkRootValid then
    let tree : PersistentPageTree.Store CoreChunkPageState.Chunk := {
      root
      nextPage := source.pageCount + 1
      rootValid := (RecursiveBPlusTree.Node.checkRootValid_iff root.erase).mp valid }
    if represents : CoreChunkPageState.Store.rows tree = table.rows then
      some ⟨table, tree, represents⟩
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
        match rebuilt : Core.Table.rebuild schema []
            (CoreChunkPageState.Store.rows tree) with
        | .error _ => none
        | .ok table =>
            some {
              table
              tree
              represents := (Core.Table.rebuild_exact rebuilt).2.2.symm }
      else none
    else none
  else none

def loadOpenTables? (source : CoreDecode.PageSource) :
    List CoreDecode.CatalogEntry →
      Option (List CoreChunkPageState.TableState)
  | [] => some []
  | entry :: entries => do
      let head ← loadOpenTable? source entry
      let tail ← loadOpenTables? source entries
      some (head :: tail)

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
