import SQLeanite.CoreWidePageCodec

namespace SQLeanite
namespace CoreWidePageLoad

/-!
# Validating loader for high-fanout table pages

The general decoder establishes the logical database.  This loader recovers
the page identities and wide topology from the same byte source, then admits
the result only when its ordered abstraction is exactly the decoded table.
Unlike the former loader it accepts every nonempty interior child list, not
only binary and ternary pages.
-/

def loadNode (schema : Core.Schema) (capacity : Nat)
    (source : CoreDecode.PageSource) :
    Nat → Nat → Option (WidePageTree.Node CoreWidePageState.Chunk)
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match CoreDecode.interiorChildren? page with
      | some [] => none
      | some children => do
          let nodes ← children.mapM (loadNode schema capacity source fuel)
          some (.branch pageNumber nodes)
      | none => do
          let rows ← CoreDecode.decodeRowsFrom schema source page
          let rowChunks := CoreChunkPageState.chunks capacity rows
          let entries ← CoreChunkPageState.entries? rowChunks
          some (.leaf pageNumber entries)

private def decodeChildRows (schema : Core.Schema)
    (source : CoreDecode.PageSource) (fuel : Nat)
    (rows : List Core.Row) (pageNumber : Nat) : Option (List Core.Row) := do
  let childRows ← CoreDecode.decodeSubtreeRowsFrom schema source fuel
    pageNumber
  some (rows ++ childRows)

private theorem loadChildren_decodes (schema : Core.Schema) (capacity : Nat)
    (source : CoreDecode.PageSource) (fuel : Nat)
    (childExact : ∀ {pageNumber : Nat}
      {node : WidePageTree.Node CoreWidePageState.Chunk},
      loadNode schema capacity source fuel pageNumber = some node →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel pageNumber =
        some (CoreWidePageState.Node.rows node)) :
    ∀ (pages : List Nat)
      (nodes : List (WidePageTree.Node CoreWidePageState.Chunk))
      (accumulator : List Core.Row),
      pages.mapM (loadNode schema capacity source fuel) = some nodes →
      pages.foldlM (decodeChildRows schema source fuel) accumulator =
        some (accumulator ++ nodes.flatMap CoreWidePageState.Node.rows)
  | [], nodes, accumulator, loaded => by
      change some [] = some nodes at loaded
      injection loaded with equal
      subst nodes
      simp
  | page :: pages, nodes, accumulator, loaded => by
      simp only [List.mapM_cons] at loaded
      cases headResult : loadNode schema capacity source fuel page with
      | none => simp [headResult] at loaded
      | some node =>
          simp only [headResult, Option.bind_eq_bind, Option.bind] at loaded
          cases tailResult : pages.mapM
              (loadNode schema capacity source fuel) with
          | none => simp [tailResult] at loaded
          | some tail =>
              rw [tailResult] at loaded
              change some (node :: tail) = some nodes at loaded
              injection loaded with equal
              subst nodes
              simp only [List.foldlM_cons, childExact headResult,
                Option.bind_eq_bind, Option.bind, decodeChildRows]
              rw [loadChildren_decodes schema capacity source fuel childExact
                pages tail (accumulator ++ CoreWidePageState.Node.rows node)
                tailResult]
              simp [List.append_assoc]

/-- The validating topology loader and the public logical decoder traverse the
same pages and recover the same row stream for arbitrary interior fanout. -/
theorem loadNode_decodes (schema : Core.Schema) (capacity : Nat)
    (source : CoreDecode.PageSource) :
    ∀ {fuel pageNumber : Nat}
      {node : WidePageTree.Node CoreWidePageState.Chunk},
      loadNode schema capacity source fuel pageNumber = some node →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel pageNumber =
        some (CoreWidePageState.Node.rows node) := by
  intro fuel
  induction fuel with
  | zero =>
      intro pageNumber node loaded
      simp [loadNode] at loaded
  | succ fuel induction =>
      intro pageNumber node loaded
      simp only [loadNode] at loaded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at loaded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at loaded
          cases interiorResult : CoreDecode.interiorChildren? page with
          | none =>
              simp only [interiorResult] at loaded
              rcases Option.bind_eq_some.mp loaded with
                ⟨rows, rowsResult, loaded⟩
              rcases Option.bind_eq_some.mp loaded with
                ⟨entries, entriesResult, loaded⟩
              simp only [Option.some.injEq] at loaded
              subst node
              unfold CoreDecode.decodeSubtreeRowsFrom
              rw [pageResult]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [interiorResult, rowsResult]
              simp only [CoreWidePageState.Node.rows,
                WidePageTree.Node.toList]
              rw [List.flatMap_def,
                (CoreChunkPageState.entries?_projections entriesResult).1,
                CoreChunkPageState.flatten_chunks]
          | some children =>
              simp only [interiorResult] at loaded
              cases children with
              | nil => simp at loaded
              | cons child children =>
                  rcases Option.bind_eq_some.mp loaded with
                    ⟨nodes, nodesResult, loaded⟩
                  simp only [Option.some.injEq] at loaded
                  subst node
                  unfold CoreDecode.decodeSubtreeRowsFrom
                  rw [pageResult]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [interiorResult]
                  change (child :: children).foldlM
                    (decodeChildRows schema source fuel) [] = _
                  rw [loadChildren_decodes schema capacity source fuel induction
                    (child :: children) nodes [] nodesResult]
                  simp [CoreWidePageState.Node.rows, WidePageTree.Node.toList,
                    List.flatMap_assoc]
                  rfl

def loadTable? (source : CoreDecode.PageSource) (rootPage : Nat)
    (table : Core.Table) : Option CoreWidePageState.TableState := do
  let capacity := CoreChunkPageState.chunkCapacityFor table.rows
  let root ← loadNode table.schema capacity source
    (source.pageCount + 1) rootPage
  match WidePageTree.decideKeysPairwise root.toList with
  | isFalse _ => none
  | isTrue ordered =>
      let tree : WidePageTree.Store CoreWidePageState.Chunk := {
        root
        nextPage := source.pageCount + 1
        represents := ordered }
      if represents : CoreWidePageState.Store.rows tree = table.rows then
        some {
          table
          tree
          represents
          capacity
          capacity_pos := CoreChunkPageState.chunkCapacityFor_pos table.rows }
      else none

theorem loadTable?_table {source : CoreDecode.PageSource} {rootPage : Nat}
    {table : Core.Table} {state : CoreWidePageState.TableState}
    (loaded : loadTable? source rootPage table = some state) :
    state.table = table := by
  unfold loadTable? at loaded
  rcases Option.bind_eq_some.mp loaded with ⟨root, rootResult, loaded⟩
  dsimp only at loaded
  cases orderResult : WidePageTree.decideKeysPairwise root.toList with
  | isFalse rejected => simp [orderResult] at loaded
  | isTrue ordered =>
      simp only [orderResult] at loaded
      split at loaded
      next =>
        injection loaded with equal
        subst state
        rfl
      next => contradiction

theorem loadTable?_represents {source : CoreDecode.PageSource} {rootPage : Nat}
    {table : Core.Table} {state : CoreWidePageState.TableState}
    (loaded : loadTable? source rootPage table = some state) :
    CoreWidePageState.Store.rows state.tree = table.rows := by
  rw [state.represents, loadTable?_table loaded]

theorem loadTable?_decodes {source : CoreDecode.PageSource} {rootPage : Nat}
    {table : Core.Table} {state : CoreWidePageState.TableState}
    (loaded : loadTable? source rootPage table = some state) :
    CoreDecode.decodeSubtreeRowsFrom table.schema source
      (source.pageCount + 1) rootPage = some table.rows := by
  unfold loadTable? at loaded
  rcases Option.bind_eq_some.mp loaded with ⟨root, rootResult, loaded⟩
  dsimp only at loaded
  cases orderResult : WidePageTree.decideKeysPairwise root.toList with
  | isFalse rejected => simp [orderResult] at loaded
  | isTrue ordered =>
      simp only [orderResult] at loaded
      split at loaded
      next represents =>
        have decoded := loadNode_decodes table.schema
          (CoreChunkPageState.chunkCapacityFor table.rows) source rootResult
        rw [show CoreWidePageState.Node.rows root = table.rows by
          simp [CoreWidePageState.Store.rows] at represents
          exact represents] at decoded
        exact decoded
      next => contradiction

structure LoadedTables (target : List Core.Table) where
  tables : List CoreWidePageState.TableState
  aligned : tables.map (fun state => state.table) = target

def loadTables? (source : CoreDecode.PageSource)
    (catalog : List CoreDecode.CatalogEntry) :
    (tables : List Core.Table) → Option (LoadedTables tables)
  | [] => some ⟨[], rfl⟩
  | table :: tables =>
      match catalogResult : catalog.find? (fun entry =>
          entry.kind == "table" && entry.name == table.schema.name) with
      | none => none
      | some entry =>
          match headResult : loadTable? source entry.rootPage table with
          | none => none
          | some head =>
              match loadTables? source catalog tables with
              | none => none
              | some tail => some ⟨head :: tail.tables, by
                  simp only [List.map_cons, List.cons.injEq]
                  exact ⟨loadTable?_table headResult, tail.aligned⟩⟩

def load? (source : CoreDecode.PageSource) (database : Core.Database) :
    Option CoreWidePageState.State := do
  let firstPage ← source.readPage 1
  let catalog ← CoreDecode.decodeCatalogForOpen firstPage
  let loaded ← loadTables? source catalog database.tables
  some {
    database
    tables := loaded.tables
    tables_eq := loaded.aligned
    nextPage := source.pageCount + 1 }

theorem load?_represents {source : CoreDecode.PageSource}
    {database : Core.Database} {state : CoreWidePageState.State}
    (loaded : load? source database = some state) :
    state.Represents database := by
  unfold load? at loaded
  rcases Option.bind_eq_some.mp loaded with
    ⟨firstPage, firstPageResult, loaded⟩
  rcases Option.bind_eq_some.mp loaded with ⟨catalog, catalogResult, loaded⟩
  rcases Option.bind_eq_some.mp loaded with ⟨tables, tablesResult, loaded⟩
  simp only [Option.some.injEq] at loaded
  subst state
  refine ⟨rfl, tables.aligned, ?_⟩
  intro table member
  exact table.represents

end CoreWidePageLoad
end SQLeanite
