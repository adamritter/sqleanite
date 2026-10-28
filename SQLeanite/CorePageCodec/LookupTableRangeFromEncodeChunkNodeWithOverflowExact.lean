import SQLeanite.CoreDecode.LookupTableRangeIOFrom
import SQLeanite.CorePageCodec.DecodeAbstractTableTreeFromEncodeChunkNodeWithOverflow
import SQLeanite.CorePageCodec.DecodeSubtreeRowsFromEncodeChunkNodeWithOverflow

namespace SQLeanite
namespace CorePageCodec

/-- End-to-end exactness of generated primary-key range traversal.  This is
the theorem used to justify bypassing whole-database materialisation on the
stamped cold-read path. -/
theorem lookupTableRangeFrom_encodeChunkNodeWithOverflow_exact
    (schema : Core.Schema) (source : CoreDecode.PageSource)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (nextOverflow : Nat) (encoding : OverflowEncoding) (fuel : Nat)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (encoded : encodeChunkNodeWithOverflow schema node nextOverflow =
      some encoding)
    (treeContains : PageSourceContains source encoding.treePages)
    (overflowContains : CoreDecode.ReadsPagesFrom source nextOverflow
      encoding.overflowPages)
    (rootValid : node.erase.RootValid)
    (valid : ∀ entry ∈ node.erase.toList, ∀ row ∈ entry.2,
      row.WellFormed schema)
    (positive : ∀ pageId ∈ node.pageIds, 0 < pageId)
    (ordered : (CoreChunkPageState.Node.rows node).Pairwise Core.Row.keyLess)
    (enough : node.erase.height < fuel)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length < source.pageCount + 1) :
    CoreDecode.lookupTableRangeFrom schema source operation target fuel
        node.rootId =
      some ((CoreChunkPageState.Node.rows node).filter
        (CoreDecode.tableRowMatchesRange operation target)) := by
  rcases decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema source
      node nextOverflow encoding fuel encoded treeContains overflowContains
      rootValid valid positive ordered enough nextPositive pageBound fuelBound with
    ⟨tree, decoded, contents, routed⟩
  rw [CoreDecode.lookupTableRangeFrom_decodeAbstract_exact schema source
    operation target fuel node.rootId tree decoded routed, contents]

theorem encodeChunkTablesWithOverflow_pageNumbers :
    ∀ (nextOverflow : Nat) (tables : List CoreChunkPageState.TableState)
      (encoding : OverflowEncoding),
      encodeChunkTablesWithOverflow nextOverflow tables = some encoding →
      encoding.treePages.map NumberedPage.pageNumber =
        CoreChunkPageState.tablePageIds tables
  | _, [], encoding, encoded => by
      simp only [encodeChunkTablesWithOverflow, Option.some.injEq] at encoded
      subst encoding
      rfl
  | nextOverflow, table :: tables, encoding, encoded => by
      simp only [encodeChunkTablesWithOverflow, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeChunkNodeWithOverflow table.table.schema
          table.tree.root nextOverflow with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeChunkTablesWithOverflow head.nextPage tables with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encoding
              simp only [List.map_append, CoreChunkPageState.tablePageIds,
                List.flatMap_cons]
              rw [encodeChunkNodeWithOverflow_pageNumbers table.table.schema
                table.tree.root nextOverflow head headResult,
                encodeChunkTablesWithOverflow_pageNumbers head.nextPage tables
                  tail tailResult]
              rfl

theorem encodeChunkTablesWithOverflow_nextPage :
    ∀ (nextOverflow : Nat) (tables : List CoreChunkPageState.TableState)
      (encoding : OverflowEncoding),
      encodeChunkTablesWithOverflow nextOverflow tables = some encoding →
      encoding.nextPage = nextOverflow + encoding.overflowPages.length
  | _, [], encoding, encoded => by
      simp only [encodeChunkTablesWithOverflow, Option.some.injEq] at encoded
      subst encoding
      simp
  | nextOverflow, table :: tables, encoding, encoded => by
      simp only [encodeChunkTablesWithOverflow, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeChunkNodeWithOverflow table.table.schema
          table.tree.root nextOverflow with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeChunkTablesWithOverflow head.nextPage tables with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encoding
              simp only [List.length_append]
              rw [encodeChunkTablesWithOverflow_nextPage head.nextPage tables
                tail tailResult,
                encodeChunkNodeWithOverflow_nextPage table.table.schema
                  table.tree.root nextOverflow head headResult]
              omega

theorem encodeChunkTables_pageNumbers :
    ∀ (tables : List CoreChunkPageState.TableState)
      (pages : List NumberedPage),
      encodeChunkTables tables = some pages →
      pages.map NumberedPage.pageNumber =
        CoreChunkPageState.tablePageIds tables
  | [], pages, encoded => by
      simp only [encodeChunkTables, Option.some.injEq] at encoded
      subst pages
      rfl
  | table :: tables, pages, encoded => by
      simp only [encodeChunkTables, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeChunkTable table with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeChunkTables tables with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst pages
              simp only [List.map_append, CoreChunkPageState.tablePageIds,
                List.flatMap_cons]
              rw [show head.map NumberedPage.pageNumber = table.pageIds by
                exact encodeChunkNode_pageNumbers table.table.schema
                  table.tree.root head headResult]
              rw [encodeChunkTables_pageNumbers tables tail tailResult]
              rfl

def chunkTableCatalogEntry (state : CoreChunkPageState.TableState) :
    CoreFile.CatalogEntry := {
  kind := "table"
  name := state.table.schema.name
  table := state.table.schema.name
  rootPage := state.rootPage
  sql := CoreFile.tableSQL state.table }

theorem decodeTableFrom_encodeChunkNodeWithOverflow
    (source : CoreDecode.PageSource) (state : CoreChunkPageState.TableState)
    (nextOverflow : Nat) (encoding : OverflowEncoding)
    (encoded : encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (treeContains : PageSourceContains source encoding.treePages)
    (overflowContains : CoreDecode.ReadsPagesFrom source nextOverflow
      encoding.overflowPages)
    (heightBound : state.tree.root.erase.height < source.pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length < source.pageCount + 1) :
    CoreDecode.decodeTableFrom source
      (CoreDecode.CatalogEntry.ofEncoded (chunkTableCatalogEntry state)) =
        some state.table.withoutIndexes := by
  have rowsValid : ∀ entry ∈ state.tree.root.erase.toList,
      ∀ row ∈ entry.2, row.WellFormed state.table.schema := by
    intro entry entryMember row rowMember
    have member : row ∈ CoreChunkPageState.Node.rows state.tree.root := by
      unfold CoreChunkPageState.Node.rows
      simp only [List.mem_flatMap]
      exact ⟨entry, entryMember, rowMember⟩
    change row ∈ CoreChunkPageState.Store.rows state.tree at member
    rw [state.represents] at member
    exact state.table.rowsWellFormed.1 row member
  have decodedRows := decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow
    state.table.schema source state.tree.root nextOverflow encoding
    (source.pageCount + 1) encoded treeContains overflowContains
    state.tree.rootValid rowsValid heightBound nextPositive pageBound fuelBound
  unfold CoreDecode.decodeTableFrom chunkTableCatalogEntry
    CoreDecode.CatalogEntry.ofEncoded
  simp only [Bool.false_eq_true, if_false]
  simp only [dif_pos True.intro]
  simp only [Option.bind_eq_bind, Option.bind]
  unfold CoreFile.tableSQL CoreChunkPageState.TableState.rootPage
  rw [CoreDecode.parseTableSchema_catalogSQL state.table]
  simp only [Option.bind_eq_bind, Option.bind]
  simp only [dif_pos True.intro]
  rw [decodedRows]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [Core.Table.rebuildFromCatalog_catalogSQL]
  change (Core.Table.rebuild state.table.schema []
    (CoreChunkPageState.Store.rows state.tree) state.table.catalogSource).toOption = _
  rw [state.represents, Core.Table.rebuild_withoutIndexes]
  rfl

theorem decodeTablesFrom_encodeChunkTablesWithOverflow
    (source : CoreDecode.PageSource) :
    ∀ (nextOverflow : Nat) (tables : List CoreChunkPageState.TableState)
      (encoding : OverflowEncoding),
      encodeChunkTablesWithOverflow nextOverflow tables = some encoding →
      PageSourceContains source encoding.treePages →
      CoreDecode.ReadsPagesFrom source nextOverflow encoding.overflowPages →
      0 < nextOverflow →
      nextOverflow + encoding.overflowPages.length < 2 ^ 32 →
      encoding.overflowPages.length < source.pageCount + 1 →
      (∀ table ∈ tables,
        table.tree.root.erase.height < source.pageCount + 1) →
      (tables.map (fun table => CoreDecode.CatalogEntry.ofEncoded
        (chunkTableCatalogEntry table))).mapM
          (CoreDecode.decodeTableFrom source) =
        some (tables.map (fun table => table.table.withoutIndexes))
  | _, [], encoding, encoded, _, _, _, _, _, _ => by
      simp only [encodeChunkTablesWithOverflow, Option.some.injEq] at encoded
      subst encoding
      rfl
  | nextOverflow, table :: tables, encoding, encoded, treeContains,
      overflowContains, nextPositive, pageBound, fuelBound, heights => by
      simp only [encodeChunkTablesWithOverflow, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeChunkNodeWithOverflow table.table.schema
          table.tree.root nextOverflow with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : encodeChunkTablesWithOverflow head.nextPage tables with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encoding
          have headTreeContains : PageSourceContains source head.treePages := by
            intro numbered member
            exact treeContains numbered (by simp [member])
          have tailTreeContains : PageSourceContains source tail.treePages := by
            intro numbered member
            exact treeContains numbered (by simp [member])
          have headOverflowContains : CoreDecode.ReadsPagesFrom source
              nextOverflow head.overflowPages :=
            CoreDecode.ReadsPagesFrom.left overflowContains
          have tailOverflowAt :=
            CoreDecode.ReadsPagesFrom.right overflowContains
          have headNext := encodeChunkNodeWithOverflow_nextPage
            table.table.schema table.tree.root nextOverflow head headResult
          have tailOverflowContains : CoreDecode.ReadsPagesFrom source
              head.nextPage tail.overflowPages := by
            simpa [headNext] using tailOverflowAt
          have headDecoded := decodeTableFrom_encodeChunkNodeWithOverflow
            source table nextOverflow head headResult headTreeContains
            headOverflowContains (heights table (by simp)) nextPositive
            (by simp only [List.length_append] at pageBound; omega)
            (by simp only [List.length_append] at fuelBound; omega)
          have tailDecoded := decodeTablesFrom_encodeChunkTablesWithOverflow
            source head.nextPage tables tail tailResult tailTreeContains
            tailOverflowContains (by rw [headNext]; omega)
            (by
              simp only [List.length_append] at pageBound
              rw [headNext]
              omega)
            (by simp only [List.length_append] at fuelBound; omega)
            (fun candidate member => heights candidate (by simp [member]))
          simp only [List.map_cons, List.mapM_cons, headDecoded, tailDecoded,
            Option.bind_eq_bind, Option.bind]
          rfl

end CorePageCodec

end SQLeanite
