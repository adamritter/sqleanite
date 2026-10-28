import SQLeanite.CoreDecode.LookupTableRangeIOFrom
import SQLeanite.CoreWidePageInverse.DecodeOffsetListEncoded

namespace SQLeanite
namespace CoreWidePageInverse

/-- Following the child pointers of an arbitrary-fanout encoded wide tree
recovers exactly its ordered row abstraction. -/
theorem decodeSubtreeRowsFrom_encodeChunkNode (schema : Core.Schema)
    (source : CoreDecode.PageSource) :
    ∀ (encodeFuel : Nat) (node : WidePageTree.Node CoreWidePageState.Chunk)
      (pages : List CorePageCodec.NumberedPage) (decodeFuel : Nat),
      CoreWidePageCodec.encodeChunkNode encodeFuel schema node = some pages →
      encodeFuel ≤ decodeFuel →
      CorePageCodec.PageSourceContains source pages →
      RowsValid schema node →
      RowsInline schema node →
      CoreDecode.decodeSubtreeRowsFrom schema source decodeFuel node.rootId =
        some (CoreWidePageState.Node.rows node) := by
  intro encodeFuel
  induction encodeFuel with
  | zero =>
      intro node pages decodeFuel encoded
      simp [CoreWidePageCodec.encodeChunkNode] at encoded
  | succ fuel induction =>
      intro node pages decodeFuel encoded fuelBound contains valid inline
      cases decodeFuel with
      | zero => omega
      | succ decodeFuel =>
        cases node with
        | leaf pageId entries =>
          simp only [CoreWidePageCodec.encodeChunkNode] at encoded
          rcases Option.bind_eq_some_iff.mp encoded with ⟨page, pageResult, encoded⟩
          simp only [Option.some.injEq] at encoded
          subst pages
          unfold CoreDecode.decodeSubtreeRowsFrom
          change (source.readPage pageId >>= _) = _
          rw [contains ⟨pageId, page⟩ (by simp)]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [CorePageCodec.interiorChildren_encodeChunkLeaf schema entries page
            pageResult]
          rw [decodeRowsFrom_encodeChunkLeaf schema entries page (by
            intro entry member row rowMember
            exact valid entry (by simpa [WidePageTree.Node.toList] using member)
              row rowMember) (by
            intro entry member row rowMember
            exact inline entry (by simpa [WidePageTree.Node.toList] using member)
              row rowMember) pageResult source]
          simp [CoreWidePageState.Node.rows, WidePageTree.Node.toList]
        | branch pageId children =>
          simp only [CoreWidePageCodec.encodeChunkNode] at encoded
          rcases Option.bind_eq_some_iff.mp encoded with ⟨parts, partsResult, encoded⟩
          rcases parts with ⟨cells, rightmost⟩
          rcases Option.bind_eq_some_iff.mp encoded with ⟨rootPage, rootResult, encoded⟩
          rcases Option.bind_eq_some_iff.mp encoded with
            ⟨childPages, childrenResult, encoded⟩
          simp only [Option.some.injEq] at encoded
          subst pages
          have rootRead : source.readPage pageId = some rootPage.bytes :=
            contains ⟨pageId, rootPage⟩ (by simp)
          have childrenContain : CorePageCodec.PageSourceContains source
              childPages.flatten := by
            intro page member
            exact contains page (by simp [member])
          have childValid : ∀ child ∈ children, RowsValid schema child := by
            intro child childMember entry entryMember row rowMember
            exact valid entry (by
              simp only [WidePageTree.Node.toList, List.mem_flatMap]
              exact ⟨child, childMember, entryMember⟩) row rowMember
          have childInline : ∀ child ∈ children,
              RowsInline schema child := by
            intro child childMember entry entryMember row rowMember
            exact inline entry (by
              simp only [WidePageTree.Node.toList, List.mem_flatMap]
              exact ⟨child, childMember, entryMember⟩) row rowMember
          have childrenDecoded := decodeChildrenFold schema source fuel decodeFuel
            (fun child pages childEncoded childContains childValid childInline =>
              induction child pages decodeFuel childEncoded
                (Nat.le_of_succ_le_succ fuelBound) childContains childValid
                childInline)
            children childPages [] childrenResult childrenContain
              childValid childInline
          unfold CoreDecode.decodeSubtreeRowsFrom
          change (source.readPage pageId >>= _) = _
          rw [rootRead]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [interiorChildren_interiorPage cells rightmost.rootId rootResult]
          rw [interiorCells?_pageNumbers partsResult]
          have rowsEqual := flatMap_node_rows children
          have branchRows :
              CoreWidePageState.Node.rows
                  (WidePageTree.Node.branch pageId children) =
                children.flatMap CoreWidePageState.Node.rows := by
            unfold CoreWidePageState.Node.rows
            simp only [WidePageTree.Node.toList]
            exact rowsEqual.symm
          change (children.map WidePageTree.Node.rootId).foldlM
              (fun rows child => do
                let decoded ← CoreDecode.decodeSubtreeRowsFrom schema source decodeFuel child
                some (rows ++ decoded)) [] =
              some (CoreWidePageState.Node.rows
                (WidePageTree.Node.branch pageId children))
          rw [branchRows]
          simpa using childrenDecoded

/-- One encoded high-fanout table decodes to the same logical table, with
indexes intentionally restored by the separate index pass. -/
theorem decodeTableFrom_encodeTable (source : CoreDecode.PageSource)
    (state : CoreWidePageState.TableState)
    (pages : List CorePageCodec.NumberedPage)
    (encoded : CoreWidePageCodec.encodeTable state = some pages)
    (contains : CorePageCodec.PageSourceContains source pages)
    (heightBound : state.tree.root.height < source.pageCount + 1)
    (inline : ∀ row ∈ state.table.rows,
      CoreOverflow.RowInline state.table.schema row) :
    CoreDecode.decodeTableFrom source
      (CoreDecode.CatalogEntry.ofEncoded
        (CoreWidePageCodec.tableCatalogEntry state)) =
      some state.table.withoutIndexes := by
  have rowsValid : RowsValid state.table.schema state.tree.root := by
    intro entry entryMember row rowMember
    have member : row ∈ CoreWidePageState.Node.rows state.tree.root := by
      unfold CoreWidePageState.Node.rows
      exact List.mem_flatMap.mpr ⟨entry, entryMember, rowMember⟩
    change row ∈ CoreWidePageState.Store.rows state.tree at member
    rw [state.represents] at member
    exact state.table.rowsWellFormed.1 row member
  have rowsInline : RowsInline state.table.schema state.tree.root := by
    intro entry entryMember row rowMember
    apply inline row
    rw [← state.represents]
    unfold CoreWidePageState.Store.rows CoreWidePageState.Node.rows
    exact List.mem_flatMap.mpr ⟨entry, entryMember, rowMember⟩
  have decodedRows := decodeSubtreeRowsFrom_encodeChunkNode
    state.table.schema source (state.tree.root.height + 1) state.tree.root
      pages (source.pageCount + 1) encoded (by omega) contains rowsValid
      rowsInline
  unfold CoreDecode.decodeTableFrom CoreWidePageCodec.tableCatalogEntry
    CoreDecode.CatalogEntry.ofEncoded
  simp only [Bool.false_eq_true, if_false, dif_pos True.intro,
    Option.bind_eq_bind, Option.bind]
  unfold CoreFile.tableSQL CoreWidePageState.TableState.rootPage
  rw [CoreDecode.parseTableSchema_catalogSQL state.table]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos True.intro]
  rw [decodedRows]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [Core.Table.rebuildFromCatalog_catalogSQL]
  change (Core.Table.rebuild state.table.schema []
    (CoreWidePageState.Store.rows state.tree) state.table.catalogSource).toOption = _
  rw [state.represents, Core.Table.rebuild_withoutIndexes]
  rfl

private theorem encodeChunkNode_height_lt_length_succ (schema : Core.Schema) :
    ∀ (fuel : Nat) (node : WidePageTree.Node CoreWidePageState.Chunk)
      (pages : List CorePageCodec.NumberedPage),
      CoreWidePageCodec.encodeChunkNode fuel schema node = some pages →
      node.height < pages.length + 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro node pages encoded
      simp [CoreWidePageCodec.encodeChunkNode] at encoded
  | succ fuel induction =>
      intro node pages encoded
      cases node with
      | leaf pageId entries =>
          simp only [CoreWidePageCodec.encodeChunkNode] at encoded
          rcases Option.bind_eq_some_iff.mp encoded with ⟨page, _, encoded⟩
          simp only [Option.some.injEq] at encoded
          subst pages
          simp [WidePageTree.Node.height]
      | branch pageId children =>
          simp only [CoreWidePageCodec.encodeChunkNode] at encoded
          rcases Option.bind_eq_some_iff.mp encoded with ⟨parts, partsResult, encoded⟩
          rcases parts with ⟨cells, rightmost⟩
          rcases Option.bind_eq_some_iff.mp encoded with ⟨page, _, encoded⟩
          rcases Option.bind_eq_some_iff.mp encoded with
            ⟨childPages, childrenResult, encoded⟩
          simp only [Option.some.injEq] at encoded
          subst pages
          cases children with
          | nil =>
              unfold CoreWidePageCodec.interiorCells? at partsResult
              simp [WidePageTree.splitLast?] at partsResult
          | cons child children =>
              simp only [List.mapM_cons] at childrenResult
              rcases Option.bind_eq_some_iff.mp childrenResult with
                ⟨headPages, headResult, childrenResult⟩
              rcases Option.bind_eq_some_iff.mp childrenResult with
                ⟨tailPages, tailResult, childrenResult⟩
              simp only [pure, Option.pure_def, Option.some.injEq] at childrenResult
              subst childPages
              have childHeight := induction child headPages headResult
              have headLength : headPages.length ≤
                  (headPages :: tailPages).flatten.length := by simp
              simp only [WidePageTree.Node.height, List.length_cons]
              omega

theorem decodeTablesFrom_encodeTables
    (source : CoreDecode.PageSource) :
    ∀ (tables : List CoreWidePageState.TableState)
      (pages : List CorePageCodec.NumberedPage),
      CoreWidePageCodec.encodeTables tables = some pages →
      CorePageCodec.PageSourceContains source pages →
      pages.length ≤ source.pageCount →
      (∀ table ∈ tables, ∀ row ∈ table.table.rows,
        CoreOverflow.RowInline table.table.schema row) →
      (tables.map (fun table => CoreDecode.CatalogEntry.ofEncoded
        (CoreWidePageCodec.tableCatalogEntry table))).mapM
          (CoreDecode.decodeTableFrom source) =
        some (tables.map (fun table => table.table.withoutIndexes))
  | [], pages, encoded, _, _, _ => by
      simp only [CoreWidePageCodec.encodeTables, List.mapM_nil, pure,
        Option.pure_def, Option.bind_eq_bind, Option.bind,
        Option.some.injEq] at encoded
      subst pages
      rfl
  | table :: tables, pages, encoded, contains, pageBound, inline => by
      unfold CoreWidePageCodec.encodeTables at encoded
      cases headResult : CoreWidePageCodec.encodeTable table with
      | none => simp [headResult] at encoded
      | some headPages =>
          cases tailResult : tables.mapM CoreWidePageCodec.encodeTable with
          | none => simp [headResult, tailResult] at encoded
          | some tailGroups =>
              simp only [List.mapM_cons, headResult, tailResult,
                Option.bind_eq_bind, Option.bind, pure, Option.pure_def,
                Option.some.injEq] at encoded
              subst pages
              have headContains :
                  CorePageCodec.PageSourceContains source headPages := by
                intro page member
                exact contains page (by simp [member])
              have tailContains : CorePageCodec.PageSourceContains source
                  tailGroups.flatten := by
                intro page member
                exact contains page (by simp [member])
              have headDecoded := decodeTableFrom_encodeTable source table
                headPages headResult headContains (by
                  have height := encodeChunkNode_height_lt_length_succ
                    table.table.schema (table.tree.root.height + 1)
                      table.tree.root headPages headResult
                  have lengthBound : headPages.length ≤ source.pageCount := by
                    have : headPages.length ≤
                        (headPages :: tailGroups).flatten.length := by simp
                    omega
                  omega)
                (fun row member => inline table (by simp) row member)
              have tailEncoded : CoreWidePageCodec.encodeTables tables =
                  some tailGroups.flatten := by
                unfold CoreWidePageCodec.encodeTables
                rw [tailResult]
                rfl
              have tailDecoded := decodeTablesFrom_encodeTables source tables
                tailGroups.flatten tailEncoded tailContains
                (by
                  have : tailGroups.flatten.length ≤
                      (headPages :: tailGroups).flatten.length := by simp
                  omega)
                (fun candidate member => inline candidate (by simp [member]))
              simp only [List.map_cons, List.mapM_cons, headDecoded, tailDecoded,
                Option.bind_eq_bind, Option.bind]
              rfl

end CoreWidePageInverse

end SQLeanite
