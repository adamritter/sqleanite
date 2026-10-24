import SQLeanite.CoreWidePageCodec

namespace SQLeanite
namespace CoreWidePageInverse

theorem decodeOffsetList_encoded (values : List Nat)
    (bounded : ∀ value ∈ values, value < 256 ^ 2) (suffix : List UInt8) :
    CoreDecode.decodeOffsetList values.length
      (values.flatMap PhysicalCodec.encodeU16Nat ++ suffix) = some values := by
  induction values generalizing suffix with
  | nil => rfl
  | cons value values induction =>
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
        CoreDecode.decodeOffsetList]
      change (FileFormat.decodeUnsignedFixed 2
        (FileFormat.encodeUnsignedFixed 2 value ++
          (values.flatMap PhysicalCodec.encodeU16Nat ++ suffix)) >>= fun pair =>
            CoreDecode.decodeOffsetList values.length pair.2 >>= fun offsets =>
              some (pair.1 :: offsets)) = some (value :: values)
      rw [FileFormat.decodeUnsignedFixed_encode _
        (bounded value (by simp))]
      simp only [Option.bind_eq_bind, Option.bind]
      have tailDecoded := induction (fun candidate member =>
        bounded candidate (by simp [member])) suffix
      rw [tailDecoded]

theorem cellOffsetsFrom_bounded (start : Nat) (cells : List (List UInt8))
    (within : start + cells.flatten.length ≤ PhysicalCodec.pageSize) :
    ∀ offset ∈ PhysicalCodec.cellOffsetsFrom start cells,
      offset < 256 ^ 2 := by
  induction cells generalizing start with
  | nil => simp [PhysicalCodec.cellOffsetsFrom]
  | cons cell cells induction =>
      intro offset member
      simp only [PhysicalCodec.cellOffsetsFrom, List.mem_cons] at member
      rcases member with rfl | later
      · have pageBound : PhysicalCodec.pageSize < 256 ^ 2 := by decide
        simp only [List.flatten_cons, List.length_append] at within
        omega
      · apply induction (start := start + cell.length)
        · simp only [List.flatten_cons, List.length_append] at within
          simpa [Nat.add_assoc] using within
        · exact later

private def decodeChildAt (page : List UInt8) (offset : Nat) : Option Nat :=
  match (page.drop offset).take 4 with
  | [first, second, third, fourth] =>
      some (FileFormat.decodeU32 ⟨first, second, third, fourth⟩)
  | _ => none

private theorem decodeChildrenAt_encoded
    (page : List UInt8) : ∀ (start : Nat)
      (children : List (Nat × Nat)) (cells : List (List UInt8)),
      children.mapM (fun child =>
        RecursivePageBTree.interiorCell? child.1 child.2) = some cells →
      page.drop start = cells.flatten →
      (PhysicalCodec.cellOffsetsFrom start cells).mapM
        (decodeChildAt page) = some (children.map Prod.fst)
  | _, [], cells, encoded, pageDrop => by
      simp only [List.mapM_nil, pure, Option.pure_def,
        Option.some.injEq] at encoded
      subst cells
      rfl
  | start, child :: children, cells, encoded, pageDrop => by
      simp only [List.mapM_cons] at encoded
      cases headResult : RecursivePageBTree.interiorCell?
          child.1 child.2 with
      | none => simp [headResult] at encoded
      | some cell =>
          simp only [headResult, Option.bind_eq_bind, Option.bind] at encoded
          cases tailResult : children.mapM (fun candidate =>
              RecursivePageBTree.interiorCell?
                candidate.1 candidate.2) with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, pure, Option.pure_def,
                Option.some.injEq] at encoded
              subst cells
              rcases CorePageCodec.interiorCell?_shape headResult with
                ⟨childValue, childEqual, keyValue, keyEqual, cellEqual⟩
              have headDecoded : decodeChildAt page start = some child.1 := by
                unfold decodeChildAt
                rw [pageDrop]
                simp only [List.flatten_cons]
                rw [cellEqual]
                simpa [FileFormat.encodeU32Bytes, childEqual] using
                  FileFormat.decodeU32_encode childValue
              have tailDrop : page.drop (start + cell.length) = tail.flatten := by
                rw [← List.drop_drop, pageDrop]
                simp
              simp only [PhysicalCodec.cellOffsetsFrom, List.mapM_cons,
                headDecoded, Option.bind_eq_bind, Option.bind, List.map_cons]
              rw [decodeChildrenAt_encoded page (start + cell.length)
                children tail tailResult tailDrop]
              rfl

/-- Arbitrary-fanout inverse for the exact SQLite interior-page constructor.
The older codec had separate one- and two-cell proofs; this theorem is the
byte-level fact required by a genuine 256-child physical tree. -/
theorem interiorChildren_interiorPage (children : List (Nat × Nat))
    (right : Nat) {page : CoreFile.Page}
    (built : RecursivePageBTree.interiorPage? children right = some page) :
    CoreDecode.interiorChildren? page.bytes =
      some (children.map Prod.fst ++ [right]) := by
  unfold RecursivePageBTree.interiorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      cases cellsResult : children.mapM (fun child =>
          RecursivePageBTree.interiorCell? child.1 child.2) with
      | none => simp [cellsResult] at built
      | some cells =>
          simp only [cellsResult] at built
          split at built
          next fits =>
            injection built with equal
            subst page
            let contentStart := PhysicalCodec.pageSize -
              (PhysicalCodec.cellBytes cells).length
            let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
              List.replicate
                (contentStart -
                  (PhysicalTableBTree.interiorHeader cells.length contentStart
                    rightmost ++
                    PhysicalCodec.leafPointers contentStart cells).length) 0 ++
              PhysicalCodec.cellBytes cells
            have bodyLayout :
                PhysicalTableBTree.interiorPageBody rightmost cells =
                  5 :: 0 :: 0 ::
                    (PhysicalCodec.encodeU16Nat cells.length ++
                      PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
                        (FileFormat.encodeU32Bytes rightmost ++ afterHeader)) := by
              unfold PhysicalTableBTree.interiorPageBody
                PhysicalTableBTree.interiorHeader
              simp only [List.cons_append, List.nil_append]
              rfl
            have bodyLength :
                (PhysicalTableBTree.interiorPageBody rightmost cells).length =
                  PhysicalCodec.pageSize :=
              PhysicalTableBTree.interiorPageBody_length rightmost cells fits
            have countBound : cells.length < 256 ^ 2 := by
              simpa using fits.cellCount_lt
            have contentLe : (PhysicalCodec.cellBytes cells).length ≤
                PhysicalCodec.pageSize := by
              unfold PhysicalTableBTree.InteriorPageFit at fits
              omega
            have contentIdentity : contentStart +
                (PhysicalCodec.cellBytes cells).length =
                  PhysicalCodec.pageSize := by
              unfold contentStart
              exact Nat.sub_add_cancel contentLe
            have offsetsBound : ∀ offset ∈
                PhysicalCodec.cellOffsetsFrom contentStart cells,
                offset < 256 ^ 2 := by
              apply cellOffsetsFrom_bounded
              simpa [PhysicalCodec.cellBytes] using
                Nat.le_of_eq contentIdentity
            have offsetsDecoded : CoreDecode.decodeOffsetList cells.length
                (PhysicalCodec.leafPointers contentStart cells ++
                  List.replicate
                    (contentStart -
                      (PhysicalTableBTree.interiorHeader cells.length
                        contentStart rightmost ++
                        PhysicalCodec.leafPointers contentStart cells).length) 0 ++
                    PhysicalCodec.cellBytes cells) =
                  some (PhysicalCodec.cellOffsetsFrom contentStart cells) := by
              simpa [PhysicalCodec.leafPointers,
                PhysicalCodec.cellOffsetsFrom_length, List.append_assoc] using
                  decodeOffsetList_encoded
                    (PhysicalCodec.cellOffsetsFrom contentStart cells)
                      offsetsBound
                      (List.replicate
                        (contentStart -
                          (PhysicalTableBTree.interiorHeader cells.length
                            contentStart rightmost ++
                            PhysicalCodec.leafPointers contentStart cells).length)
                          0 ++ PhysicalCodec.cellBytes cells)
            have dropped := PhysicalTableBTree.interiorPageBody_drop_content
              rightmost cells fits
            have childrenDecoded :
                (PhysicalCodec.cellOffsetsFrom contentStart cells).mapM
                  (decodeChildAt
                    (PhysicalTableBTree.interiorPageBody rightmost cells)) =
                  some (children.map Prod.fst) := by
              apply decodeChildrenAt_encoded
                (PhysicalTableBTree.interiorPageBody rightmost cells)
                  contentStart children cells cellsResult
              simpa [contentStart, PhysicalCodec.cellBytes] using dropped
            change CoreDecode.interiorChildren?
              (PhysicalTableBTree.interiorPageBody rightmost cells) = _
            unfold CoreDecode.interiorChildren?
            rw [if_pos (by simpa using bodyLength)]
            rw [bodyLayout]
            let countValue : FileFormat.U16Value :=
              ⟨cells.length, by simpa using countBound⟩
            let contentValue : FileFormat.U16Value :=
              ⟨contentStart, by
                simpa using PhysicalCodec.contentStart_lt cells⟩
            have countEncoding : PhysicalCodec.encodeU16Nat cells.length =
                FileFormat.encodeU16Bytes countValue := by
              symm
              rw [FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed]
              rfl
            have contentEncoding : PhysicalCodec.encodeU16Nat contentStart =
                FileFormat.encodeU16Bytes contentValue := by
              symm
              rw [FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed]
              rfl
            rw [countEncoding, contentEncoding]
            simp only [FileFormat.encodeU16Bytes, List.append_assoc,
              List.cons_append, List.nil_append, FileFormat.encodeU32Bytes]
            rw [FileFormat.decodeU16_encode countValue]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [FileFormat.decodeU32_encode rightmost]
            rw [offsetsDecoded]
            have pageRestore :
                5 :: 0 :: 0 ::
                  (FileFormat.encodeU16 countValue).1 ::
                  (FileFormat.encodeU16 countValue).2 ::
                  (FileFormat.encodeU16 contentValue).1 ::
                  (FileFormat.encodeU16 contentValue).2 :: 0 ::
                  (FileFormat.encodeU32 rightmost).first ::
                  (FileFormat.encodeU32 rightmost).second ::
                  (FileFormat.encodeU32 rightmost).third ::
                  (FileFormat.encodeU32 rightmost).fourth :: afterHeader =
                    PhysicalTableBTree.interiorPageBody rightmost cells := by
              rw [bodyLayout]
              simp [countEncoding, contentEncoding,
                FileFormat.encodeU16Bytes, FileFormat.encodeU32Bytes]
            rw [pageRestore]
            change (PhysicalCodec.cellOffsetsFrom contentStart cells).mapM
                (decodeChildAt
                  (PhysicalTableBTree.interiorPageBody rightmost cells)) >>= _ = _
            rw [childrenDecoded]
            simp [CorePageCodec.boundedU32?_value rightResult]
          next => contradiction

private theorem encodeInteriorCells_pageNumbers :
    ∀ {nodes : List (WidePageTree.Node CoreWidePageState.Chunk)}
      {encoded : List (Nat × Nat)},
      nodes.mapM (fun child => do
        let key ← CoreWidePageCodec.maximumChunkRowid? child
        some (child.rootId, key)) = some encoded →
      encoded.map Prod.fst = nodes.map WidePageTree.Node.rootId
  | [], encoded, success => by
      simp only [List.mapM_nil, pure, Option.pure_def,
        Option.some.injEq] at success
      subst encoded
      rfl
  | node :: nodes, encoded, success => by
      rw [List.mapM_cons] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨head, headResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨tail, tailResult, success⟩
      simp only [pure, Option.pure_def, Option.some.injEq] at success
      subst encoded
      have headRoot : head.1 = node.rootId := by
        cases keyResult : CoreWidePageCodec.maximumChunkRowid? node with
        | none => simp [keyResult] at headResult
        | some key =>
            simp [keyResult] at headResult
            subst head
            rfl
      simp only [List.map_cons]
      rw [headRoot, encodeInteriorCells_pageNumbers tailResult]

theorem interiorCells?_pageNumbers
    {children : List (WidePageTree.Node CoreWidePageState.Chunk)}
    {cells : List (Nat × Nat)}
    {last : WidePageTree.Node CoreWidePageState.Chunk}
    (success : CoreWidePageCodec.interiorCells? children =
      some (cells, last)) :
    cells.map Prod.fst ++ [last.rootId] =
      children.map WidePageTree.Node.rootId := by
  unfold CoreWidePageCodec.interiorCells? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨parts, splitResult, success⟩
  rcases parts with ⟨initial, terminal⟩
  rcases Option.bind_eq_some_iff.mp success with ⟨encoded, encodedResult, success⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at success
  rcases success with ⟨rfl, rfl⟩
  have encodedRoots := encodeInteriorCells_pageNumbers encodedResult
  calc
    encoded.map Prod.fst ++ [terminal.rootId] =
        initial.map WidePageTree.Node.rootId ++ [terminal.rootId] := by
          rw [encodedRoots]
    _ = (initial ++ [terminal]).map WidePageTree.Node.rootId := by simp
    _ = children.map WidePageTree.Node.rootId := by
      rw [WidePageTree.splitLast?_reconstruct splitResult]

theorem decodeRowsFrom_encodeChunkLeaf (schema : Core.Schema)
    (entries : List (PagedBTree.Entry CoreWidePageState.Chunk))
    (page : CoreFile.Page)
    (valid : ∀ entry ∈ entries, ∀ row ∈ entry.2,
      row.WellFormed schema)
    (inline : ∀ entry ∈ entries, ∀ row ∈ entry.2,
      CoreOverflow.RowInline schema row)
    (encoded : CorePageCodec.encodeChunkLeaf schema entries = some page)
    (source : CoreDecode.PageSource) :
    CoreDecode.decodeRowsFrom schema source page.bytes =
      some (entries.flatMap fun entry => entry.2) := by
  unfold CorePageCodec.encodeChunkLeaf CorePageCodec.encodeLeaf at encoded
  cases cellsResult :
      (entries.flatMap fun entry =>
        entry.2.map fun row => (row.treeKey, row)).mapM
          (fun entry => CoreRecord.encodeCell? schema entry.2) with
  | none => simp [cellsResult] at encoded
  | some cells =>
      simp only [cellsResult, Option.bind_eq_bind, Option.bind] at encoded
      let rows := entries.flatMap fun entry => entry.2
      have rowCells : rows.mapM (CoreRecord.encodeCell? schema) =
          some cells := by
        rw [← CorePageCodec.mapM_map_entry_values] at cellsResult
        simpa [rows, List.map_flatMap, List.map_map,
          Function.comp_def] using cellsResult
      have rowsValid : ∀ row ∈ rows, row.WellFormed schema := by
        intro row member
        rcases List.mem_flatMap.mp member with
          ⟨entry, entryMember, rowMember⟩
        exact valid entry entryMember row rowMember
      have rowsInline : ∀ row ∈ rows,
          CoreOverflow.RowInline schema row := by
        intro row member
        rcases List.mem_flatMap.mp member with
          ⟨entry, entryMember, rowMember⟩
        exact inline entry entryMember row rowMember
      rcases CorePageCodec.tableCellPlans_of_inline_encodeCells schema rows
          cells rowCells rowsInline with ⟨plans, plansResult, planCells⟩
      let resolved : CoreOverflow.Resolved := ⟨cells, [], 1⟩
      have resolvedResult : CoreOverflow.resolvePlans 1 plans =
          some resolved := by
        exact CoreOverflow.resolvePlans_of_cellBytes_none 1 plans cells
          planCells
      have decoded := CoreDecode.decodeRowsFrom_resolvedLeaf schema source rows
        plans 1 resolved page rowsValid plansResult resolvedResult encoded
        (by omega) (by simp [resolved]) (by simp [resolved]) (by
          simp [resolved, CoreDecode.ReadsPagesFrom])
      simpa [rows] using decoded

private def RowsValid (schema : Core.Schema)
    (node : WidePageTree.Node CoreWidePageState.Chunk) : Prop :=
  ∀ entry ∈ node.toList, ∀ row ∈ entry.2, row.WellFormed schema

private def RowsInline (schema : Core.Schema)
    (node : WidePageTree.Node CoreWidePageState.Chunk) : Prop :=
  ∀ entry ∈ node.toList, ∀ row ∈ entry.2,
    CoreOverflow.RowInline schema row

private theorem decodeChildrenFold (schema : Core.Schema)
    (source : CoreDecode.PageSource) (encodeFuel decodeFuel : Nat)
    (childExact : ∀ (node : WidePageTree.Node CoreWidePageState.Chunk)
      (pages : List CorePageCodec.NumberedPage),
      CoreWidePageCodec.encodeChunkNode encodeFuel schema node = some pages →
      CorePageCodec.PageSourceContains source pages →
      RowsValid schema node →
      RowsInline schema node →
      CoreDecode.decodeSubtreeRowsFrom schema source decodeFuel node.rootId =
        some (CoreWidePageState.Node.rows node)) :
    ∀ (children : List (WidePageTree.Node CoreWidePageState.Chunk))
      (encodings : List (List CorePageCodec.NumberedPage))
      (accumulator : List Core.Row),
      children.mapM (CoreWidePageCodec.encodeChunkNode encodeFuel schema) =
        some encodings →
      CorePageCodec.PageSourceContains source encodings.flatten →
      (∀ node ∈ children, RowsValid schema node) →
      (∀ node ∈ children, RowsInline schema node) →
      (children.map WidePageTree.Node.rootId).foldlM
        (fun rows child => do
          let decoded ← CoreDecode.decodeSubtreeRowsFrom schema source decodeFuel child
          some (rows ++ decoded)) accumulator =
        some (accumulator ++ children.flatMap CoreWidePageState.Node.rows)
  | [], encodings, accumulator, encoded, _, _, _ => by
      simp only [List.mapM_nil, pure, Option.pure_def,
        Option.some.injEq] at encoded
      subst encodings
      simp
  | child :: children, encodings, accumulator, encoded, contains, valid,
      inline => by
      simp only [List.mapM_cons] at encoded
      cases headResult : CoreWidePageCodec.encodeChunkNode encodeFuel schema child with
      | none => simp [headResult] at encoded
      | some headPages =>
          simp only [headResult, Option.bind_eq_bind, Option.bind] at encoded
          cases tailResult : children.mapM
              (CoreWidePageCodec.encodeChunkNode encodeFuel schema) with
          | none => simp [tailResult] at encoded
          | some tailPages =>
              simp only [tailResult, pure, Option.pure_def,
                Option.some.injEq] at encoded
              subst encodings
              have headContains : CorePageCodec.PageSourceContains source
                  headPages := by
                intro page member
                exact contains page (by simp [member])
              have tailContains : CorePageCodec.PageSourceContains source
                  tailPages.flatten := by
                intro page member
                exact contains page (by simp [member])
              have headDecoded := childExact child headPages headResult
                headContains (valid child (by simp)) (inline child (by simp))
              simp only [List.map_cons, List.foldlM_cons, headDecoded,
                Option.bind_eq_bind, Option.bind, List.flatMap_cons]
              have tailDecoded := decodeChildrenFold schema source encodeFuel
                decodeFuel
                childExact children
                tailPages
                (accumulator ++ CoreWidePageState.Node.rows child)
                tailResult tailContains (fun node member =>
                  valid node (by simp [member])) (fun node member =>
                    inline node (by simp [member]))
              simpa [List.append_assoc, Option.bind] using tailDecoded

private theorem flatMap_node_rows
    (children : List (WidePageTree.Node CoreWidePageState.Chunk)) :
    children.flatMap CoreWidePageState.Node.rows =
      (children.flatMap WidePageTree.Node.toList).flatMap
        (fun entry => entry.2) := by
  induction children with
  | nil => rfl
  | cons child children induction =>
      simp only [List.flatMap_cons, CoreWidePageState.Node.rows]
      rw [List.flatMap_append, induction]

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
  rw [CoreDecode.parseTableSchema_tableSQL state.table.schema
    (CanonicalSchemaSQL.Printable.ofWellFormed state.table.schema
      state.table.schemaWellFormed)]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos True.intro]
  rw [decodedRows]
  simp only [Option.bind_eq_bind, Option.bind]
  change (Core.Table.rebuild state.table.schema []
    (CoreWidePageState.Store.rows state.tree)).toOption = _
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

private theorem decodeTablesFrom_encodeTables
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

/-- The complete inline high-fanout image has the logical meaning carried by
its proof-owned state.  Tables are decoded by arbitrary-fanout traversal;
secondary indexes reuse the established promoted-key inverse. -/
theorem pageSourceRepresents_encodeBulkInlineWithState
    (utf8 : CoreDecode.UTF8Roundtrips) (database : Core.Database)
    (image : CoreFile.Image) (wideState : CoreWidePageState.State)
    (encoded : CoreWidePageCodec.encodeBulkInlineWithState database =
      some (image, wideState)) :
    CoreDecode.PageSourceRepresents
      (.ofList (image.pages.map CoreFile.Page.bytes)) database := by
  unfold CoreWidePageCodec.encodeBulkInlineWithState at encoded
  rcases Option.bind_eq_some_iff.mp encoded with ⟨state, stateResult, encoded⟩
  split at encoded
  next inlineResult =>
    rcases Option.bind_eq_some_iff.mp encoded with
      ⟨numbered, numberedResult, encoded⟩
    let ordered := CorePageCodec.orderNumberedPages
      (CoreWidePageCodec.includePendingBytePlaceholder state.nextPage numbered)
    dsimp only at encoded
    split at encoded
    next numbers =>
      rcases Option.bind_eq_some_iff.mp encoded with
        ⟨indexEncodings, indexResult, encoded⟩
      split at encoded
      next countBound =>
        let tableEntries := state.tables.map CoreWidePageCodec.tableCatalogEntry
        let indexEntries := CoreWideIndex.indexEntriesOf indexEncodings
        let entries := tableEntries ++ indexEntries
        let indexPages := CoreWideIndex.indexPagesOf indexEncodings
        let remaining := ordered.map CorePageCodec.NumberedPage.page ++ indexPages
        let count : FileFormat.U32Value := ⟨1 + remaining.length, by
          change 1 + remaining.length < 2 ^ 32
          have stronger : 1 + remaining.length + 1 < 2 ^ 32 := by
            simpa [remaining, ordered, indexPages] using countBound
          omega⟩
        change (do
          let schema ← CoreFile.schemaPageForEntries? entries count
          some (⟨database, schema :: remaining⟩, state)) =
            some (image, wideState) at encoded
        cases schemaResult : CoreFile.schemaPageForEntries? entries count with
        | none => simp [schemaResult] at encoded
        | some schemaPage =>
          rw [schemaResult] at encoded
          simp only [Option.bind_eq_bind, Option.bind, Option.some.injEq,
            Prod.mk.injEq] at encoded
          rcases encoded with ⟨imageEqual, stateEqual⟩
          subst image
          subst wideState
          let source : CoreDecode.PageSource := .ofList
            ((schemaPage :: remaining).map CoreFile.Page.bytes)
          have stateNextLower : 2 ≤ state.nextPage :=
            CoreWidePageState.State.build?_nextPage_ge stateResult
          have orderedCount : ordered.length = state.nextPage - 2 := by
            have lengths := congrArg List.length numbers
            simpa using lengths
          have startEqual : 2 + ordered.length = state.nextPage := by
            rw [orderedCount]
            omega
          have orderedNumbers : ordered.map
              CorePageCodec.NumberedPage.pageNumber =
                List.range' 2 ordered.length := by
            simpa [orderedCount] using numbers
          have remainingReads : CoreDecode.ReadsPagesFrom source 2 remaining := by
            simpa [source] using CoreDecode.ReadsPagesFrom.ofList_append
              [schemaPage.bytes] remaining []
          have orderedReads : CoreDecode.ReadsPagesFrom source 2
              (ordered.map CorePageCodec.NumberedPage.page) := by
            exact CoreDecode.ReadsPagesFrom.left
              (right := indexPages) (by simpa [remaining] using remainingReads)
          have orderedContains : CorePageCodec.PageSourceContains source ordered :=
            CorePageCodec.PageSourceContains.ofReadsRange source 2 ordered
              orderedNumbers orderedReads
          have numberedContains :
              CorePageCodec.PageSourceContains source numbered := by
            intro page member
            apply orderedContains page
            apply List.mem_mergeSort.mpr
            unfold CoreWidePageCodec.includePendingBytePlaceholder
            split <;> simp_all
          have numberedLengthLe : numbered.length ≤ ordered.length := by
            simp [ordered, CorePageCodec.orderNumberedPages,
              CoreWidePageCodec.includePendingBytePlaceholder]
            split <;> simp
          have sourceCount : source.pageCount = 1 + remaining.length := by
            simp [source, CoreDecode.PageSource.ofList, Nat.add_comm]
          have tablesDecoded := decodeTablesFrom_encodeTables source state.tables
            numbered numberedResult numberedContains (by
              rw [sourceCount]
              simp only [remaining, List.length_append, List.length_map]
              omega)
            (fun table member =>
              CoreWidePageCodec.rowsInline_spec inlineResult table member)
          have tableList :
              state.tables.map (fun table => table.table.withoutIndexes) =
                database.tables.map Core.Table.withoutIndexes := by
            calc
              _ = (state.tables.map (fun table => table.table)).map
                    Core.Table.withoutIndexes := by
                  simp [List.map_map, Function.comp_def]
              _ = database.tables.map Core.Table.withoutIndexes := by
                  rw [state.tables_eq,
                    (CoreWidePageState.State.build?_represents stateResult).1]
          have tablesDecoded' :
              (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).mapM
                  (CoreDecode.decodeTableFrom source) =
                some (database.tables.map Core.Table.withoutIndexes) := by
            unfold tableEntries
            simpa [List.map_map, Function.comp_def, tableList]
              using tablesDecoded
          have indexReads : CoreDecode.ReadsPagesFrom source state.nextPage
              indexPages := by
            have afterTables := CoreDecode.ReadsPagesFrom.right
              (left := ordered.map CorePageCodec.NumberedPage.page)
              (right := indexPages)
              (by simpa [remaining] using remainingReads)
            simpa [startEqual] using afterTables
          let indexNumbered := CoreWideIndex.numberedPagesOf indexEncodings
          have indexNumbers : indexNumbered.map
                CorePageCodec.NumberedPage.pageNumber =
              List.range' state.nextPage indexPages.length := by
            simpa [indexNumbered, indexPages] using
              CoreWideIndex.encodeIndexTableGroups_numbers state.nextPage
                database.tables indexEncodings indexResult
          have indexPageMap : indexNumbered.map
                CorePageCodec.NumberedPage.page = indexPages := by
            simpa [indexNumbered, indexPages] using
              (CoreWideIndex.indexPagesOf_eq_map indexEncodings).symm
          have indexNumberedLength : indexNumbered.length =
              indexPages.length := by
            have equal := congrArg List.length indexPageMap
            simpa using equal
          have indexNumbers' : indexNumbered.map
                CorePageCodec.NumberedPage.pageNumber =
              List.range' state.nextPage indexNumbered.length := by
            simpa [indexNumberedLength] using indexNumbers
          have indexNumberedReads : CoreDecode.ReadsPagesFrom source
              state.nextPage
              (indexNumbered.map CorePageCodec.NumberedPage.page) := by
            simpa [indexPageMap] using indexReads
          have allIndexesContain : CorePageCodec.PageSourceContains source
              indexNumbered :=
            CorePageCodec.PageSourceContains.ofReadsRange source
              state.nextPage indexNumbered indexNumbers' indexNumberedReads
          have individualIndexContains : ∀ encoding ∈ indexEncodings,
              CorePageCodec.PageSourceContains source
                encoding.numberedPages := by
            intro encoding member page pageMember
            apply allIndexesContain page
            unfold indexNumbered CoreWideIndex.numberedPagesOf
            simp only [List.mem_flatMap]
            exact ⟨encoding, member, List.mem_mergeSort.mpr pageMember⟩
          have individualIndexBound : ∀ encoding ∈ indexEncodings,
              encoding.numberedPages.length < source.pageCount + 1 := by
            intro encoding member
            have lengthBound :=
              CoreWideIndex.numberedPages_length_le_of_mem member
            unfold indexNumbered at indexNumberedLength
            rw [indexNumberedLength] at lengthBound
            have indexWithinRemaining : indexPages.length ≤
                remaining.length := by
              simp [remaining]
            rw [sourceCount]
            omega
          have indexesApplied :=
            CoreWideIndex.applyIndexesForOpen_encoded source database
              state.nextPage indexEncodings indexResult
              individualIndexContains individualIndexBound
          have indexesApplied' :
              CoreDecode.applyIndexesForOpen source database.withoutIndexes
                (indexEntries.map CoreDecode.CatalogEntry.ofEncoded) =
                  some database.canonicalize := by
            simpa [indexEntries, CoreWideIndex.indexEntriesOf, List.map_map,
              Function.comp_def] using indexesApplied
          have safe : ∀ entry ∈ entries,
              CoreDecode.CatalogTextRoundtrips entry := by
            intro entry _
            exact ⟨utf8 entry.kind, utf8 entry.name,
              utf8 entry.table, utf8 entry.sql⟩
          have catalogDecoded :=
            CoreDecode.decodeCatalogForOpen_schemaPageForEntries entries count
              safe schemaResult
          have tableFilter :
              ((entries.map CoreDecode.CatalogEntry.ofEncoded).filter
                (fun entry => entry.kind == "table")) =
                tableEntries.map CoreDecode.CatalogEntry.ofEncoded := by
            rw [show entries.map CoreDecode.CatalogEntry.ofEncoded =
                tableEntries.map CoreDecode.CatalogEntry.ofEncoded ++
                  indexEntries.map CoreDecode.CatalogEntry.ofEncoded by
              simp [entries]]
            rw [List.filter_append]
            have tablesKept :
                (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                  (fun entry => entry.kind == "table") =
                    tableEntries.map CoreDecode.CatalogEntry.ofEncoded := by
              apply List.filter_eq_self.mpr
              intro entry member
              rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
              rfl
            have indexesRemoved :
                (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                  (fun entry => entry.kind == "table") = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro entry member
              rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp encodedMember with ⟨encoding, _, rfl⟩
              simp [CoreWideIndex.IndexEncoding.catalogEntry,
                CoreDecode.CatalogEntry.ofEncoded]
            rw [tablesKept, indexesRemoved, List.append_nil]
          have indexFilter :
              ((entries.map CoreDecode.CatalogEntry.ofEncoded).filter
                (fun entry => entry.kind == "index")) =
                indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
            rw [show entries.map CoreDecode.CatalogEntry.ofEncoded =
                tableEntries.map CoreDecode.CatalogEntry.ofEncoded ++
                  indexEntries.map CoreDecode.CatalogEntry.ofEncoded by
              simp [entries]]
            rw [List.filter_append]
            have tablesRemoved :
                (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                  (fun entry => entry.kind == "index") = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro entry member
              rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
              simp [CoreWidePageCodec.tableCatalogEntry,
                CoreDecode.CatalogEntry.ofEncoded]
            have indexesKept :
                (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                  (fun entry => entry.kind == "index") =
                    indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
              apply List.filter_eq_self.mpr
              intro entry member
              rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp encodedMember with ⟨encoding, _, rfl⟩
              rfl
            rw [tablesRemoved, indexesKept, List.nil_append]
          have firstRead : source.readPage 1 = some schemaPage.bytes := by
            simp [source, CoreDecode.PageSource.ofList, CoreDecode.page?]
          refine .intro (entries.map CoreDecode.CatalogEntry.ofEncoded) ?_ ?_ ?_
          · rw [firstRead]
            simp only [Option.bind_eq_bind, Option.bind]
            exact catalogDecoded
          · rw [tableFilter]
            exact tablesDecoded'
          · rw [indexFilter]
            exact indexesApplied'
      next => contradiction
    next => contradiction
  next => contradiction

theorem pageSourceRepresents_encodeBulkInline
    (utf8 : CoreDecode.UTF8Roundtrips) (database : Core.Database)
    (image : CoreFile.Image)
    (encoded : CoreWidePageCodec.encodeBulkInline database = some image) :
    CoreDecode.PageSourceRepresents
      (.ofList (image.pages.map CoreFile.Page.bytes)) database := by
  unfold CoreWidePageCodec.encodeBulkInline at encoded
  cases resultEq : CoreWidePageCodec.encodeBulkInlineWithState database with
  | none => simp [resultEq] at encoded
  | some result =>
      rcases result with ⟨builtImage, state⟩
      simp only [resultEq, Option.map, Option.some.injEq] at encoded
      subst image
      exact pageSourceRepresents_encodeBulkInlineWithState utf8 database
        builtImage state resultEq

theorem decodeFromPageSource_encodeBulkInline
    (utf8 : CoreDecode.UTF8Roundtrips) (database : Core.Database)
    (image : CoreFile.Image)
    (encoded : CoreWidePageCodec.encodeBulkInline database = some image) :
    CoreDecode.decodeFromPageSource
      (.ofList (image.pages.map CoreFile.Page.bytes)) =
        some database.canonicalize :=
  (pageSourceRepresents_encodeBulkInline utf8 database image encoded).decode

theorem encodeBulkInline_header {database : Core.Database}
    {image : CoreFile.Image}
    (encoded : CoreWidePageCodec.encodeBulkInline database = some image) :
    ∃ (count : FileFormat.U32Value) (schema : CoreFile.Page)
      (remaining : List CoreFile.Page) (body : List UInt8),
      image.pages = schema :: remaining ∧
      image.pageCount = count.val ∧
      schema.bytes = FileFormat.encodeDatabaseHeader
        (CoreFile.databaseHeader count) ++ body := by
  unfold CoreWidePageCodec.encodeBulkInline at encoded
  cases resultEq : CoreWidePageCodec.encodeBulkInlineWithState database with
  | none => simp [resultEq] at encoded
  | some result =>
    rcases result with ⟨builtImage, builtState⟩
    simp only [resultEq, Option.map, Option.some.injEq] at encoded
    subst image
    unfold CoreWidePageCodec.encodeBulkInlineWithState at resultEq
    rcases Option.bind_eq_some_iff.mp resultEq with ⟨state, stateResult, resultEq⟩
    split at resultEq
    next =>
      rcases Option.bind_eq_some_iff.mp resultEq with
        ⟨numbered, numberedResult, resultEq⟩
      dsimp only at resultEq
      split at resultEq
      next =>
        rcases Option.bind_eq_some_iff.mp resultEq with
          ⟨indexEncodings, indexResult, resultEq⟩
        split at resultEq
        next countBound =>
          let ordered := CorePageCodec.orderNumberedPages
            (CoreWidePageCodec.includePendingBytePlaceholder state.nextPage
              numbered)
          let entries := state.tables.map CoreWidePageCodec.tableCatalogEntry ++
            CoreWideIndex.indexEntriesOf indexEncodings
          let remaining := ordered.map CorePageCodec.NumberedPage.page ++
            CoreWideIndex.indexPagesOf indexEncodings
          let count : FileFormat.U32Value := ⟨1 + remaining.length, by
            have stronger : 1 + remaining.length + 1 < 2 ^ 32 := by
              simpa [remaining, ordered] using countBound
            omega⟩
          change (do
            let schema ← CoreFile.schemaPageForEntries? entries count
            some (⟨database, schema :: remaining⟩, state)) =
              some (builtImage, builtState) at resultEq
          cases schemaResult : CoreFile.schemaPageForEntries? entries count with
          | none => simp [schemaResult] at resultEq
          | some schema =>
            rw [schemaResult] at resultEq
            simp only [Option.bind_eq_bind, Option.bind, Option.some.injEq,
              Prod.mk.injEq] at resultEq
            rcases resultEq with ⟨imageEqual, stateEqual⟩
            subst builtImage
            rcases CoreFile.schemaPageForEntries_header schemaResult with
              ⟨body, header⟩
            refine ⟨count, schema, remaining, body, rfl, ?_, header⟩
            simp [CoreFile.Image.pageCount, count, Nat.add_comm]
        next => contradiction
      next => contradiction
    next => contradiction

/-- Whole-file left inverse for the high-fanout inline encoder. -/
theorem decode_encodeBulkInline (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CoreWidePageCodec.encodeBulkInline database = some image) :
    CoreDecode.decode image.fileBytes = some database.canonicalize := by
  rcases encodeBulkInline_header encoded with
    ⟨count, schema, remaining, body, pagesEqual, countEqual, headerEqual⟩
  have bytesLayout : image.fileBytes =
      FileFormat.encodeDatabaseHeader (CoreFile.databaseHeader count) ++
        (body ++ remaining.flatMap CoreFile.Page.bytes) := by
    unfold CoreFile.Image.fileBytes
    rw [pagesEqual]
    simp only [List.flatMap_cons]
    rw [headerEqual]
    simp [List.append_assoc]
  have fileLength : image.fileBytes.length =
      count.val * PhysicalCodec.pageSize := by
    rw [CoreFile.Image.fileBytes_length, countEqual, Nat.mul_comm]
  have splitPages : CoreDecode.pages count.val image.fileBytes =
      image.pages.map CoreFile.Page.bytes := by
    rw [← countEqual]
    exact CoreDecode.pages_image image
  unfold CoreDecode.decode
  rw [bytesLayout, FileFormat.decodeDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show (CoreFile.databaseHeader count).databaseSizePages.val = count.val
    from rfl]
  rw [dif_pos (by rfl), dif_pos (by rfl), dif_pos (by rfl)]
  rw [← bytesLayout]
  rw [dif_pos fileLength, splitPages]
  exact decodeFromPageSource_encodeBulkInline utf8 database image encoded

end CoreWidePageInverse
end SQLeanite
