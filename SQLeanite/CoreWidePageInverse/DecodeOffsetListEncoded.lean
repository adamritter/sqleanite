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

def RowsValid (schema : Core.Schema)
    (node : WidePageTree.Node CoreWidePageState.Chunk) : Prop :=
  ∀ entry ∈ node.toList, ∀ row ∈ entry.2, row.WellFormed schema

def RowsInline (schema : Core.Schema)
    (node : WidePageTree.Node CoreWidePageState.Chunk) : Prop :=
  ∀ entry ∈ node.toList, ∀ row ∈ entry.2,
    CoreOverflow.RowInline schema row

theorem decodeChildrenFold (schema : Core.Schema)
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

theorem flatMap_node_rows
    (children : List (WidePageTree.Node CoreWidePageState.Chunk)) :
    children.flatMap CoreWidePageState.Node.rows =
      (children.flatMap WidePageTree.Node.toList).flatMap
        (fun entry => entry.2) := by
  induction children with
  | nil => rfl
  | cons child children induction =>
      simp only [List.flatMap_cons, CoreWidePageState.Node.rows]
      rw [List.flatMap_append, induction]

end CoreWidePageInverse

end SQLeanite
