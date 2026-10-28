import SQLeanite.CorePageCodec.EncodeChunkTablesWithOverflow

namespace SQLeanite
namespace CorePageCodec

/-- The generated table encoder establishes the exact separator-routing
certificate consumed by the live primary-key range reader.  The statement
connects bytes, the persistent topology, logical in-order rows, and the
semantic no-skipped-match invariant in one refinement. -/
theorem decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow
    (schema : Core.Schema) (source : CoreDecode.PageSource) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (nextOverflow : Nat) (encoding : OverflowEncoding) (fuel : Nat),
      encodeChunkNodeWithOverflow schema node nextOverflow = some encoding →
      PageSourceContains source encoding.treePages →
      CoreDecode.ReadsPagesFrom source nextOverflow encoding.overflowPages →
      node.erase.RootValid →
      (∀ entry ∈ node.erase.toList, ∀ row ∈ entry.2,
        row.WellFormed schema) →
      (∀ pageId ∈ node.pageIds, 0 < pageId) →
      (CoreChunkPageState.Node.rows node).Pairwise Core.Row.keyLess →
      node.erase.height < fuel →
      0 < nextOverflow →
      nextOverflow + encoding.overflowPages.length < 2 ^ 32 →
      encoding.overflowPages.length < source.pageCount + 1 →
      ∃ tree,
        CoreDecode.decodeAbstractTableTreeFrom schema source fuel node.rootId =
          some tree ∧
        tree.toList = CoreChunkPageState.Node.rows node ∧
        tree.RangeWellRouted
  | .leaf pageId entries, nextOverflow, encoding, fuel, encoded, treeContains,
      overflowContains, _, valid, _, _, enough, nextPositive, pageBound,
      fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases plansResult :
          (entries.flatMap fun entry => entry.2).mapM
            (CoreOverflow.tableCellPlan? schema) with
      | none => simp [plansResult] at encoded
      | some plans =>
        simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
        cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
        | none => simp [resolvedResult] at encoded
        | some resolved =>
          simp only [resolvedResult] at encoded
          cases pageResult : CoreFile.tableLeafPage? resolved.cells with
          | none => simp [pageResult] at encoded
          | some page =>
            simp only [pageResult, Option.some.injEq] at encoded
            subst encoding
            cases fuel with
            | zero =>
              simp [PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.height] at enough
            | succ childFuel =>
              let rows := entries.flatMap fun entry => entry.2
              have rowsValid : ∀ row ∈ rows, row.WellFormed schema := by
                intro row member
                simp only [rows, List.mem_flatMap] at member
                rcases member with ⟨entry, entryMember, rowMember⟩
                exact valid entry (by simpa [PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList] using entryMember) row rowMember
              have rootRead : source.readPage pageId = some page.bytes :=
                treeContains ⟨pageId, page⟩ (by simp)
              have decoded := CoreDecode.decodeRowsFrom_resolvedLeaf schema source
                rows plans nextOverflow resolved page rowsValid
                (by simpa [rows] using plansResult) resolvedResult pageResult
                nextPositive (by simpa using pageBound)
                (by simpa using fuelBound) overflowContains
              refine ⟨CoreDecode.AbstractTableTree.leaf rows, ?_, rfl, ?_⟩
              · simp only [CoreDecode.decodeAbstractTableTreeFrom,
                  PersistentPageTree.Node.rootId]
                rw [rootRead]
                simp only [Option.bind_eq_bind, Option.bind]
                rw [decodeTableInterior_tableLeafPage pageResult, decoded]
                rfl
              · exact CoreDecode.AbstractTableTree.RangeWellRouted.leaf rows
  | .branch2 pageId left separator right, nextOverflow, encoding, fuel,
      encoded, treeContains, overflowContains, rootValid, valid, positive,
      ordered, enough, nextPositive, pageBound, fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left
            nextOverflow with
        | none => simp [leftResult] at encoded
        | some leftEncoding =>
          simp only [leftResult] at encoded
          cases rightResult : encodeChunkNodeWithOverflow schema right
              leftEncoding.nextPage with
          | none => simp [rightResult] at encoded
          | some rightEncoding =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst encoding
            cases fuel with
            | zero =>
              simp [PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.height] at enough
            | succ childFuel =>
              have rootNumber := encodeChunkRoot_pageNumber schema
                (.branch2 pageId left separator right) root rootResult
              have rootNumber' : root.pageNumber = pageId := by
                simpa [PersistentPageTree.Node.rootId] using rootNumber
              have rootRead : source.readPage pageId = some root.page.bytes := by
                rw [← rootNumber']
                exact treeContains root (by simp)
              have leftTreeContains :
                  PageSourceContains source leftEncoding.treePages := by
                intro numbered member
                exact treeContains numbered (by simp [member])
              have rightTreeContains :
                  PageSourceContains source rightEncoding.treePages := by
                intro numbered member
                exact treeContains numbered (by simp [member])
              have leftOverflowContains : CoreDecode.ReadsPagesFrom source
                  nextOverflow leftEncoding.overflowPages :=
                CoreDecode.ReadsPagesFrom.left overflowContains
              have leftNext := encodeChunkNodeWithOverflow_nextPage schema left
                nextOverflow leftEncoding leftResult
              have rightOverflowContains : CoreDecode.ReadsPagesFrom source
                  leftEncoding.nextPage rightEncoding.overflowPages := by
                rw [leftNext]
                exact CoreDecode.ReadsPagesFrom.right overflowContains
              rcases rootValid with
                ⟨leftValid, rightValid, heights, _, _⟩
              have leftRowsValid : ∀ entry ∈ left.erase.toList,
                  ∀ row ∈ entry.2, row.WellFormed schema := by
                intro entry member row rowMember
                exact valid entry (by
                  simp only [PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.mem_append]
                  exact Or.inl member) row rowMember
              have rightRowsValid : ∀ entry ∈ right.erase.toList,
                  ∀ row ∈ entry.2, row.WellFormed schema := by
                intro entry member row rowMember
                exact valid entry (by
                  simp only [PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.mem_append]
                  exact Or.inr member) row rowMember
              have leftPositive : ∀ id ∈ left.pageIds, 0 < id := by
                intro id member
                apply positive id
                simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                  List.mem_append]
                exact Or.inl (Or.inr member)
              have rightPositive : ∀ id ∈ right.pageIds, 0 < id := by
                intro id member
                apply positive id
                simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                  List.mem_append]
                exact Or.inr member
              have childrenOrdered :
                  (CoreChunkPageState.Node.rows left ++
                    CoreChunkPageState.Node.rows right).Pairwise
                      Core.Row.keyLess := by
                simpa [CoreChunkPageState.Node.rows,
                  PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList, List.flatMap_append]
                  using ordered
              have leftCertificate :=
                decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                  source left nextOverflow leftEncoding childFuel leftResult
                  leftTreeContains leftOverflowContains leftValid.rootValid
                  leftRowsValid leftPositive
                  (List.pairwise_append.mp childrenOrdered).1 (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  nextPositive
                  (by simp only [List.length_append] at pageBound; omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              have rightCertificate :=
                decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                  source right leftEncoding.nextPage rightEncoding childFuel
                  rightResult rightTreeContains rightOverflowContains
                  rightValid.rootValid rightRowsValid rightPositive
                  (List.pairwise_append.mp childrenOrdered).2.1 (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  (by rw [leftNext]; omega)
                  (by
                    simp only [List.length_append] at pageBound
                    rw [leftNext]
                    omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              rcases leftCertificate with
                ⟨leftTree, leftDecoded, leftContents, leftRouted⟩
              rcases rightCertificate with
                ⟨rightTree, rightDecoded, rightContents, rightRouted⟩
              have leftRootPositive : 0 < left.rootId :=
                leftPositive left.rootId left.rootId_mem_pageIds
              rcases decodeTableInterior_encodeChunkRoot_branch2 schema pageId
                left separator right root leftRootPositive rootResult with
                ⟨boundary, boundaryLast, rootDecoded⟩
              have boundaryMember : boundary ∈
                  CoreChunkPageState.Node.rows left := by
                rcases List.getLast?_eq_some_iff.mp boundaryLast with
                  ⟨front, equal⟩
                rw [equal]
                simp
              have splitOrdered := List.pairwise_append.mp childrenOrdered
              refine ⟨CoreDecode.AbstractTableTree.branch2 leftTree
                boundary.rowid rightTree, ?_, ?_, ?_⟩
              · simp only [CoreDecode.decodeAbstractTableTreeFrom,
                  PersistentPageTree.Node.rootId]
                rw [rootRead]
                simp only [Option.bind_eq_bind, Option.bind, rootDecoded,
                  leftDecoded, rightDecoded]
              · simp [CoreDecode.AbstractTableTree.toList, leftContents,
                  rightContents, CoreChunkPageState.Node.rows,
                  PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList, List.flatMap_append]
              · apply CoreDecode.AbstractTableTree.RangeWellRouted.branch2
                  leftTree rightTree boundary.rowid leftRouted rightRouted
                · intro operation target row member matched
                  apply CoreDecode.table_range_upper_admitted row boundary.rowid
                    operation target _ matched
                  exact rowid_le_of_pairwise_last splitOrdered.1 boundaryLast
                    row (by simpa [leftContents] using member)
                · intro operation target row member matched
                  apply CoreDecode.table_range_lower_admitted boundary.rowid row
                    operation target _ matched
                  have after := splitOrdered.2.2 boundary boundaryMember row
                    (by simpa [rightContents] using member)
                  simpa [Core.Row.keyLess] using after
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      nextOverflow, encoding, fuel, encoded, treeContains, overflowContains,
      rootValid, valid, positive, ordered, enough, nextPositive, pageBound,
      fuelBound => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left
            nextOverflow with
        | none => simp [leftResult] at encoded
        | some leftEncoding =>
          simp only [leftResult] at encoded
          cases middleResult : encodeChunkNodeWithOverflow schema middle
              leftEncoding.nextPage with
          | none => simp [middleResult] at encoded
          | some middleEncoding =>
            simp only [middleResult] at encoded
            cases rightResult : encodeChunkNodeWithOverflow schema right
                middleEncoding.nextPage with
            | none => simp [rightResult] at encoded
            | some rightEncoding =>
              simp only [rightResult, Option.some.injEq] at encoded
              subst encoding
              cases fuel with
              | zero =>
                simp [PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.height] at enough
              | succ childFuel =>
                change CoreDecode.ReadsPagesFrom source nextOverflow
                  (leftEncoding.overflowPages ++ middleEncoding.overflowPages ++
                    rightEncoding.overflowPages) at overflowContains
                have rootNumber := encodeChunkRoot_pageNumber schema
                  (.branch3 pageId left firstSeparator middle secondSeparator
                    right) root rootResult
                have rootNumber' : root.pageNumber = pageId := by
                  simpa [PersistentPageTree.Node.rootId] using rootNumber
                have rootRead : source.readPage pageId = some root.page.bytes := by
                  rw [← rootNumber']
                  exact treeContains root (by simp)
                have leftTreeContains :
                    PageSourceContains source leftEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                have middleTreeContains :
                    PageSourceContains source middleEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                have rightTreeContains :
                    PageSourceContains source rightEncoding.treePages := by
                  intro numbered member
                  exact treeContains numbered (by simp [member])
                rw [List.append_assoc] at overflowContains
                have leftOverflowContains : CoreDecode.ReadsPagesFrom source
                    nextOverflow leftEncoding.overflowPages :=
                  CoreDecode.ReadsPagesFrom.left overflowContains
                have leftNext := encodeChunkNodeWithOverflow_nextPage schema left
                  nextOverflow leftEncoding leftResult
                have afterLeft : CoreDecode.ReadsPagesFrom source
                    leftEncoding.nextPage (middleEncoding.overflowPages ++
                      rightEncoding.overflowPages) := by
                  rw [leftNext]
                  exact CoreDecode.ReadsPagesFrom.right overflowContains
                have middleOverflowContains : CoreDecode.ReadsPagesFrom source
                    leftEncoding.nextPage middleEncoding.overflowPages :=
                  CoreDecode.ReadsPagesFrom.left afterLeft
                have middleNext := encodeChunkNodeWithOverflow_nextPage schema
                  middle leftEncoding.nextPage middleEncoding middleResult
                have rightOverflowContains : CoreDecode.ReadsPagesFrom source
                    middleEncoding.nextPage rightEncoding.overflowPages := by
                  rw [middleNext]
                  exact CoreDecode.ReadsPagesFrom.right afterLeft
                rcases rootValid with
                  ⟨leftValid, middleValid, rightValid, leftHeight,
                    rightHeight, _, _, _, _⟩
                have leftRowsValid : ∀ entry ∈ left.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inl (Or.inl member)) row rowMember
                have middleRowsValid : ∀ entry ∈ middle.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inl (Or.inr member)) row rowMember
                have rightRowsValid : ∀ entry ∈ right.erase.toList,
                    ∀ row ∈ entry.2, row.WellFormed schema := by
                  intro entry member row rowMember
                  exact valid entry (by
                    simp only [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.mem_append]
                    exact Or.inr member) row rowMember
                have leftPositive : ∀ id ∈ left.pageIds, 0 < id := by
                  intro id member
                  apply positive id
                  simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                    List.mem_append]
                  exact Or.inl (Or.inl (Or.inr member))
                have middlePositive : ∀ id ∈ middle.pageIds, 0 < id := by
                  intro id member
                  apply positive id
                  simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                    List.mem_append]
                  exact Or.inl (Or.inr member)
                have rightPositive : ∀ id ∈ right.pageIds, 0 < id := by
                  intro id member
                  apply positive id
                  simp only [PersistentPageTree.Node.pageIds, List.mem_cons,
                    List.mem_append]
                  exact Or.inr member
                have childrenOrdered :
                    (CoreChunkPageState.Node.rows left ++
                      CoreChunkPageState.Node.rows middle ++
                      CoreChunkPageState.Node.rows right).Pairwise
                        Core.Row.keyLess := by
                  simpa [CoreChunkPageState.Node.rows,
                    PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.flatMap_append,
                    List.append_assoc] using ordered
                have groupedOrdered :
                    (CoreChunkPageState.Node.rows left ++
                      (CoreChunkPageState.Node.rows middle ++
                        CoreChunkPageState.Node.rows right)).Pairwise
                          Core.Row.keyLess := by
                  simpa [List.append_assoc] using childrenOrdered
                have splitLeft := List.pairwise_append.mp groupedOrdered
                have splitMiddle := List.pairwise_append.mp splitLeft.2.1
                have leftCertificate :=
                  decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                    source left nextOverflow leftEncoding childFuel leftResult
                    leftTreeContains leftOverflowContains leftValid.rootValid
                    leftRowsValid leftPositive splitLeft.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    nextPositive
                    (by simp only [List.length_append] at pageBound; omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have middleCertificate :=
                  decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                    source middle leftEncoding.nextPage middleEncoding childFuel
                    middleResult middleTreeContains middleOverflowContains
                    middleValid.rootValid middleRowsValid middlePositive
                    splitMiddle.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have rightCertificate :=
                  decodeAbstractTableTreeFrom_encodeChunkNodeWithOverflow schema
                    source right middleEncoding.nextPage rightEncoding childFuel
                    rightResult rightTreeContains rightOverflowContains
                    rightValid.rootValid rightRowsValid rightPositive
                    splitMiddle.2.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [middleNext, leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [middleNext, leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                rcases leftCertificate with
                  ⟨leftTree, leftDecoded, leftContents, leftRouted⟩
                rcases middleCertificate with
                  ⟨middleTree, middleDecoded, middleContents, middleRouted⟩
                rcases rightCertificate with
                  ⟨rightTree, rightDecoded, rightContents, rightRouted⟩
                have leftRootPositive : 0 < left.rootId :=
                  leftPositive left.rootId left.rootId_mem_pageIds
                have middleRootPositive : 0 < middle.rootId :=
                  middlePositive middle.rootId middle.rootId_mem_pageIds
                rcases decodeTableInterior_encodeChunkRoot_branch3 schema pageId
                  left firstSeparator middle secondSeparator right root
                  leftRootPositive middleRootPositive rootResult with
                  ⟨leftBoundary, middleBoundary, leftBoundaryLast,
                    middleBoundaryLast, rootDecoded⟩
                have leftBoundaryMember : leftBoundary ∈
                    CoreChunkPageState.Node.rows left := by
                  rcases List.getLast?_eq_some_iff.mp leftBoundaryLast with
                    ⟨front, equal⟩
                  rw [equal]
                  simp
                have middleBoundaryMember : middleBoundary ∈
                    CoreChunkPageState.Node.rows middle := by
                  rcases List.getLast?_eq_some_iff.mp middleBoundaryLast with
                    ⟨front, equal⟩
                  rw [equal]
                  simp
                refine ⟨CoreDecode.AbstractTableTree.branch3 leftTree
                  leftBoundary.rowid middleTree middleBoundary.rowid rightTree,
                  ?_, ?_, ?_⟩
                · simp only [CoreDecode.decodeAbstractTableTreeFrom,
                    PersistentPageTree.Node.rootId]
                  rw [rootRead]
                  simp only [Option.bind_eq_bind, Option.bind, rootDecoded,
                    leftDecoded, middleDecoded, rightDecoded]
                · simp [CoreDecode.AbstractTableTree.toList, leftContents,
                    middleContents, rightContents,
                    CoreChunkPageState.Node.rows,
                    PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.flatMap_append,
                    List.append_assoc]
                · apply CoreDecode.AbstractTableTree.RangeWellRouted.branch3
                    leftTree middleTree rightTree leftBoundary.rowid
                    middleBoundary.rowid leftRouted middleRouted rightRouted
                  · intro operation target row member matched
                    apply CoreDecode.table_range_upper_admitted row
                      leftBoundary.rowid operation target _ matched
                    exact rowid_le_of_pairwise_last splitLeft.1 leftBoundaryLast
                      row (by simpa [leftContents] using member)
                  · intro operation target row member matched
                    apply CoreDecode.table_range_middle_admitted
                      leftBoundary.rowid row middleBoundary.rowid operation target
                    · have after := splitLeft.2.2 leftBoundary
                          leftBoundaryMember row
                          (by
                            apply List.mem_append.mpr
                            exact Or.inl (by
                              simpa [middleContents] using member))
                      simpa [Core.Row.keyLess] using after
                    · exact rowid_le_of_pairwise_last splitMiddle.1
                        middleBoundaryLast row
                        (by simpa [middleContents] using member)
                    · exact matched
                  · intro operation target row member matched
                    apply CoreDecode.table_range_lower_admitted
                      middleBoundary.rowid row operation target _ matched
                    have after := splitMiddle.2.2 middleBoundary
                      middleBoundaryMember row
                      (by simpa [rightContents] using member)
                    simpa [Core.Row.keyLess] using after

end CorePageCodec

end SQLeanite
