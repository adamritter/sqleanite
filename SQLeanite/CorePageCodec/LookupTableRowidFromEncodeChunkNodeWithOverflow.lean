import SQLeanite.CoreDecode.DecodeAbstractTableTreeFromToList
import SQLeanite.CorePageCodec.EncodeChunkTablesWithOverflow

namespace SQLeanite
namespace CorePageCodec

/-- Exact point lookup for the live overflow-aware persistent table encoder.
The result covers both hits and valid misses and follows exactly one child at
each interior page. -/
theorem lookupTableRowidFrom_encodeChunkNodeWithOverflow
    (schema : Core.Schema) (source : CoreDecode.PageSource)
    (target : Core.Integer) :
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
      CoreDecode.lookupTableRowidFrom schema source target fuel node.rootId =
        some ((CoreChunkPageState.Node.rows node).find?
          fun row => row.rowid = target)
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
              rw [CoreDecode.lookupTableRowidFrom_succ]
              simp only [PersistentPageTree.Node.rootId]
              rw [rootRead]
              simp only
              rw [decodeTableInterior_tableLeafPage pageResult, decoded]
              rfl
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
              have leftLookup :=
                lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                  target left nextOverflow leftEncoding childFuel leftResult
                  leftTreeContains leftOverflowContains leftValid.rootValid
                  leftRowsValid leftPositive
                  (List.pairwise_append.mp childrenOrdered).1 (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  nextPositive
                  (by simp only [List.length_append] at pageBound; omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              have rightLookup :=
                lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                  target right leftEncoding.nextPage rightEncoding childFuel
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
              have leftRootPositive : 0 < left.rootId :=
                leftPositive left.rootId left.rootId_mem_pageIds
              rcases decodeTableInterior_encodeChunkRoot_branch2 schema pageId
                left separator right root leftRootPositive rootResult with
                ⟨boundary, boundaryLast, rootDecoded⟩
              have routing := findRowid_append_routed target boundary.rowid
                (CoreChunkPageState.Node.rows left)
                (CoreChunkPageState.Node.rows right) childrenOrdered
                (by rw [boundaryLast]; rfl)
              rw [CoreDecode.lookupTableRowidFrom_succ]
              simp only [PersistentPageTree.Node.rootId]
              rw [rootRead]
              simp only
              rw [rootDecoded]
              by_cases routed : target.value ≤ boundary.rowid.value
              · have findEqual := routing
                simp only [if_pos routed] at findEqual
                simpa [CoreDecode.tableChildForRowid, routed, leftLookup,
                  findRowid, CoreChunkPageState.Node.rows,
                  PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList, List.flatMap_append]
                  using congrArg some findEqual.symm
              · have findEqual := routing
                simp only [if_neg routed] at findEqual
                simpa [CoreDecode.tableChildForRowid, routed, rightLookup,
                  findRowid, CoreChunkPageState.Node.rows,
                  PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList, List.flatMap_append]
                  using congrArg some findEqual.symm
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
                have normalizedOverflow : CoreDecode.ReadsPagesFrom source
                    nextOverflow (leftEncoding.overflowPages ++
                      (middleEncoding.overflowPages ++
                        rightEncoding.overflowPages)) := by
                  simpa [List.append_assoc] using overflowContains
                have leftOverflowContains : CoreDecode.ReadsPagesFrom source
                    nextOverflow leftEncoding.overflowPages :=
                  CoreDecode.ReadsPagesFrom.left normalizedOverflow
                have afterLeft := CoreDecode.ReadsPagesFrom.right
                  normalizedOverflow
                have leftNext := encodeChunkNodeWithOverflow_nextPage schema left
                  nextOverflow leftEncoding leftResult
                have middleOverflowContains : CoreDecode.ReadsPagesFrom source
                    leftEncoding.nextPage middleEncoding.overflowPages := by
                  rw [leftNext]
                  exact CoreDecode.ReadsPagesFrom.left afterLeft
                have afterMiddle := CoreDecode.ReadsPagesFrom.right afterLeft
                have middleNext := encodeChunkNodeWithOverflow_nextPage schema
                  middle leftEncoding.nextPage middleEncoding middleResult
                have rightOverflowContains : CoreDecode.ReadsPagesFrom source
                    middleEncoding.nextPage rightEncoding.overflowPages := by
                  rw [middleNext, leftNext]
                  exact afterMiddle
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
                have firstSplit := List.pairwise_append.mp (show
                  (CoreChunkPageState.Node.rows left ++
                    (CoreChunkPageState.Node.rows middle ++
                      CoreChunkPageState.Node.rows right)).Pairwise
                        Core.Row.keyLess from by
                    simpa only [List.append_assoc] using childrenOrdered)
                have middleRightOrdered :
                    (CoreChunkPageState.Node.rows middle ++
                      CoreChunkPageState.Node.rows right).Pairwise
                        Core.Row.keyLess := firstSplit.2.1
                have secondSplit := List.pairwise_append.mp middleRightOrdered
                have leftLookup :=
                  lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                    target left nextOverflow leftEncoding childFuel leftResult
                    leftTreeContains leftOverflowContains leftValid.rootValid
                    leftRowsValid leftPositive firstSplit.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    nextPositive
                    (by simp only [List.length_append] at pageBound; omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have middleLookup :=
                  lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                    target middle leftEncoding.nextPage middleEncoding childFuel
                    middleResult middleTreeContains middleOverflowContains
                    middleValid.rootValid middleRowsValid middlePositive
                    secondSplit.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have rightLookup :=
                  lookupTableRowidFrom_encodeChunkNodeWithOverflow schema source
                    target right middleEncoding.nextPage rightEncoding childFuel
                    rightResult rightTreeContains rightOverflowContains
                    rightValid.rootValid rightRowsValid rightPositive
                    secondSplit.2.1 (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [middleNext, leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [middleNext, leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have leftRootPositive : 0 < left.rootId :=
                  leftPositive left.rootId left.rootId_mem_pageIds
                have middleRootPositive : 0 < middle.rootId :=
                  middlePositive middle.rootId middle.rootId_mem_pageIds
                rcases decodeTableInterior_encodeChunkRoot_branch3 schema pageId
                  left firstSeparator middle secondSeparator right root
                  leftRootPositive middleRootPositive rootResult with
                  ⟨leftBoundary, middleBoundary, leftLast, middleLast,
                    rootDecoded⟩
                have firstRouting := findRowid_append_routed target
                  leftBoundary.rowid (CoreChunkPageState.Node.rows left)
                  (CoreChunkPageState.Node.rows middle ++
                    CoreChunkPageState.Node.rows right)
                  (show (CoreChunkPageState.Node.rows left ++
                    (CoreChunkPageState.Node.rows middle ++
                      CoreChunkPageState.Node.rows right)).Pairwise
                        Core.Row.keyLess from by
                    simpa only [List.append_assoc] using childrenOrdered)
                  (by rw [leftLast]; rfl)
                have secondRouting := findRowid_append_routed target
                  middleBoundary.rowid (CoreChunkPageState.Node.rows middle)
                  (CoreChunkPageState.Node.rows right) middleRightOrdered
                  (by rw [middleLast]; rfl)
                rw [CoreDecode.lookupTableRowidFrom_succ]
                simp only [PersistentPageTree.Node.rootId]
                rw [rootRead]
                simp only
                rw [rootDecoded]
                by_cases leftRoute : target.value ≤ leftBoundary.rowid.value
                · have findEqual := firstRouting
                  simp only [if_pos leftRoute] at findEqual
                  simpa [CoreDecode.tableChildForRowid, leftRoute, leftLookup,
                    findRowid, CoreChunkPageState.Node.rows,
                    PersistentPageTree.Node.erase,
                    RecursiveBPlusTree.Node.toList, List.flatMap_append,
                    List.append_assoc] using congrArg some findEqual.symm
                · by_cases middleRoute :
                      target.value ≤ middleBoundary.rowid.value
                  · have firstEqual := firstRouting
                    simp only [if_neg leftRoute] at firstEqual
                    have secondEqual := secondRouting
                    simp only [if_pos middleRoute] at secondEqual
                    have findEqual := firstEqual.trans secondEqual
                    simpa [CoreDecode.tableChildForRowid, leftRoute,
                      middleRoute, middleLookup, findRowid,
                      CoreChunkPageState.Node.rows,
                      PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.flatMap_append,
                      List.append_assoc] using congrArg some findEqual.symm
                  · have firstEqual := firstRouting
                    simp only [if_neg leftRoute] at firstEqual
                    have secondEqual := secondRouting
                    simp only [if_neg middleRoute] at secondEqual
                    have findEqual := firstEqual.trans secondEqual
                    simpa [CoreDecode.tableChildForRowid, leftRoute,
                      middleRoute, rightLookup, findRowid,
                      CoreChunkPageState.Node.rows,
                      PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.toList, List.flatMap_append,
                      List.append_assoc] using congrArg some findEqual.symm

def orderNumberedPages (pages : List NumberedPage) : List NumberedPage :=
  pages.mergeSort (fun left right => left.pageNumber ≤ right.pageNumber)

theorem orderNumberedPages_eq_of_range {pages : List NumberedPage}
    {start count : Nat}
    (numbers : pages.map NumberedPage.pageNumber = List.range' start count) :
    orderNumberedPages pages = pages := by
  unfold orderNumberedPages
  apply List.mergeSort_of_pairwise
  apply (List.pairwise_map (f := NumberedPage.pageNumber)
    (R := fun left right : Nat => decide (left ≤ right) = true)).mp
  rw [numbers]
  exact List.pairwise_le_range'.imp fun less => by simpa using less

end CorePageCodec

end SQLeanite
