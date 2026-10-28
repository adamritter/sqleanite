import SQLeanite.CoreDecode.DecodeAbstractTableTreeFromToList
import SQLeanite.CorePageCodec.EncodeChunkTablesWithOverflow

namespace SQLeanite
namespace CorePageCodec

/-- Full raw-page inverse for the store-owned tree with overflow payloads.
Tree pages are addressed by persistent identities; the separately allocated
overflow interval is split compositionally between recursive children. -/
theorem decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow
    (schema : Core.Schema) (source : CoreDecode.PageSource) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (nextOverflow : Nat) (encoding : OverflowEncoding) (fuel : Nat),
      encodeChunkNodeWithOverflow schema node nextOverflow = some encoding →
      PageSourceContains source encoding.treePages →
      CoreDecode.ReadsPagesFrom source nextOverflow encoding.overflowPages →
      node.erase.RootValid →
      (∀ entry ∈ node.erase.toList, ∀ row ∈ entry.2,
        row.WellFormed schema) →
      node.erase.height < fuel →
      0 < nextOverflow →
      nextOverflow + encoding.overflowPages.length < 2 ^ 32 →
      encoding.overflowPages.length < source.pageCount + 1 →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel node.rootId =
        some (CoreChunkPageState.Node.rows node)
  | .leaf pageId entries, nextOverflow, encoding, fuel, encoded, treeContains,
      overflowContains, _, valid, enough, nextPositive, pageBound, fuelBound => by
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
              unfold CoreDecode.decodeSubtreeRowsFrom
              simp only [PersistentPageTree.Node.rootId]
              rw [rootRead]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [interiorChildren_tableLeafPage pageResult, decoded]
              rfl
  | .branch2 pageId left separator right, nextOverflow, encoding, fuel,
      encoded, treeContains, overflowContains, rootValid, valid, enough,
      nextPositive, pageBound, fuelBound => by
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
              have leftDecoded :=
                decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                  left nextOverflow leftEncoding childFuel leftResult
                  leftTreeContains leftOverflowContains leftValid.rootValid
                  leftRowsValid (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  nextPositive
                  (by simp only [List.length_append] at pageBound; omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              have rightDecoded :=
                decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                  right leftEncoding.nextPage rightEncoding childFuel rightResult
                  rightTreeContains rightOverflowContains rightValid.rootValid
                  rightRowsValid (by
                    simp [PersistentPageTree.Node.erase,
                      RecursiveBPlusTree.Node.height] at enough
                    omega)
                  (by rw [leftNext]; omega)
                  (by
                    simp only [List.length_append] at pageBound
                    rw [leftNext]
                    omega)
                  (by simp only [List.length_append] at fuelBound; omega)
              unfold CoreDecode.decodeSubtreeRowsFrom
              simp only [PersistentPageTree.Node.rootId]
              rw [rootRead]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [interiorChildren_encodeChunkRoot_branch2 schema pageId left
                separator right root rootResult]
              simp [leftDecoded, rightDecoded, CoreChunkPageState.Node.rows,
                PersistentPageTree.Node.erase,
                RecursiveBPlusTree.Node.toList]
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      nextOverflow, encoding, fuel, encoded, treeContains, overflowContains,
      rootValid, valid, enough, nextPositive, pageBound, fuelBound => by
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
                  (leftEncoding.overflowPages ++
                    middleEncoding.overflowPages ++
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
                    leftEncoding.nextPage
                    (middleEncoding.overflowPages ++
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
                have leftDecoded :=
                  decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                    left nextOverflow leftEncoding childFuel leftResult
                    leftTreeContains leftOverflowContains leftValid.rootValid
                    leftRowsValid (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    nextPositive
                    (by simp only [List.length_append] at pageBound; omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have middleDecoded :=
                  decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                    middle leftEncoding.nextPage middleEncoding childFuel
                    middleResult middleTreeContains middleOverflowContains
                    middleValid.rootValid middleRowsValid (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                have rightDecoded :=
                  decodeSubtreeRowsFrom_encodeChunkNodeWithOverflow schema source
                    right middleEncoding.nextPage rightEncoding childFuel
                    rightResult rightTreeContains rightOverflowContains
                    rightValid.rootValid rightRowsValid (by
                      simp [PersistentPageTree.Node.erase,
                        RecursiveBPlusTree.Node.height] at enough
                      omega)
                    (by rw [middleNext, leftNext]; omega)
                    (by
                      simp only [List.length_append] at pageBound
                      rw [middleNext, leftNext]
                      omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                unfold CoreDecode.decodeSubtreeRowsFrom
                simp only [PersistentPageTree.Node.rootId]
                rw [rootRead]
                simp only [Option.bind_eq_bind, Option.bind]
                rw [interiorChildren_encodeChunkRoot_branch3 schema pageId left
                  firstSeparator middle secondSeparator right root rootResult]
                simp [leftDecoded, middleDecoded, rightDecoded,
                  CoreChunkPageState.Node.rows, PersistentPageTree.Node.erase,
                  RecursiveBPlusTree.Node.toList]

end CorePageCodec

end SQLeanite
