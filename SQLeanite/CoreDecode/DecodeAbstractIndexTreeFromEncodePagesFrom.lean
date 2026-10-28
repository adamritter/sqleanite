import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.AbstractIndexTreeEqualityCandidatesExact

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

/-- Pages emitted from a refined balanced index plan decode to the same
promoted-key topology under the proof-oriented abstract decoder. Unlike the
flat decoder theorem, this retains the child boundaries needed by directed
lookups. -/
theorem decodeAbstractIndexTreeFrom_encodePagesFrom (source : PageSource) :
    ∀ (plan : RecursivePageBTree.IndexPlan) (start : Nat)
      (pages : List CoreFile.Page) (entries : List IndexEntry) (fuel : Nat),
      plan.encodePagesFrom start = some pages →
      ReadsPagesFrom source start pages →
      plan.Balanced →
      IndexPlanDecodes source (source.pageCount + 1) plan entries →
      plan.height < fuel →
      ∃ tree, decodeAbstractIndexTreeFrom source fuel start = some tree ∧
        tree.toList = entries
  | .leaf cells, start, pages, entries, fuel, encoded, reads, _, refined,
      fuelBound => by
      simp only [RecursivePageBTree.IndexPlan.encodePagesFrom,
        Option.bind_eq_bind, Option.bind] at encoded
      cases pageResult : CoreFile.indexLeafPage? cells with
      | none => simp [pageResult] at encoded
      | some page =>
        simp only [pageResult, Option.some.injEq] at encoded
        subst pages
        cases refined with
        | leaf decoded =>
          have rootRead : source.readPage start = some page.bytes := by
            have available := reads 0 (by simp)
            simpa using available
          cases fuel with
          | zero => simp [RecursivePageBTree.IndexPlan.height] at fuelBound
          | succ childFuel =>
            refine ⟨.leaf entries, ?_, by
              simp [AbstractIndexTree.toList]⟩
            simp only [decodeAbstractIndexTreeFrom]
            rw [rootRead]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [decodeIndexInteriorFrom_indexLeafPage source pageResult]
            rw [decodeIndexLeafFrom_indexLeafPage source decoded pageResult]
            rfl
  | .branch2 left separator right, start, pages, entries, fuel, encoded,
      reads, balanced, refined, fuelBound => by
      simp only [RecursivePageBTree.IndexPlan.encodePagesFrom,
        Option.bind_eq_bind, Option.bind] at encoded
      let leftStart := start + 1
      let rightStart := leftStart + left.pageCount
      cases rootResult : RecursivePageBTree.indexInteriorPage?
          [(leftStart, separator)] rightStart with
      | none => simp [leftStart, rightStart, rootResult] at encoded
      | some root =>
        simp only [leftStart, rightStart, rootResult] at encoded
        cases leftResult : left.encodePagesFrom (start + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases rightResult : right.encodePagesFrom
              (start + 1 + left.pageCount) with
          | none => simp [rightResult] at encoded
          | some rightPages =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst pages
            cases refined with
            | branch2 leftDecoded separatorDecoded rightDecoded =>
              rename_i leftEntries separatorEntry rightEntries
              simp only [RecursivePageBTree.IndexPlan.Balanced] at balanced
              rcases balanced with
                ⟨leftBalanced, rightBalanced, heightEqual⟩
              have rootRead : source.readPage start = some root.bytes := by
                have available := reads 0 (by simp)
                simpa using available
              have childrenReads : ReadsPagesFrom source leftStart
                  (leftPages ++ rightPages) := by
                have remaining := ReadsPagesFrom.right
                  (left := [root]) (right := leftPages ++ rightPages) reads
                simpa [leftStart] using remaining
              have leftReads : ReadsPagesFrom source leftStart leftPages :=
                ReadsPagesFrom.left childrenReads
              have leftLength :=
                RecursivePageBTree.IndexPlan.encodePagesFrom_length leftResult
              have rightReads : ReadsPagesFrom source rightStart rightPages := by
                have remaining := ReadsPagesFrom.right childrenReads
                simpa [rightStart, leftStart, leftLength] using remaining
              cases fuel with
              | zero =>
                simp [RecursivePageBTree.IndexPlan.height] at fuelBound
              | succ childFuel =>
                have leftFuel : left.height < childFuel := by
                  simp only [RecursivePageBTree.IndexPlan.height] at fuelBound
                  omega
                have rightFuel : right.height < childFuel := by
                  rw [← heightEqual]
                  exact leftFuel
                rcases decodeAbstractIndexTreeFrom_encodePagesFrom source left
                    leftStart leftPages _ childFuel leftResult leftReads
                    leftBalanced leftDecoded leftFuel with
                  ⟨leftTree, leftExact, leftContents⟩
                rcases decodeAbstractIndexTreeFrom_encodePagesFrom source right
                    rightStart rightPages _ childFuel rightResult rightReads
                    rightBalanced rightDecoded rightFuel with
                  ⟨rightTree, rightExact, rightContents⟩
                refine ⟨.branch2 leftTree separatorEntry rightTree, ?_, ?_⟩
                · simp only [decodeAbstractIndexTreeFrom]
                  rw [rootRead]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [decodeIndexInteriorFrom_indexInteriorPage_one source
                    separatorDecoded rootResult]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [leftExact, rightExact]
                · simp [AbstractIndexTree.toList, leftContents,
                    rightContents]
  | .branch3 left firstSeparator middle secondSeparator right, start, pages,
      entries, fuel, encoded, reads, balanced, refined, fuelBound => by
      simp only [RecursivePageBTree.IndexPlan.encodePagesFrom,
        Option.bind_eq_bind, Option.bind] at encoded
      let leftStart := start + 1
      let middleStart := leftStart + left.pageCount
      let rightStart := middleStart + middle.pageCount
      cases rootResult : RecursivePageBTree.indexInteriorPage?
          [(leftStart, firstSeparator), (middleStart, secondSeparator)]
          rightStart with
      | none =>
        simp [leftStart, middleStart, rightStart, rootResult] at encoded
      | some root =>
        simp only [leftStart, middleStart, rightStart, rootResult] at encoded
        cases leftResult : left.encodePagesFrom (start + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases middleResult : middle.encodePagesFrom
              (start + 1 + left.pageCount) with
          | none => simp [middleResult] at encoded
          | some middlePages =>
            simp only [middleResult] at encoded
            cases rightResult : right.encodePagesFrom
                (start + 1 + left.pageCount + middle.pageCount) with
            | none => simp [rightResult] at encoded
            | some rightPages =>
              simp only [rightResult, Option.some.injEq] at encoded
              subst pages
              cases refined with
              | branch3 leftDecoded firstDecoded middleDecoded secondDecoded
                  rightDecoded =>
                rename_i leftEntries firstEntry middleEntries secondEntry
                  rightEntries
                simp only [RecursivePageBTree.IndexPlan.Balanced] at balanced
                rcases balanced with
                  ⟨leftBalanced, middleBalanced, rightBalanced,
                    leftMiddleHeight, middleRightHeight⟩
                have rootRead : source.readPage start = some root.bytes := by
                  have available := reads 0 (by simp)
                  simpa using available
                have childrenReads : ReadsPagesFrom source leftStart
                    (leftPages ++ (middlePages ++ rightPages)) := by
                  have normalized : ReadsPagesFrom source start
                      ([root] ++ (leftPages ++ (middlePages ++ rightPages))) := by
                    simpa [List.append_assoc] using reads
                  have remaining := ReadsPagesFrom.right
                    (left := [root])
                    (right := leftPages ++ (middlePages ++ rightPages))
                    normalized
                  simpa [leftStart, List.append_assoc] using remaining
                have leftReads : ReadsPagesFrom source leftStart leftPages :=
                  ReadsPagesFrom.left childrenReads
                have afterLeftReads : ReadsPagesFrom source
                    (leftStart + leftPages.length)
                    (middlePages ++ rightPages) :=
                  ReadsPagesFrom.right childrenReads
                have leftLength :=
                  RecursivePageBTree.IndexPlan.encodePagesFrom_length leftResult
                have middleReads : ReadsPagesFrom source middleStart
                    middlePages := by
                  have middlePrefix := ReadsPagesFrom.left afterLeftReads
                  simpa [middleStart, leftStart, leftLength] using middlePrefix
                have afterMiddleReads : ReadsPagesFrom source
                    (leftStart + leftPages.length + middlePages.length)
                    rightPages := ReadsPagesFrom.right afterLeftReads
                have middleLength :=
                  RecursivePageBTree.IndexPlan.encodePagesFrom_length
                    middleResult
                have rightReads : ReadsPagesFrom source rightStart
                    rightPages := by
                  simpa [rightStart, middleStart, leftLength, middleLength,
                    Nat.add_assoc] using afterMiddleReads
                cases fuel with
                | zero =>
                  simp [RecursivePageBTree.IndexPlan.height] at fuelBound
                | succ childFuel =>
                  have leftFuel : left.height < childFuel := by
                    simp only [RecursivePageBTree.IndexPlan.height] at fuelBound
                    omega
                  have middleFuel : middle.height < childFuel := by
                    rw [← leftMiddleHeight]
                    exact leftFuel
                  have rightFuel : right.height < childFuel := by
                    rw [← middleRightHeight]
                    exact middleFuel
                  rcases decodeAbstractIndexTreeFrom_encodePagesFrom source left
                      leftStart leftPages _ childFuel leftResult leftReads
                      leftBalanced leftDecoded leftFuel with
                    ⟨leftTree, leftExact, leftContents⟩
                  rcases decodeAbstractIndexTreeFrom_encodePagesFrom source
                      middle middleStart middlePages _ childFuel middleResult
                      middleReads middleBalanced middleDecoded middleFuel with
                    ⟨middleTree, middleExact, middleContents⟩
                  rcases decodeAbstractIndexTreeFrom_encodePagesFrom source right
                      rightStart rightPages _ childFuel rightResult rightReads
                      rightBalanced rightDecoded rightFuel with
                    ⟨rightTree, rightExact, rightContents⟩
                  refine ⟨.branch3 leftTree firstEntry middleTree secondEntry
                    rightTree, ?_, ?_⟩
                  · simp only [decodeAbstractIndexTreeFrom]
                    rw [rootRead]
                    simp only [Option.bind_eq_bind, Option.bind]
                    rw [decodeIndexInteriorFrom_indexInteriorPage_two source
                      firstDecoded secondDecoded rootResult]
                    simp only [Option.bind_eq_bind, Option.bind]
                    rw [leftExact, middleExact, rightExact]
                  · simp [AbstractIndexTree.toList, leftContents,
                      middleContents, rightContents, List.append_assoc]

theorem decodeAbstractIndexTreeFrom_toList (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      decodeIndexSubtreeFrom source fuel pageNumber = some tree.toList
  | 0, _, _, decoded => by simp [decodeAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractIndexTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeIndexLeafFrom source page with
              | none => simp [leafResult] at decoded
              | some entries =>
                  rw [leafResult] at decoded
                  change some (.leaf entries) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [decodeIndexSubtreeFrom, pageResult, interiorResult,
                    leafResult, AbstractIndexTree.toList]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractIndexTreeFrom source fuel
                          leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractIndexTreeFrom source
                              fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftDecoded :=
                                decodeAbstractIndexTreeFrom_toList source fuel
                                  leftPage left leftResult
                              have rightDecoded :=
                                decodeAbstractIndexTreeFrom_toList source fuel
                                  rightPage right rightResult
                              simp [decodeIndexSubtreeFrom, pageResult,
                                interiorResult, leftDecoded, rightDecoded,
                                AbstractIndexTree.toList]
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractIndexTreeFrom source
                              fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractIndexTreeFrom
                                  source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult : decodeAbstractIndexTreeFrom
                                      source fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult, Option.some.injEq]
                                        at decoded
                                      subst tree
                                      have leftDecoded :=
                                        decodeAbstractIndexTreeFrom_toList source
                                          fuel leftPage left leftResult
                                      have middleDecoded :=
                                        decodeAbstractIndexTreeFrom_toList source
                                          fuel middlePage middle middleResult
                                      have rightDecoded :=
                                        decodeAbstractIndexTreeFrom_toList source
                                          fuel rightPage right rightResult
                                      simp [decodeIndexSubtreeFrom, pageResult,
                                        interiorResult, leftDecoded,
                                        middleDecoded, rightDecoded,
                                        AbstractIndexTree.toList,
                                        List.append_assoc]

/-- One equality traversal shared by the pure proof target and live IO reader.
Page acquisition and overflow decoding vary; interval routing, promoted
interior entries, and fuel accounting are definitionally the same code. -/
def indexValueCandidatesWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeInterior : List UInt8 →
      m (Option (List (Nat × IndexEntry) × Nat)))
    (decodeLeaf : List UInt8 → m (Option (List IndexEntry)))
    (target : Core.Value) : Nat → Nat → m (Option (List IndexEntry))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      let interior ← decodeInterior page
      match interior with
      | some (entries, rightmost) => do
          let lowers := none :: entries.map (fun entry => some entry.2)
          let groups ← (entries.zip lowers).mapM fun bounded => do
            let entry := bounded.1
            let lower := bounded.2
            let left ← if indexLowerAllows lower target &&
                indexUpperAllows target entry.2 then
              indexValueCandidatesWith readPage decodeInterior decodeLeaf target
                fuel entry.1
            else pure (some [])
            return left.map fun values => values ++ [entry.2]
          let visitRight := match entries.getLast? with
            | none => true
            | some entry => indexLowerAllows (some entry.2) target
          let right ← if visitRight then
            indexValueCandidatesWith readPage decodeInterior decodeLeaf target
              fuel rightmost
          else pure (some [])
          let some groups := sequenceOptions groups | return none
          let some right := right | return none
          return some (groups.flatten ++ right)
      | none => decodeLeaf page

/-- Page-directed equality traversal. Interior separators bound the child
subtrees by indexed value (inclusively because equal values are further ordered
by rowid), so unrelated children are never requested. The returned candidate
subtree is filtered separately below. -/
def indexValueCandidatesFrom (source : PageSource) (target : Core.Value)
    (fuel pageNumber : Nat) : Option (List IndexEntry) :=
  indexValueCandidatesWith (m := Id) source.readPage
    (decodeIndexInteriorFrom source) (decodeIndexLeafFrom source)
    target fuel pageNumber

def lookupIndexValueFrom (source : PageSource) (target : Core.Value)
    (fuel pageNumber : Nat) : Option (List IndexEntry) := do
  let candidates ← indexValueCandidatesFrom source target fuel pageNumber
  some (candidates.filter (fun entry => entry.matchesValue target))

/-- Every successful directed lookup contains only SQL-equal index entries.
Completeness is checked against the already validated index contents at the
live boundary until the interval proof is connected end to end. -/
theorem lookupIndexValueFrom_all_matches (source : PageSource)
    (target : Core.Value) (fuel pageNumber : Nat) (result : List IndexEntry)
    (success : lookupIndexValueFrom source target fuel pageNumber = some result) :
    result.all (fun entry => entry.matchesValue target) = true := by
  unfold lookupIndexValueFrom at success
  cases candidatesResult : indexValueCandidatesFrom source target fuel pageNumber with
  | none => simp [candidatesResult] at success
  | some candidates =>
      simp only [candidatesResult, Option.bind_eq_bind, Option.bind,
        Option.some.injEq] at success
      subst result
      simp [IndexEntry.matchesValue]

end CoreDecode

end SQLeanite
