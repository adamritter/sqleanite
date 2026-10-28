import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeIndexLeafFromResolvedLeaf

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem decodeIndexSubtreeFrom_encodePagesFrom (source : PageSource) :
    ∀ (plan : RecursivePageBTree.IndexPlan) (start : Nat)
      (pages : List CoreFile.Page) (entries : List IndexEntry) (fuel : Nat),
      plan.encodePagesFrom start = some pages →
      ReadsPagesFrom source start pages →
      plan.Balanced →
      IndexPlanDecodes source (source.pageCount + 1) plan entries →
      plan.height < fuel →
      decodeIndexSubtreeFrom source fuel start = some entries
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
            simp only [decodeIndexSubtreeFrom]
            rw [rootRead]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [decodeIndexInteriorFrom_indexLeafPage source pageResult]
            exact decodeIndexLeafFrom_indexLeafPage source decoded pageResult
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
                have leftExact := decodeIndexSubtreeFrom_encodePagesFrom source
                  left leftStart leftPages _ childFuel leftResult leftReads
                  leftBalanced leftDecoded leftFuel
                have rightExact := decodeIndexSubtreeFrom_encodePagesFrom source
                  right rightStart rightPages _ childFuel rightResult rightReads
                  rightBalanced rightDecoded rightFuel
                simp only [decodeIndexSubtreeFrom]
                rw [rootRead]
                simp only [Option.bind_eq_bind, Option.bind]
                rw [decodeIndexInteriorFrom_indexInteriorPage_one source
                  separatorDecoded rootResult]
                simp only [List.mapM_cons, List.mapM_nil, pure, Pure.pure,
                  Option.bind_eq_bind, Option.bind]
                rw [leftExact, rightExact]
                simp
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
                  have leftExact := decodeIndexSubtreeFrom_encodePagesFrom
                    source left leftStart leftPages _ childFuel leftResult
                    leftReads leftBalanced leftDecoded leftFuel
                  have middleExact := decodeIndexSubtreeFrom_encodePagesFrom
                    source middle middleStart middlePages _ childFuel
                    middleResult middleReads middleBalanced middleDecoded
                    middleFuel
                  have rightExact := decodeIndexSubtreeFrom_encodePagesFrom
                    source right rightStart rightPages _ childFuel rightResult
                    rightReads rightBalanced rightDecoded rightFuel
                  simp only [decodeIndexSubtreeFrom]
                  rw [rootRead]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [decodeIndexInteriorFrom_indexInteriorPage_two source
                    firstDecoded secondDecoded rootResult]
                  simp only [List.mapM_cons, List.mapM_nil, pure, Pure.pure,
                    Option.bind_eq_bind, Option.bind]
                  rw [leftExact, middleExact, rightExact]
                  simp [List.append_assoc]

theorem decodeIndexSubtreeFrom_encodeIndex (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1) :
    decodeIndexSubtreeFrom source (source.pageCount + 1) rootPage =
      some ((CoreFile.sortedIndexRows table index).map fun row =>
        ⟨row.value index.column, row.rowid⟩) := by
  unfold CoreOverflow.encodeIndex at encoded
  cases plansResult : CoreOverflow.indexPlans table index with
  | none => simp [plansResult] at encoded
  | some plans =>
    simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
    cases provisionalResult : CoreOverflow.provisionalIndexStore? plans with
    | none => simp [provisionalResult] at encoded
    | some provisional =>
      simp only [provisionalResult] at encoded
      cases resolvedResult : CoreOverflow.resolvePlans
          (rootPage + provisional.plan.pageCount) plans with
      | none => simp [resolvedResult] at encoded
      | some resolved =>
        simp only [resolvedResult] at encoded
        cases updatedResult : provisional.retarget? resolved.cells with
        | none => simp [updatedResult] at encoded
        | some topology =>
          simp only [updatedResult] at encoded
          cases treeResult : topology.plan.encodePagesFrom rootPage with
          | none => simp [treeResult] at encoded
          | some treePages =>
            simp only [treeResult, Option.some.injEq] at encoded
            subst encoding
            have treeReads : ReadsPagesFrom source rootPage treePages :=
              ReadsPagesFrom.left reads
            have treeLength :=
              RecursivePageBTree.IndexPlan.encodePagesFrom_length treeResult
            have pageCountEqual :=
              RecursivePageBTree.IndexStore.retarget?_pageCount updatedResult
            have overflowReads : ReadsPagesFrom source
                (rootPage + provisional.plan.pageCount) resolved.pages := by
              have remaining := ReadsPagesFrom.right reads
              simpa [CoreOverflow.IndexEncoding.pages, treeLength,
                pageCountEqual] using remaining
            have planned : (CoreFile.sortedIndexRows table index).mapM
                (CoreOverflow.indexCellPlan? index) = some plans := by
              simpa [CoreOverflow.indexPlans] using plansResult
            have cellsDecoded := indexCellsDecode_resolvePlans index source
              (source.pageCount + 1) (CoreFile.sortedIndexRows table index)
              plans (rootPage + provisional.plan.pageCount) resolved planned
              resolvedResult (by omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at pageBound
                omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at withinSource
                omega)
              overflowReads
            have cellsEqual :=
              RecursivePageBTree.IndexStore.retarget?_represents updatedResult
            have planCells : IndexCellsDecode source (source.pageCount + 1)
                topology.plan.toCells
                ((CoreFile.sortedIndexRows table index).map fun row =>
                  ⟨row.value index.column, row.rowid⟩) := by
              rw [cellsEqual]
              exact cellsDecoded
            have planDecoded := IndexPlanDecodes.of_cells topology.plan _ planCells
            have balanced := topology.balanced
            have heightBound : topology.plan.height < source.pageCount + 1 := by
              have heightPageCount := topology.plan.height_lt_pageCount
              simp only [CoreOverflow.IndexEncoding.pages,
                List.length_append] at withinSource
              omega
            exact decodeIndexSubtreeFrom_encodePagesFrom source topology.plan rootPage
              treePages _ (source.pageCount + 1) treeResult treeReads balanced
              planDecoded heightBound

def IndexEntry.matchesValue (entry : IndexEntry) (target : Core.Value) : Bool :=
  PhysicalQuery.sqlEquals entry.value target = .true

def indexLowerAllows (lower : Option IndexEntry)
    (target : Core.Value) : Bool :=
  match target with
  | .realBits _ => true
  | _ => match lower with
      | none => true
      | some entry => PhysicalQuery.compareValue entry.value target != .gt

def indexUpperAllows (target : Core.Value) (upper : IndexEntry) : Bool :=
  match target with
  | .realBits _ => true
  | _ => PhysicalQuery.compareValue target upper.value != .gt

inductive AbstractIndexTree where
  | leaf (entries : List IndexEntry)
  | branch2 (left : AbstractIndexTree) (separator : IndexEntry)
      (right : AbstractIndexTree)
  | branch3 (left : AbstractIndexTree) (firstSeparator : IndexEntry)
      (middle : AbstractIndexTree) (secondSeparator : IndexEntry)
      (right : AbstractIndexTree)

def AbstractIndexTree.toList : AbstractIndexTree → List IndexEntry
  | .leaf entries => entries
  | .branch2 left separator right =>
      left.toList ++ [separator] ++ right.toList
  | .branch3 left firstSeparator middle secondSeparator right =>
      left.toList ++ [firstSeparator] ++ middle.toList ++
        [secondSeparator] ++ right.toList

/-- The pure meaning of the bounded physical prefix cursor. Unlike
`toList.take`, this definition exposes where traversal stops, so the effectful
reader can refine it without acquiring later children. -/
def AbstractIndexTree.cursorPrefix : Nat → AbstractIndexTree → List IndexEntry
  | 0, _ => []
  | limit + 1, .leaf entries => entries.take (limit + 1)
  | limit + 1, .branch2 left separator right =>
      let leftPrefix := left.cursorPrefix (limit + 1)
      if leftPrefix.length = limit + 1 then leftPrefix
      else leftPrefix ++ [separator] ++
        right.cursorPrefix (limit - leftPrefix.length)
  | limit + 1, .branch3 left firstSeparator middle secondSeparator right =>
      let leftPrefix := left.cursorPrefix (limit + 1)
      if leftPrefix.length = limit + 1 then leftPrefix
      else
        let middlePrefix := middle.cursorPrefix (limit - leftPrefix.length)
        let beforeRight := leftPrefix ++ [firstSeparator] ++ middlePrefix
        if beforeRight.length = limit + 1 then beforeRight
        else beforeRight ++ [secondSeparator] ++
          right.cursorPrefix (limit - beforeRight.length)

def AbstractIndexTree.leftmostLeaf : AbstractIndexTree → List IndexEntry
  | .leaf entries => entries
  | .branch2 left _ _ => left.leftmostLeaf
  | .branch3 left _ _ _ _ => left.leftmostLeaf

theorem AbstractIndexTree.leftmostLeaf_length_le (tree : AbstractIndexTree) :
    tree.leftmostLeaf.length ≤ tree.toList.length := by
  induction tree with
  | leaf entries => exact Nat.le_refl _
  | branch2 left separator right leftInduction rightInduction =>
      simp only [AbstractIndexTree.leftmostLeaf, AbstractIndexTree.toList,
        List.length_append, List.length_cons, List.length_nil]
      omega
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [AbstractIndexTree.leftmostLeaf, AbstractIndexTree.toList,
        List.length_append, List.length_cons, List.length_nil]
      omega

theorem AbstractIndexTree.take_toList_eq_take_leftmostLeaf
    (tree : AbstractIndexTree) (limit : Nat)
    (fits : limit ≤ tree.leftmostLeaf.length) :
    tree.toList.take limit = tree.leftmostLeaf.take limit := by
  induction tree with
  | leaf entries => rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp only [AbstractIndexTree.leftmostLeaf] at fits ⊢
      simp only [AbstractIndexTree.toList, List.append_assoc]
      rw [List.take_append_of_le_length
        (Nat.le_trans fits left.leftmostLeaf_length_le)]
      exact leftInduction fits
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [AbstractIndexTree.leftmostLeaf] at fits ⊢
      simp only [AbstractIndexTree.toList, List.append_assoc]
      rw [List.take_append_of_le_length
        (Nat.le_trans fits left.leftmostLeaf_length_le)]
      exact leftInduction fits

def AbstractIndexTree.equalityCandidates (target : Core.Value) :
    AbstractIndexTree → List IndexEntry
  | .leaf entries => entries
  | .branch2 left separator right =>
      (if indexUpperAllows target separator then
        left.equalityCandidates target else []) ++ [separator] ++
      (if indexLowerAllows (some separator) target then
        right.equalityCandidates target else [])
  | .branch3 left firstSeparator middle secondSeparator right =>
      (if indexUpperAllows target firstSeparator then
        left.equalityCandidates target else []) ++ [firstSeparator] ++
      (if indexLowerAllows (some firstSeparator) target &&
          indexUpperAllows target secondSeparator then
        middle.equalityCandidates target else []) ++ [secondSeparator] ++
      (if indexLowerAllows (some secondSeparator) target then
        right.equalityCandidates target else [])

inductive AbstractIndexTree.WellRouted : AbstractIndexTree → Prop where
  | leaf (entries : List IndexEntry) : WellRouted (.leaf entries)
  | branch2 (left right : AbstractIndexTree) (separator : IndexEntry)
      (leftValid : left.WellRouted) (rightValid : right.WellRouted)
      (leftAdmitted : ∀ target entry, entry ∈ left.toList →
        entry.matchesValue target = true →
        indexUpperAllows target separator = true)
      (rightAdmitted : ∀ target entry, entry ∈ right.toList →
        entry.matchesValue target = true →
        indexLowerAllows (some separator) target = true) :
      WellRouted (.branch2 left separator right)
  | branch3 (left middle right : AbstractIndexTree)
      (firstSeparator secondSeparator : IndexEntry)
      (leftValid : left.WellRouted) (middleValid : middle.WellRouted)
      (rightValid : right.WellRouted)
      (leftAdmitted : ∀ target entry, entry ∈ left.toList →
        entry.matchesValue target = true →
        indexUpperAllows target firstSeparator = true)
      (middleAdmitted : ∀ target entry, entry ∈ middle.toList →
        entry.matchesValue target = true →
        (indexLowerAllows (some firstSeparator) target &&
          indexUpperAllows target secondSeparator) = true)
      (rightAdmitted : ∀ target entry, entry ∈ right.toList →
        entry.matchesValue target = true →
        indexLowerAllows (some secondSeparator) target = true) :
      WellRouted
        (.branch3 left firstSeparator middle secondSeparator right)

def IndexEntry.IntegerValued (entry : IndexEntry) : Prop :=
  ∃ value : Core.Integer, entry.value = .integer value

instance (entry : IndexEntry) : Decidable entry.IntegerValued := by
  cases valueResult : entry.value with
  | integer value =>
      exact isTrue ⟨value, valueResult⟩
  | null | realBits | text | blob =>
      apply isFalse
      rintro ⟨value, equal⟩
      rw [valueResult] at equal
      contradiction

def IndexEntry.ValueLe (left right : IndexEntry) : Prop :=
  PhysicalQuery.compareValue left.value right.value ≠ .gt

instance (left right : IndexEntry) : Decidable (left.ValueLe right) := by
  unfold IndexEntry.ValueLe
  infer_instance

end CoreDecode

end SQLeanite
