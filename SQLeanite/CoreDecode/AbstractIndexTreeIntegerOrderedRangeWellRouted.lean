import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.IndexValueCandidatesFromDecodeAbstract
import SQLeanite.CoreDecode.LeftmostIndexLeafFromDecodeAbstract

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem AbstractIndexTree.IntegerOrdered.rangeWellRouted
    {tree : AbstractIndexTree} (valid : tree.IntegerOrdered) :
    tree.RangeWellRouted := by
  induction valid with
  | leaf entries integers =>
      exact AbstractIndexTree.RangeWellRouted.leaf entries
  | branch2 left right separator leftValid rightValid separatorInteger
      leftBefore rightAfter leftInduction rightInduction =>
      apply AbstractIndexTree.RangeWellRouted.branch2 left right separator
        leftInduction rightInduction
      · intro operation target entry member matched
        exact integer_range_upper_admitted entry separator operation target
          (leftValid.allInteger entry member) separatorInteger
          (leftBefore entry member) matched
      · intro operation target entry member matched
        exact integer_range_lower_admitted separator entry operation target
          separatorInteger (rightValid.allInteger entry member)
          (rightAfter entry member) matched
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid firstInteger secondInteger leftBefore middleAfter
      middleBefore rightAfter leftInduction middleInduction rightInduction =>
      apply AbstractIndexTree.RangeWellRouted.branch3 left middle right
        firstSeparator secondSeparator leftInduction middleInduction
        rightInduction
      · intro operation target entry member matched
        exact integer_range_upper_admitted entry firstSeparator operation target
          (leftValid.allInteger entry member) firstInteger
          (leftBefore entry member) matched
      · intro operation target entry member matched
        exact integer_range_middle_admitted firstSeparator entry secondSeparator
          operation target firstInteger
          (middleValid.allInteger entry member) secondInteger
          (middleAfter entry member) (middleBefore entry member) matched
      · intro operation target entry member matched
        exact integer_range_lower_admitted secondSeparator entry operation target
          secondInteger (rightValid.allInteger entry member)
          (rightAfter entry member) matched

/-- One range traversal shared by the pure proof target and live IO reader. -/
def indexRangeCandidatesWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeInterior : List UInt8 →
      m (Option (List (Nat × IndexEntry) × Nat)))
    (decodeLeaf : List UInt8 → m (Option (List IndexEntry)))
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    Nat → Nat → m (Option (List IndexEntry))
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
            let left ← if indexRangeMayMatch operation lower
                (some entry.2) target then
              indexRangeCandidatesWith readPage decodeInterior decodeLeaf
                operation target fuel entry.1
            else pure (some [])
            return left.map fun values => values ++ [entry.2]
          let lower := entries.getLast?.map (·.2)
          let right ← if indexRangeMayMatch operation lower none target then
            indexRangeCandidatesWith readPage decodeInterior decodeLeaf
              operation target fuel rightmost
          else pure (some [])
          let some groups := sequenceOptions groups | return none
          let some right := right | return none
          return some (groups.flatten ++ right)
      | none => decodeLeaf page

/-- Page-directed half-bounded range traversal over a persisted index. -/
def indexRangeCandidatesFrom (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) : Option (List IndexEntry) :=
  indexRangeCandidatesWith (m := Id) source.readPage
    (decodeIndexInteriorFrom source) (decodeIndexLeafFrom source)
    operation target fuel pageNumber

theorem indexRangeCandidatesFrom_decodeAbstract (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      indexRangeCandidatesFrom source operation target fuel pageNumber =
        some (tree.rangeCandidates operation target)
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
                  simp [indexRangeCandidatesFrom, indexRangeCandidatesWith,
                    pageResult, interiorResult, leafResult,
                    AbstractIndexTree.rangeCandidates]
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
                              have leftCandidates :=
                                indexRangeCandidatesFrom_decodeAbstract source
                                  operation target fuel leftPage left leftResult
                              have rightCandidates :=
                                indexRangeCandidatesFrom_decodeAbstract source
                                  operation target fuel rightPage right rightResult
                              have leftWith : indexRangeCandidatesWith (m := Id)
                                  source.readPage (decodeIndexInteriorFrom source)
                                  (decodeIndexLeafFrom source) operation target
                                  fuel leftPage = some
                                    (left.rangeCandidates operation target) := by
                                simpa [indexRangeCandidatesFrom] using
                                  leftCandidates
                              have rightWith : indexRangeCandidatesWith (m := Id)
                                  source.readPage (decodeIndexInteriorFrom source)
                                  (decodeIndexLeafFrom source) operation target
                                  fuel rightPage = some
                                    (right.rangeCandidates operation target) := by
                                simpa [indexRangeCandidatesFrom] using
                                  rightCandidates
                              by_cases leftAllowed : indexRangeMayMatch operation
                                none (some firstSeparator) target = true
                              <;> by_cases rightAllowed :
                                indexRangeMayMatch operation
                                  (some firstSeparator) none target = true
                              <;> simp [indexRangeCandidatesFrom,
                                indexRangeCandidatesWith, pageResult,
                                interiorResult, leftWith, rightWith,
                                AbstractIndexTree.rangeCandidates,
                                leftAllowed, rightAllowed, sequenceOptions,
                                List.append_assoc]
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
                                      have leftCandidates :=
                                        indexRangeCandidatesFrom_decodeAbstract
                                          source operation target fuel leftPage
                                          left leftResult
                                      have middleCandidates :=
                                        indexRangeCandidatesFrom_decodeAbstract
                                          source operation target fuel middlePage
                                          middle middleResult
                                      have rightCandidates :=
                                        indexRangeCandidatesFrom_decodeAbstract
                                          source operation target fuel rightPage
                                          right rightResult
                                      have leftWith : indexRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) operation
                                          target fuel leftPage = some
                                            (left.rangeCandidates operation
                                              target) := by
                                        simpa [indexRangeCandidatesFrom] using
                                          leftCandidates
                                      have middleWith : indexRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) operation
                                          target fuel middlePage = some
                                            (middle.rangeCandidates operation
                                              target) := by
                                        simpa [indexRangeCandidatesFrom] using
                                          middleCandidates
                                      have rightWith : indexRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) operation
                                          target fuel rightPage = some
                                            (right.rangeCandidates operation
                                              target) := by
                                        simpa [indexRangeCandidatesFrom] using
                                          rightCandidates
                                      by_cases leftAllowed :
                                        indexRangeMayMatch operation none
                                          (some firstSeparator) target = true
                                      <;> by_cases middleAllowed :
                                        indexRangeMayMatch operation
                                          (some firstSeparator)
                                          (some secondSeparator) target = true
                                      <;> by_cases rightAllowed :
                                        indexRangeMayMatch operation
                                          (some secondSeparator) none target =
                                            true
                                      <;> simp [indexRangeCandidatesFrom,
                                        indexRangeCandidatesWith, pageResult,
                                        interiorResult, leftWith, middleWith,
                                        rightWith,
                                        AbstractIndexTree.rangeCandidates,
                                        leftAllowed, middleAllowed, rightAllowed,
                                        sequenceOptions, List.append_assoc]

def lookupIndexRangeFrom (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) : Option (List IndexEntry) := do
  let candidates ←
    indexRangeCandidatesFrom source operation target fuel pageNumber
  some (candidates.filter (fun entry => entry.matchesRange operation target))

theorem lookupIndexRangeFrom_decodeAbstract_exact (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (valid : tree.RangeWellRouted) :
    lookupIndexRangeFrom source operation target fuel pageNumber =
      some (tree.toList.filter
        (fun entry => entry.matchesRange operation target)) := by
  unfold lookupIndexRangeFrom
  rw [indexRangeCandidatesFrom_decodeAbstract source operation target fuel
    pageNumber tree decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [AbstractIndexTree.rangeCandidates_exact valid operation target]

theorem lookupIndexRangeFrom_refines_full_decode (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (valid : tree.RangeWellRouted) :
    lookupIndexRangeFrom source operation target fuel pageNumber =
      (decodeIndexSubtreeFrom source fuel pageNumber).map
        (List.filter (fun entry => entry.matchesRange operation target)) := by
  rw [lookupIndexRangeFrom_decodeAbstract_exact source operation target fuel
    pageNumber tree decoded valid]
  rw [decodeAbstractIndexTreeFrom_toList source fuel pageNumber tree decoded]
  rfl

theorem lookupIndexRangeFrom_all_matches (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) (result : List IndexEntry)
    (success : lookupIndexRangeFrom source operation target fuel pageNumber =
      some result) :
    result.all (fun entry => entry.matchesRange operation target) = true := by
  unfold lookupIndexRangeFrom at success
  cases candidatesResult :
      indexRangeCandidatesFrom source operation target fuel pageNumber with
  | none => simp [candidatesResult] at success
  | some candidates =>
      simp only [candidatesResult, Option.bind_eq_bind, Option.bind,
        Option.some.injEq] at success
      subst result
      simp [IndexEntry.matchesRange]

def expectedIndexEntries (table : Core.Table) (index : Core.Index) :
    List IndexEntry :=
  (CoreFile.sortedIndexRows table index).map fun row =>
    ⟨row.value index.column, row.rowid⟩

theorem expectedIndexEntries_pairwise_valueLe (table : Core.Table)
    (index : Core.Index)
    (integers : CoreFile.indexValuesInteger table index = true) :
    (expectedIndexEntries table index).Pairwise IndexEntry.ValueLe := by
  unfold expectedIndexEntries
  rw [List.pairwise_map]
  change (CoreFile.sortedIndexRows table index).Pairwise (CoreFile.indexRowValueLe index)
  exact CoreFile.sortedIndexRows_pairwise_valueLe table index integers

theorem expectedIndexEntries_all_integer (table : Core.Table)
    (index : Core.Index)
    (integers : CoreFile.indexValuesInteger table index = true) :
    ∀ entry ∈ expectedIndexEntries table index, entry.IntegerValued := by
  intro entry member
  unfold expectedIndexEntries at member
  rcases List.mem_map.mp member with ⟨row, rowMember, rfl⟩
  have sourceMember : row ∈ table.rows :=
    (CoreFile.sortedIndexRows_perm table index).subset rowMember
  rcases (CoreFile.indexValuesInteger_iff table index).mp integers row
      sourceMember with ⟨value, valueEqual⟩
  exact ⟨value, valueEqual⟩

theorem expectedIndexEntries_pairwise_valueLe_text (table : Core.Table)
    (index : Core.Index)
    (texts : CoreFile.indexValuesText table index = true) :
    (expectedIndexEntries table index).Pairwise IndexEntry.ValueLe := by
  unfold expectedIndexEntries
  rw [List.pairwise_map]
  change (CoreFile.sortedIndexRows table index).Pairwise (CoreFile.indexRowValueLe index)
  exact CoreFile.sortedIndexRows_pairwise_valueLe_text table index texts

theorem expectedIndexEntries_all_text (table : Core.Table)
    (index : Core.Index)
    (texts : CoreFile.indexValuesText table index = true) :
    ∀ entry ∈ expectedIndexEntries table index, entry.TextValued := by
  intro entry member
  unfold expectedIndexEntries at member
  rcases List.mem_map.mp member with ⟨row, rowMember, rfl⟩
  have sourceMember : row ∈ table.rows :=
    (CoreFile.sortedIndexRows_perm table index).subset rowMember
  rcases (CoreFile.indexValuesText_iff table index).mp texts row
      sourceMember with ⟨value, valueEqual⟩
  exact ⟨value, valueEqual⟩

@[simp] theorem expectedIndexEntries_withoutIndexes (table : Core.Table)
    (index : Core.Index) :
    expectedIndexEntries table.withoutIndexes index =
      expectedIndexEntries table index := by
  unfold expectedIndexEntries CoreFile.sortedIndexRows
  simp [CoreFile.indexValuesInteger, CoreFile.indexValuesText,
    Core.Table.withoutIndexes_rows, Core.Table.withoutIndexes_catalogSource]

/-- A reopened index certificate ties the bytes, promoted-key topology,
routing invariant, and logical Core index contents together.  Constructing it
is a pure checked operation; consumers receive all premises required by the
localized exactness theorems as proof fields. -/
structure CertifiedIntegerIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree
  ordered : tree.IntegerOrdered
  contents : tree.toList = expected

structure CertifiedTextIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree
  routed : tree.WellRouted
  contents : tree.toList = expected

/-- Reopen-time certificate for general-arity SQLite index pages. It has the
same semantic payload as `CertifiedIntegerIndex`; only the decoder provenance
differs. -/
structure CertifiedWideIntegerIndex (source : PageSource)
    (fuel pageNumber : Nat) (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree
  ordered : tree.IntegerOrdered
  contents : tree.toList = expected

/-- General-arity TEXT indexes retain their promoted-key routing proof too.
Unlike `CertifiedAllValueIndex`, equality lookup can therefore discard every
unrelated subtree instead of filtering the complete retained abstraction. -/
structure CertifiedWideTextIndex (source : PageSource)
    (fuel pageNumber : Nat) (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree
  routed : tree.WellRouted
  contents : tree.toList = expected

/-- Exact reopen certificate for indexes whose storage classes do not satisfy
the INTEGER routing invariant. Queries filter the retained physical index
abstraction directly; this removes the duplicate logical-plan validation while
remaining deliberately conservative about mixed numeric interval pruning. -/
structure CertifiedAllValueIndex (source : PageSource)
    (fuel pageNumber : Nat) (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree
  contents : tree.toList = expected

end CoreDecode

end SQLeanite
