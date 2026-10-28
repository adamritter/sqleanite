import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeAbstractIndexTreeFromEncodePagesFrom

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem indexValueCandidatesFrom_decodeAbstract (source : PageSource)
    (target : Core.Value) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      indexValueCandidatesFrom source target fuel pageNumber =
        some (tree.equalityCandidates target)
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
                  simp [indexValueCandidatesFrom, indexValueCandidatesWith,
                    pageResult, interiorResult, leafResult,
                    AbstractIndexTree.equalityCandidates]
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
                                indexValueCandidatesFrom_decodeAbstract source
                                  target fuel leftPage left leftResult
                              have rightCandidates :=
                                indexValueCandidatesFrom_decodeAbstract source
                                  target fuel rightPage right rightResult
                              have leftWith : indexValueCandidatesWith (m := Id)
                                  source.readPage (decodeIndexInteriorFrom source)
                                  (decodeIndexLeafFrom source) target fuel leftPage =
                                    some (left.equalityCandidates target) := by
                                simpa [indexValueCandidatesFrom] using
                                  leftCandidates
                              have rightWith : indexValueCandidatesWith (m := Id)
                                  source.readPage (decodeIndexInteriorFrom source)
                                  (decodeIndexLeafFrom source) target fuel rightPage =
                                    some (right.equalityCandidates target) := by
                                simpa [indexValueCandidatesFrom] using
                                  rightCandidates
                              have lowerNone :
                                  indexLowerAllows none target = true := by
                                cases target <;> rfl
                              by_cases leftAllowed :
                                indexUpperAllows target firstSeparator = true
                              <;> by_cases rightAllowed :
                                indexLowerAllows (some firstSeparator) target =
                                  true
                              <;> simp [indexValueCandidatesFrom,
                                indexValueCandidatesWith, pageResult,
                                interiorResult, leftWith, rightWith,
                                AbstractIndexTree.equalityCandidates,
                                leftAllowed, rightAllowed, sequenceOptions,
                                lowerNone, List.append_assoc]
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
                                        indexValueCandidatesFrom_decodeAbstract
                                          source target fuel leftPage left
                                          leftResult
                                      have middleCandidates :=
                                        indexValueCandidatesFrom_decodeAbstract
                                          source target fuel middlePage middle
                                          middleResult
                                      have rightCandidates :=
                                        indexValueCandidatesFrom_decodeAbstract
                                          source target fuel rightPage right
                                          rightResult
                                      have leftWith : indexValueCandidatesWith
                                          (m := Id)
                                          source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) target fuel
                                          leftPage = some
                                            (left.equalityCandidates target) := by
                                        simpa [indexValueCandidatesFrom] using
                                          leftCandidates
                                      have middleWith : indexValueCandidatesWith
                                          (m := Id)
                                          source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) target fuel
                                          middlePage = some
                                            (middle.equalityCandidates target) := by
                                        simpa [indexValueCandidatesFrom] using
                                          middleCandidates
                                      have rightWith : indexValueCandidatesWith
                                          (m := Id)
                                          source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) target fuel
                                          rightPage = some
                                            (right.equalityCandidates target) := by
                                        simpa [indexValueCandidatesFrom] using
                                          rightCandidates
                                      have lowerNone :
                                          indexLowerAllows none target = true :=
                                        by cases target <;> rfl
                                      by_cases leftAllowed : indexUpperAllows
                                        target firstSeparator = true
                                      <;> by_cases middleLowerAllowed :
                                        indexLowerAllows (some firstSeparator)
                                          target = true
                                      <;> by_cases middleUpperAllowed :
                                        indexUpperAllows target
                                          secondSeparator = true
                                      <;> by_cases rightAllowed :
                                        indexLowerAllows (some secondSeparator)
                                          target = true
                                      <;> simp [indexValueCandidatesFrom,
                                        indexValueCandidatesWith, pageResult,
                                        interiorResult, leftWith,
                                        middleWith, rightWith,
                                        AbstractIndexTree.equalityCandidates,
                                        leftAllowed, middleLowerAllowed,
                                        middleUpperAllowed, rightAllowed,
                                        lowerNone, sequenceOptions,
                                        List.append_assoc]

/-- Once the physical 2-3 tree decodes to a well-routed promoted-key tree,
directed equality lookup returns exactly the matching entries of that tree.
This removes the validating full scan from the theorem statement: every
interior record is part of the abstraction and every skipped subtree is
proved unable to contain a match. -/
theorem lookupIndexValueFrom_decodeAbstract_exact (source : PageSource)
    (target : Core.Value) (fuel pageNumber : Nat)
    (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (valid : tree.WellRouted) :
    lookupIndexValueFrom source target fuel pageNumber =
      some (tree.toList.filter (fun entry => entry.matchesValue target)) := by
  unfold lookupIndexValueFrom
  rw [indexValueCandidatesFrom_decodeAbstract source target fuel pageNumber tree
    decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [AbstractIndexTree.equalityCandidates_exact valid target]

/-- Byte-level refinement form of equality exactness.  Under the same decoded
routing certificate, the localized lookup agrees with filtering the complete
physical index decode. -/
theorem lookupIndexValueFrom_refines_full_decode (source : PageSource)
    (target : Core.Value) (fuel pageNumber : Nat)
    (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (valid : tree.WellRouted) :
    lookupIndexValueFrom source target fuel pageNumber =
      (decodeIndexSubtreeFrom source fuel pageNumber).map
        (List.filter (fun entry => entry.matchesValue target)) := by
  rw [lookupIndexValueFrom_decodeAbstract_exact source target fuel pageNumber
    tree decoded valid]
  rw [decodeAbstractIndexTreeFrom_toList source fuel pageNumber tree decoded]
  rfl

def IndexEntry.matchesRange (entry : IndexEntry)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) : Bool :=
  PhysicalQuery.sqlCompare operation entry.value target = .true

/-- Whether an index-value interval can contain a value satisfying a range
predicate. Bounds are inclusive because rowid is the secondary index key. -/
def indexRangeMayMatch (operation : PhysicalQuery.Comparison)
    (lower upper : Option IndexEntry) (target : Core.Value) : Bool :=
  match target with
  | .realBits _ => true
  | _ => match operation with
      | .less => match lower with
          | none => true
          | some entry => PhysicalQuery.compareValue entry.value target == .lt
      | .lessEqual => match lower with
          | none => true
          | some entry => PhysicalQuery.compareValue entry.value target != .gt
      | .greater => match upper with
          | none => true
          | some entry => PhysicalQuery.compareValue entry.value target == .gt
      | .greaterEqual => match upper with
          | none => true
          | some entry => PhysicalQuery.compareValue entry.value target != .lt

def AbstractIndexTree.rangeCandidates
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    AbstractIndexTree → List IndexEntry
  | .leaf entries => entries
  | .branch2 left separator right =>
      (if indexRangeMayMatch operation none (some separator) target then
        left.rangeCandidates operation target else []) ++ [separator] ++
      (if indexRangeMayMatch operation (some separator) none target then
        right.rangeCandidates operation target else [])
  | .branch3 left firstSeparator middle secondSeparator right =>
      (if indexRangeMayMatch operation none (some firstSeparator) target then
        left.rangeCandidates operation target else []) ++ [firstSeparator] ++
      (if indexRangeMayMatch operation (some firstSeparator)
          (some secondSeparator) target then
        middle.rangeCandidates operation target else []) ++ [secondSeparator] ++
      (if indexRangeMayMatch operation (some secondSeparator) none target then
        right.rangeCandidates operation target else [])

/-- Range-routing validity is deliberately semantic.  For every comparison
and target, a child containing a matching entry must be admitted by the same
interval test used by the executable traversal. -/
inductive AbstractIndexTree.RangeWellRouted : AbstractIndexTree → Prop where
  | leaf (entries : List IndexEntry) : RangeWellRouted (.leaf entries)
  | branch2 (left right : AbstractIndexTree) (separator : IndexEntry)
      (leftValid : left.RangeWellRouted) (rightValid : right.RangeWellRouted)
      (leftAdmitted : ∀ operation target entry, entry ∈ left.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation none (some separator) target = true)
      (rightAdmitted : ∀ operation target entry, entry ∈ right.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation (some separator) none target = true) :
      RangeWellRouted (.branch2 left separator right)
  | branch3 (left middle right : AbstractIndexTree)
      (firstSeparator secondSeparator : IndexEntry)
      (leftValid : left.RangeWellRouted)
      (middleValid : middle.RangeWellRouted)
      (rightValid : right.RangeWellRouted)
      (leftAdmitted : ∀ operation target entry, entry ∈ left.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation none (some firstSeparator) target = true)
      (middleAdmitted : ∀ operation target entry, entry ∈ middle.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation (some firstSeparator)
          (some secondSeparator) target = true)
      (rightAdmitted : ∀ operation target entry, entry ∈ right.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation (some secondSeparator) none target = true) :
      RangeWellRouted
        (.branch3 left firstSeparator middle secondSeparator right)

private theorem filter_range_eq_nil_of_not_admitted
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (entries : List IndexEntry) (allowed : Bool)
    (notAllowed : allowed = false)
    (admitted : ∀ entry, entry ∈ entries →
      entry.matchesRange operation target = true → allowed = true) :
    entries.filter (fun entry => entry.matchesRange operation target) = [] := by
  induction entries with
  | nil => rfl
  | cons entry entries induction =>
      have tailAdmitted : ∀ candidate, candidate ∈ entries →
          candidate.matchesRange operation target = true → allowed = true := by
        intro candidate member matched
        exact admitted candidate (by simp [member]) matched
      have tailEmpty := induction tailAdmitted
      by_cases matched : entry.matchesRange operation target = true
      · have contradiction := admitted entry (by simp) matched
        rw [notAllowed] at contradiction
        contradiction
      · simp [matched, tailEmpty]

theorem AbstractIndexTree.rangeCandidates_exact {tree : AbstractIndexTree}
    (valid : tree.RangeWellRouted) (operation : PhysicalQuery.Comparison)
    (target : Core.Value) :
    (tree.rangeCandidates operation target).filter
        (fun entry => entry.matchesRange operation target) =
      tree.toList.filter (fun entry => entry.matchesRange operation target) := by
  induction valid with
  | leaf entries => rfl
  | branch2 left right separator leftValid rightValid leftAdmitted
      rightAdmitted leftInduction rightInduction =>
      have leftExact :
          ((if indexRangeMayMatch operation none (some separator) target then
              left.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            left.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed :
            indexRangeMayMatch operation none (some separator) target with
        | true => simpa [allowed] using leftInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              left.toList _ allowed
              (fun entry member matched =>
                leftAdmitted operation target entry member matched)
            simp [allowed, empty]
      have rightExact :
          ((if indexRangeMayMatch operation (some separator) none target then
              right.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            right.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed :
            indexRangeMayMatch operation (some separator) none target with
        | true => simpa [allowed] using rightInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              right.toList _ allowed
              (fun entry member matched =>
                rightAdmitted operation target entry member matched)
            simp [allowed, empty]
      simp only [AbstractIndexTree.rangeCandidates,
        AbstractIndexTree.toList, List.filter_append]
      rw [leftExact, rightExact]
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid leftAdmitted middleAdmitted rightAdmitted
      leftInduction middleInduction rightInduction =>
      have leftExact :
          ((if indexRangeMayMatch operation none (some firstSeparator) target then
              left.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            left.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed : indexRangeMayMatch operation none
            (some firstSeparator) target with
        | true => simpa [allowed] using leftInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              left.toList _ allowed
              (fun entry member matched =>
                leftAdmitted operation target entry member matched)
            simp [allowed, empty]
      have middleExact :
          ((if indexRangeMayMatch operation (some firstSeparator)
              (some secondSeparator) target then
              middle.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            middle.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed : indexRangeMayMatch operation (some firstSeparator)
            (some secondSeparator) target with
        | true => simpa [allowed] using middleInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              middle.toList _ allowed
              (fun entry member matched =>
                middleAdmitted operation target entry member matched)
            simp [allowed, empty]
      have rightExact :
          ((if indexRangeMayMatch operation (some secondSeparator) none target then
              right.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            right.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed : indexRangeMayMatch operation (some secondSeparator)
            none target with
        | true => simpa [allowed] using rightInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              right.toList _ allowed
              (fun entry member matched =>
                rightAdmitted operation target entry member matched)
            simp [allowed, empty]
      simp only [AbstractIndexTree.rangeCandidates,
        AbstractIndexTree.toList, List.filter_append]
      rw [leftExact, middleExact, rightExact]

theorem integer_range_upper_admitted (entry upper : IndexEntry)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (entryInteger : entry.IntegerValued)
    (upperInteger : upper.IntegerValued) (before : entry.ValueLe upper)
    (matched : entry.matchesRange operation target = true) :
    indexRangeMayMatch operation none (some upper) target = true := by
  rcases entryInteger with ⟨entryValue, entryEqual⟩
  rcases upperInteger with ⟨upperValue, upperEqual⟩
  unfold IndexEntry.ValueLe at before
  unfold IndexEntry.matchesRange at matched
  simp only [entryEqual, upperEqual] at before matched ⊢
  cases operation <;> cases target <;>
    simp [indexRangeMayMatch, entryEqual, upperEqual,
      PhysicalQuery.sqlCompare,
      PhysicalQuery.Comparison.holds, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass, Int.compare_eq_lt,
      Int.compare_eq_gt] at matched before ⊢
  all_goals first | exact matched | omega

theorem integer_range_lower_admitted (lower entry : IndexEntry)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (lowerInteger : lower.IntegerValued)
    (entryInteger : entry.IntegerValued) (after : lower.ValueLe entry)
    (matched : entry.matchesRange operation target = true) :
    indexRangeMayMatch operation (some lower) none target = true := by
  rcases lowerInteger with ⟨lowerValue, lowerEqual⟩
  rcases entryInteger with ⟨entryValue, entryEqual⟩
  unfold IndexEntry.ValueLe at after
  unfold IndexEntry.matchesRange at matched
  simp only [lowerEqual, entryEqual] at after matched ⊢
  cases operation <;> cases target <;>
    simp [indexRangeMayMatch, lowerEqual, entryEqual,
      PhysicalQuery.sqlCompare,
      PhysicalQuery.Comparison.holds, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass, Int.compare_eq_lt,
      Int.compare_eq_gt] at matched after ⊢
  all_goals first | exact matched | omega

theorem integer_range_middle_admitted (lower entry upper : IndexEntry)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (lowerInteger : lower.IntegerValued)
    (entryInteger : entry.IntegerValued)
    (upperInteger : upper.IntegerValued)
    (after : lower.ValueLe entry) (before : entry.ValueLe upper)
    (matched : entry.matchesRange operation target = true) :
    indexRangeMayMatch operation (some lower) (some upper) target = true := by
  cases operation with
  | less =>
      exact integer_range_lower_admitted lower entry .less target
        lowerInteger entryInteger after matched
  | lessEqual =>
      exact integer_range_lower_admitted lower entry .lessEqual target
        lowerInteger entryInteger after matched
  | greater =>
      exact integer_range_upper_admitted entry upper .greater target
        entryInteger upperInteger before matched
  | greaterEqual =>
      exact integer_range_upper_admitted entry upper .greaterEqual target
        entryInteger upperInteger before matched

end CoreDecode

end SQLeanite
