import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeIndexSubtreeFromEncodePagesFrom

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

/-- A proof-oriented certificate for the common integer-index case.  It says
more than shape validity: every stored/promoted value is an integer and each
child is bounded by the promoted entries around it.  REAL query targets are
handled conservatively by visiting every interval, so this certificate never
depends on an unproved mixed INTEGER/REAL ordering law. -/
inductive AbstractIndexTree.IntegerOrdered : AbstractIndexTree → Prop where
  | leaf (entries : List IndexEntry)
      (integers : ∀ entry ∈ entries, entry.IntegerValued) :
      IntegerOrdered (.leaf entries)
  | branch2 (left right : AbstractIndexTree) (separator : IndexEntry)
      (leftValid : left.IntegerOrdered) (rightValid : right.IntegerOrdered)
      (separatorInteger : separator.IntegerValued)
      (leftBefore : ∀ entry ∈ left.toList, entry.ValueLe separator)
      (rightAfter : ∀ entry ∈ right.toList, separator.ValueLe entry) :
      IntegerOrdered (.branch2 left separator right)
  | branch3 (left middle right : AbstractIndexTree)
      (firstSeparator secondSeparator : IndexEntry)
      (leftValid : left.IntegerOrdered)
      (middleValid : middle.IntegerOrdered)
      (rightValid : right.IntegerOrdered)
      (firstInteger : firstSeparator.IntegerValued)
      (secondInteger : secondSeparator.IntegerValued)
      (leftBefore : ∀ entry ∈ left.toList, entry.ValueLe firstSeparator)
      (middleAfter : ∀ entry ∈ middle.toList,
        firstSeparator.ValueLe entry)
      (middleBefore : ∀ entry ∈ middle.toList,
        entry.ValueLe secondSeparator)
      (rightAfter : ∀ entry ∈ right.toList,
        secondSeparator.ValueLe entry) :
      IntegerOrdered
        (.branch3 left firstSeparator middle secondSeparator right)

/-- Global in-order facts imply the local routing bounds carried by an
`IntegerOrdered` tree. This is the bridge from the encoder's sorted logical
sequence to the exact promoted-key topology decoded from its pages. -/
theorem AbstractIndexTree.IntegerOrdered.of_pairwise
    (tree : AbstractIndexTree)
    (integers : ∀ entry ∈ tree.toList, entry.IntegerValued)
    (ordered : tree.toList.Pairwise IndexEntry.ValueLe) :
    tree.IntegerOrdered := by
  induction tree with
  | leaf entries =>
      exact .leaf entries (by
        simpa [AbstractIndexTree.toList] using integers)
  | branch2 left separator right leftInduction rightInduction =>
      simp only [AbstractIndexTree.toList] at integers ordered
      have leftSeparatorRight := List.pairwise_append.mp ordered
      have leftSeparator := List.pairwise_append.mp leftSeparatorRight.1
      apply AbstractIndexTree.IntegerOrdered.branch2 left right separator
      · apply leftInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact leftSeparator.1
      · apply rightInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact leftSeparatorRight.2.1
      · exact integers separator (by simp)
      · intro entry member
        exact leftSeparator.2.2 entry member separator (by simp)
      · intro entry member
        exact leftSeparatorRight.2.2 separator (by simp) entry member
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [AbstractIndexTree.toList] at integers ordered
      have throughSecondRight := List.pairwise_append.mp ordered
      have throughMiddleSecond :=
        List.pairwise_append.mp throughSecondRight.1
      have leftFirstMiddle :=
        List.pairwise_append.mp throughMiddleSecond.1
      have leftFirst := List.pairwise_append.mp leftFirstMiddle.1
      apply AbstractIndexTree.IntegerOrdered.branch3 left middle right
        firstSeparator secondSeparator
      · apply leftInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact leftFirst.1
      · apply middleInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact leftFirstMiddle.2.1
      · apply rightInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact throughSecondRight.2.1
      · exact integers firstSeparator (by simp)
      · exact integers secondSeparator (by simp)
      · intro entry member
        exact leftFirst.2.2 entry member firstSeparator (by simp)
      · intro entry member
        exact leftFirstMiddle.2.2 firstSeparator (by simp) entry member
      · intro entry member
        exact throughMiddleSecond.2.2 entry (by simp [member]) secondSeparator
          (by simp)
      · intro entry member
        exact throughSecondRight.2.2 secondSeparator (by simp) entry member

structure AllCertificate {α : Type} (predicate : α → Prop)
    (values : List α) : Type where
  valid : ∀ value ∈ values, predicate value

def certifyAll {α : Type} (predicate : α → Prop)
    [DecidablePred predicate] :
    (values : List α) → Option (AllCertificate predicate values)
  | [] => some ⟨by simp⟩
  | value :: values => do
      if headValid : predicate value then
        let tailValid ← certifyAll predicate values
        some ⟨by
          intro candidate member
          rcases List.mem_cons.mp member with rfl | member
          · exact headValid
          · exact tailValid.valid candidate member⟩
      else none

structure AbstractIndexTree.IntegerOrderedCertificate
    (tree : AbstractIndexTree) : Type where
  valid : tree.IntegerOrdered

/-- A total proof-producing validator.  Success returns kernel evidence, not a
Boolean that later code must trust.  It is intentionally linear in the decoded
index and is suitable for connection-open certification; the cold-open plan
will replace that cost with persisted/authenticated provenance. -/
def AbstractIndexTree.certifyIntegerOrdered :
    (tree : AbstractIndexTree) → Option (IntegerOrderedCertificate tree)
  | .leaf entries => do
      let integers ← certifyAll IndexEntry.IntegerValued entries
      some ⟨.leaf entries integers.valid⟩
  | .branch2 left separator right => do
      let leftCertificate ← left.certifyIntegerOrdered
      let rightCertificate ← right.certifyIntegerOrdered
      if separatorInteger : separator.IntegerValued then
        let leftBefore ← certifyAll (·.ValueLe separator) left.toList
        let rightAfter ← certifyAll (separator.ValueLe ·) right.toList
        some ⟨.branch2 left right separator leftCertificate.valid
          rightCertificate.valid separatorInteger leftBefore.valid
          rightAfter.valid⟩
      else none
  | .branch3 left firstSeparator middle secondSeparator right => do
      let leftCertificate ← left.certifyIntegerOrdered
      let middleCertificate ← middle.certifyIntegerOrdered
      let rightCertificate ← right.certifyIntegerOrdered
      if firstInteger : firstSeparator.IntegerValued then
        if secondInteger : secondSeparator.IntegerValued then
          let leftBefore ← certifyAll (·.ValueLe firstSeparator) left.toList
          let middleAfter ← certifyAll (firstSeparator.ValueLe ·) middle.toList
          let middleBefore ← certifyAll (·.ValueLe secondSeparator) middle.toList
          let rightAfter ← certifyAll (secondSeparator.ValueLe ·) right.toList
          some ⟨.branch3 left middle right firstSeparator secondSeparator
            leftCertificate.valid middleCertificate.valid rightCertificate.valid
            firstInteger secondInteger leftBefore.valid middleAfter.valid
            middleBefore.valid rightAfter.valid⟩
        else none
      else none

theorem AbstractIndexTree.IntegerOrdered.allInteger {tree : AbstractIndexTree}
    (valid : tree.IntegerOrdered) :
    ∀ entry ∈ tree.toList, entry.IntegerValued := by
  induction valid with
  | leaf entries integers => simpa [AbstractIndexTree.toList] using integers
  | branch2 left right separator leftValid rightValid separatorInteger
      leftBefore rightAfter leftInduction rightInduction =>
      simp only [AbstractIndexTree.toList, List.mem_append, List.mem_singleton]
      intro entry member
      rcases member with (leftMember | equal) | rightMember
      · exact leftInduction entry leftMember
      · rw [equal]
        exact separatorInteger
      · exact rightInduction entry rightMember
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid firstInteger secondInteger leftBefore middleAfter
      middleBefore rightAfter leftInduction middleInduction rightInduction =>
      simp only [AbstractIndexTree.toList, List.mem_append, List.mem_singleton]
      intro entry member
      rcases member with
        (((leftMember | firstEqual) | middleMember) | secondEqual) | rightMember
      · exact leftInduction entry leftMember
      · rw [firstEqual]
        exact firstInteger
      · exact middleInduction entry middleMember
      · rw [secondEqual]
        exact secondInteger
      · exact rightInduction entry rightMember

private theorem integer_match_upper_admitted (entry upper : IndexEntry)
    (target : Core.Value) (entryInteger : entry.IntegerValued)
    (upperInteger : upper.IntegerValued) (before : entry.ValueLe upper)
    (matched : entry.matchesValue target = true) :
    indexUpperAllows target upper = true := by
  rcases entryInteger with ⟨entryValue, entryEqual⟩
  rcases upperInteger with ⟨upperValue, upperEqual⟩
  unfold IndexEntry.ValueLe at before
  unfold IndexEntry.matchesValue at matched
  unfold indexUpperAllows
  simp only [entryEqual, upperEqual] at before matched ⊢
  cases target <;>
    simp [PhysicalQuery.sqlEquals, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass] at matched before ⊢
  case integer targetValue =>
    subst targetValue
    exact before

private theorem integer_match_lower_admitted (lower entry : IndexEntry)
    (target : Core.Value) (lowerInteger : lower.IntegerValued)
    (entryInteger : entry.IntegerValued) (after : lower.ValueLe entry)
    (matched : entry.matchesValue target = true) :
    indexLowerAllows (some lower) target = true := by
  rcases lowerInteger with ⟨lowerValue, lowerEqual⟩
  rcases entryInteger with ⟨entryValue, entryEqual⟩
  unfold IndexEntry.ValueLe at after
  unfold IndexEntry.matchesValue at matched
  unfold indexLowerAllows
  simp only [lowerEqual, entryEqual] at after matched ⊢
  cases target <;>
    simp [PhysicalQuery.sqlEquals, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass] at matched after ⊢
  case integer targetValue =>
    subst targetValue
    exact after

theorem AbstractIndexTree.IntegerOrdered.wellRouted
    {tree : AbstractIndexTree} (valid : tree.IntegerOrdered) :
    tree.WellRouted := by
  induction valid with
  | leaf entries integers =>
      exact AbstractIndexTree.WellRouted.leaf entries
  | branch2 left right separator leftValid rightValid separatorInteger
      leftBefore rightAfter leftInduction rightInduction =>
      apply AbstractIndexTree.WellRouted.branch2 left right separator
        leftInduction rightInduction
      · intro target entry member matched
        exact integer_match_upper_admitted entry separator target
          (leftValid.allInteger entry member) separatorInteger
          (leftBefore entry member) matched
      · intro target entry member matched
        exact integer_match_lower_admitted separator entry target
          separatorInteger (rightValid.allInteger entry member)
          (rightAfter entry member) matched
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid firstInteger secondInteger leftBefore middleAfter
      middleBefore rightAfter leftInduction middleInduction rightInduction =>
      apply AbstractIndexTree.WellRouted.branch3 left middle right
        firstSeparator secondSeparator
        leftInduction middleInduction rightInduction
      · intro target entry member matched
        exact integer_match_upper_admitted entry firstSeparator target
          (leftValid.allInteger entry member) firstInteger
          (leftBefore entry member) matched
      · intro target entry member matched
        have lower := integer_match_lower_admitted firstSeparator entry target
          firstInteger (middleValid.allInteger entry member)
          (middleAfter entry member) matched
        have upper := integer_match_upper_admitted entry secondSeparator target
          (middleValid.allInteger entry member) secondInteger
          (middleBefore entry member) matched
        simp [lower, upper]
      · intro target entry member matched
        exact integer_match_lower_admitted secondSeparator entry target
          secondInteger (rightValid.allInteger entry member)
          (rightAfter entry member) matched

def IndexEntry.TextValued (entry : IndexEntry) : Prop :=
  ∃ value : PhysicalCodec.Text, entry.value = .text value

private theorem text_match_upper_admitted (entry upper : IndexEntry)
    (target : Core.Value) (entryText : entry.TextValued)
    (upperText : upper.TextValued) (before : entry.ValueLe upper)
    (matched : entry.matchesValue target = true) :
    indexUpperAllows target upper = true := by
  rcases entryText with ⟨entryValue, entryEqual⟩
  rcases upperText with ⟨upperValue, upperEqual⟩
  unfold IndexEntry.ValueLe at before
  unfold IndexEntry.matchesValue at matched
  unfold indexUpperAllows
  simp only [entryEqual, upperEqual] at before matched ⊢
  cases target <;>
    simp [PhysicalQuery.sqlEquals, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass] at matched before ⊢
  case text targetValue =>
    subst targetValue
    exact before

private theorem text_match_lower_admitted (lower entry : IndexEntry)
    (target : Core.Value) (lowerText : lower.TextValued)
    (entryText : entry.TextValued) (after : lower.ValueLe entry)
    (matched : entry.matchesValue target = true) :
    indexLowerAllows (some lower) target = true := by
  rcases lowerText with ⟨lowerValue, lowerEqual⟩
  rcases entryText with ⟨entryValue, entryEqual⟩
  unfold IndexEntry.ValueLe at after
  unfold IndexEntry.matchesValue at matched
  unfold indexLowerAllows
  simp only [lowerEqual, entryEqual] at after matched ⊢
  cases target <;>
    simp [PhysicalQuery.sqlEquals, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass] at matched after ⊢
  case text targetValue =>
    subst targetValue
    exact after

/-- A generated all-TEXT index is routed exactly by the same promoted keys
that occur in its in-order abstraction.  The proof consumes the encoder's
pairwise byte ordering; no reopen-time scan is needed. -/
theorem AbstractIndexTree.wellRouted_of_pairwise_text
    (tree : AbstractIndexTree)
    (texts : ∀ entry ∈ tree.toList, entry.TextValued)
    (ordered : tree.toList.Pairwise IndexEntry.ValueLe) :
    tree.WellRouted := by
  induction tree with
  | leaf entries => exact .leaf entries
  | branch2 left separator right leftInduction rightInduction =>
      simp only [AbstractIndexTree.toList] at texts ordered
      have leftSeparatorRight := List.pairwise_append.mp ordered
      have leftSeparator := List.pairwise_append.mp leftSeparatorRight.1
      apply AbstractIndexTree.WellRouted.branch2 left right separator
      · apply leftInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact leftSeparator.1
      · apply rightInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact leftSeparatorRight.2.1
      · intro target entry member matched
        exact text_match_upper_admitted entry separator target
          (texts entry (by simp [member])) (texts separator (by simp))
          (leftSeparator.2.2 entry member separator (by simp)) matched
      · intro target entry member matched
        exact text_match_lower_admitted separator entry target
          (texts separator (by simp)) (texts entry (by simp [member]))
          (leftSeparatorRight.2.2 separator (by simp) entry member) matched
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [AbstractIndexTree.toList] at texts ordered
      have throughSecondRight := List.pairwise_append.mp ordered
      have throughMiddleSecond :=
        List.pairwise_append.mp throughSecondRight.1
      have leftFirstMiddle :=
        List.pairwise_append.mp throughMiddleSecond.1
      have leftFirst := List.pairwise_append.mp leftFirstMiddle.1
      apply AbstractIndexTree.WellRouted.branch3 left middle right
        firstSeparator secondSeparator
      · apply leftInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact leftFirst.1
      · apply middleInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact leftFirstMiddle.2.1
      · apply rightInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact throughSecondRight.2.1
      · intro target entry member matched
        exact text_match_upper_admitted entry firstSeparator target
          (texts entry (by simp [member])) (texts firstSeparator (by simp))
          (leftFirst.2.2 entry member firstSeparator (by simp)) matched
      · intro target entry member matched
        have lower := text_match_lower_admitted firstSeparator entry target
          (texts firstSeparator (by simp)) (texts entry (by simp [member]))
          (leftFirstMiddle.2.2 firstSeparator (by simp) entry member) matched
        have upper := text_match_upper_admitted entry secondSeparator target
          (texts entry (by simp [member])) (texts secondSeparator (by simp))
          (throughMiddleSecond.2.2 entry (by simp [member]) secondSeparator
            (by simp)) matched
        simp [lower, upper]
      · intro target entry member matched
        exact text_match_lower_admitted secondSeparator entry target
          (texts secondSeparator (by simp)) (texts entry (by simp [member]))
          (throughSecondRight.2.2 secondSeparator (by simp) entry member)
          matched

theorem filter_matches_eq_nil_of_not_admitted
    (target : Core.Value) (entries : List IndexEntry) (allowed : Bool)
    (notAllowed : allowed = false)
    (admitted : ∀ entry, entry ∈ entries →
      entry.matchesValue target = true → allowed = true) :
    entries.filter (fun entry => entry.matchesValue target) = [] := by
  induction entries with
  | nil => rfl
  | cons entry entries induction =>
      have tailAdmitted : ∀ candidate, candidate ∈ entries →
          candidate.matchesValue target = true → allowed = true := by
        intro candidate member matched
        exact admitted candidate (by simp [member]) matched
      have tailEmpty := induction tailAdmitted
      by_cases matched : entry.matchesValue target = true
      · have contradiction := admitted entry (by simp) matched
        rw [notAllowed] at contradiction
        contradiction
      · simp [matched, tailEmpty]

end CoreDecode

end SQLeanite
