import SQLeanite.RecursiveBPlusTree.NodeLookupOfMem

namespace SQLeanite
namespace RecursiveBPlusTree

/-- The complete recursive insertion invariant.  Besides preserving contents,
insertion preserves occupancy, sorted leaves, equal leaf depth, and every
separator bound.  A split returns two valid nodes at the original height with
an exact routing boundary between them. -/
theorem Node.insertStep_valid (node : Node Value) (valid : node.Valid)
    (key : Nat) (value : Value) :
    (node.insertStep key value).ValidAt node.height := by
  induction node with
  | leaf entries =>
      have sorted := PagedBTree.orderedInsert_sorted
        (key := key) (value := value) entries valid.2.1
      have lengthBound := orderedInsert_length_le entries key value
      have nonempty : PagedBTree.orderedInsert key value entries ≠ [] := by
        induction entries with
        | nil => simp [PagedBTree.orderedInsert]
        | cons entry entries induction =>
            simp only [PagedBTree.orderedInsert]
            split <;> try simp
            split <;> simp
      simp only [Node.insertStep]
      generalize updatedEq : PagedBTree.orderedInsert key value entries = updated
      rw [updatedEq] at sorted lengthBound nonempty
      cases updated with
      | nil => contradiction
      | cons first rest =>
        cases rest with
        | nil =>
            exact ⟨⟨by simp, by simp [PagedBTree.KeysStrictlySorted], by simp⟩,
              rfl⟩
        | cons second rest =>
          cases rest with
          | nil =>
              exact ⟨⟨by simp, sorted, by simp⟩, rfl⟩
          | cons third rest =>
            cases rest with
            | nil =>
              simp [PagedBTree.KeysStrictlySorted] at sorted
              rcases sorted with ⟨⟨firstSecond, firstThird⟩, secondThird⟩
              simp only [InsertResult.ValidAt, Node.Valid, Node.height,
                Node.toList, List.length_cons, List.length_nil]
              exact ⟨⟨by simp, by simp [PagedBTree.KeysStrictlySorted], by omega⟩,
                ⟨by simp, by simpa [PagedBTree.KeysStrictlySorted] using secondThird,
                  by omega⟩,
                trivial, trivial,
                by
                  intro entry member
                  simp only [List.mem_singleton] at member
                  subst entry
                  exact firstSecond,
                by intro entry member
                   simp only [List.mem_cons, List.mem_singleton] at member
                   rcases member with equal | tail
                   · subst entry
                     exact Nat.le_refl _
                   · rcases tail with equal | impossible
                     · subst entry
                       exact Nat.le_of_lt secondThird
                     · simp at impossible⟩
            | cons fourth rest =>
              simp only [Node.Valid] at valid
              simp only [List.length_cons, List.length_nil] at lengthBound
              omega
  | branch2 left separator right leftInduction rightInduction =>
      rcases valid with
        ⟨leftValid, rightValid, equalHeight, leftBefore, rightAfter⟩
      simp only [Node.insertStep]
      split
      next keyBefore =>
        have content := left.insertStep_toList leftValid.routes key value
        have upper : ∀ entry ∈ (left.insertStep key value).toList,
            entry.1 < separator := by
          intro entry member
          rw [content] at member
          exact all_orderedInsert (fun candidate => candidate.1 < separator)
            keyBefore leftBefore entry member
        have childResult := leftInduction leftValid
        cases inserted : left.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedValid, updatedHeight⟩
            simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at upper ⊢
            refine ⟨⟨updatedValid, rightValid,
              updatedHeight.trans equalHeight, upper, rightAfter⟩, ?_⟩
            simp [Node.height, updatedHeight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstValid, secondValid, firstHeight, secondHeight,
                firstBefore, secondAfter⟩
            have promotedBefore : promoted < separator := by
              obtain ⟨entry, member⟩ :=
                List.exists_mem_of_ne_nil second.toList secondValid.nonempty
              exact Nat.lt_of_le_of_lt (secondAfter entry member)
                (upper entry (by simp [inserted, InsertResult.toList, member]))
            simp only [inserted, InsertResult.ValidAt] at upper ⊢
            refine ⟨?_, ?_⟩
            · exact ⟨firstValid, secondValid, rightValid,
                firstHeight.trans secondHeight.symm,
                secondHeight.trans equalHeight, promotedBefore, firstBefore,
                (fun entry member => ⟨secondAfter entry member,
                  upper entry (by simp [InsertResult.toList, member])⟩),
                rightAfter⟩
            · simp [Node.height, firstHeight]
      next keyAfter =>
        have content := right.insertStep_toList rightValid.routes key value
        have lower : ∀ entry ∈ (right.insertStep key value).toList,
            separator ≤ entry.1 := by
          intro entry member
          rw [content] at member
          exact all_orderedInsert (fun candidate => separator ≤ candidate.1)
            (Nat.le_of_not_gt keyAfter) rightAfter entry member
        have childResult := rightInduction rightValid
        cases inserted : right.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedValid, updatedHeight⟩
            simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at lower ⊢
            refine ⟨⟨leftValid, updatedValid,
              equalHeight.trans updatedHeight.symm, leftBefore, lower⟩, rfl⟩
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstValid, secondValid, firstHeight, secondHeight,
                firstBefore, secondAfter⟩
            have separatorBefore : separator < promoted := by
              obtain ⟨entry, member⟩ :=
                List.exists_mem_of_ne_nil first.toList firstValid.nonempty
              exact Nat.lt_of_le_of_lt
                (lower entry (by simp [inserted, InsertResult.toList, member]))
                (firstBefore entry member)
            simp only [inserted, InsertResult.ValidAt] at lower ⊢
            refine ⟨?_, rfl⟩
            exact ⟨leftValid, firstValid, secondValid,
              equalHeight.trans firstHeight.symm,
              firstHeight.trans secondHeight.symm, separatorBefore, leftBefore,
              (fun entry member => ⟨
                lower entry (by simp [InsertResult.toList, member]),
                firstBefore entry member⟩), secondAfter⟩
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases valid with
        ⟨leftValid, middleValid, rightValid, leftMiddle, middleRight,
          separatorsOrdered, leftBefore, middleBetween, rightAfter⟩
      simp only [Node.insertStep]
      split
      next keyBefore =>
        have content := left.insertStep_toList leftValid.routes key value
        have upper : ∀ entry ∈ (left.insertStep key value).toList,
            entry.1 < firstSeparator := by
          intro entry member
          rw [content] at member
          exact all_orderedInsert (fun candidate => candidate.1 < firstSeparator)
            keyBefore leftBefore entry member
        have childResult := leftInduction leftValid
        cases inserted : left.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedValid, updatedHeight⟩
            simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at upper ⊢
            refine ⟨⟨updatedValid, middleValid, rightValid,
              updatedHeight.trans leftMiddle, middleRight, separatorsOrdered,
              upper, middleBetween, rightAfter⟩, ?_⟩
            simp [Node.height, updatedHeight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstValid, secondValid, firstHeight, secondHeight,
                firstBefore, secondAfter⟩
            simp only [inserted, InsertResult.ValidAt] at upper ⊢
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact ⟨firstValid, secondValid,
                firstHeight.trans secondHeight.symm, firstBefore, secondAfter⟩
            · exact ⟨middleValid, rightValid, middleRight,
                (fun entry member => (middleBetween entry member).2), rightAfter⟩
            · simp [Node.height, firstHeight]
            · simp [Node.height, leftMiddle]
            · intro entry member
              simp only [Node.toList, List.mem_append] at member
              rcases member with firstMember | secondMember
              · exact upper entry (by simp [InsertResult.toList, firstMember])
              · exact upper entry (by simp [InsertResult.toList, secondMember])
            · intro entry member
              simp only [Node.toList, List.mem_append] at member
              rcases member with middleMember | rightMember
              · exact (middleBetween entry middleMember).1
              · exact Nat.le_trans (Nat.le_of_lt separatorsOrdered)
                  (rightAfter entry rightMember)
      next notLeft =>
        split
        next beforeRight =>
          have content := middle.insertStep_toList middleValid.routes key value
          have lower : ∀ entry ∈ (middle.insertStep key value).toList,
              firstSeparator ≤ entry.1 := by
            intro entry member
            rw [content] at member
            exact all_orderedInsert
              (fun candidate => firstSeparator ≤ candidate.1)
              (Nat.le_of_not_gt notLeft)
              (fun entry member => (middleBetween entry member).1) entry member
          have upper : ∀ entry ∈ (middle.insertStep key value).toList,
              entry.1 < secondSeparator := by
            intro entry member
            rw [content] at member
            exact all_orderedInsert
              (fun candidate => candidate.1 < secondSeparator) beforeRight
              (fun entry member => (middleBetween entry member).2) entry member
          have childResult := middleInduction middleValid
          cases inserted : middle.insertStep key value with
          | done updated =>
              rw [inserted] at childResult
              rcases childResult with ⟨updatedValid, updatedHeight⟩
              simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at lower upper ⊢
              refine ⟨⟨leftValid, updatedValid, rightValid,
                leftMiddle.trans updatedHeight.symm,
                updatedHeight.trans middleRight, separatorsOrdered, leftBefore,
                (fun entry member => ⟨lower entry member, upper entry member⟩),
                rightAfter⟩, rfl⟩
          | split first promoted second =>
              rw [inserted] at childResult
              rcases childResult with
                ⟨firstValid, secondValid, firstHeight, secondHeight,
                  firstBefore, secondAfter⟩
              simp only [inserted, InsertResult.ValidAt] at lower upper ⊢
              have firstSeparatorBeforePromoted : firstSeparator < promoted := by
                obtain ⟨witness, witnessMember⟩ :=
                  List.exists_mem_of_ne_nil first.toList firstValid.nonempty
                exact Nat.lt_of_le_of_lt
                  (lower witness (by simp [InsertResult.toList, witnessMember]))
                  (firstBefore witness witnessMember)
              have promotedBeforeSecond : promoted < secondSeparator := by
                obtain ⟨witness, witnessMember⟩ :=
                  List.exists_mem_of_ne_nil second.toList secondValid.nonempty
                exact Nat.lt_of_le_of_lt (secondAfter witness witnessMember)
                  (upper witness (by simp [InsertResult.toList, witnessMember]))
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact ⟨leftValid, firstValid,
                  leftMiddle.trans firstHeight.symm, leftBefore,
                  fun entry member => lower entry
                    (by simp [InsertResult.toList, member])⟩
              · exact ⟨secondValid, rightValid,
                  secondHeight.trans middleRight, (fun entry member =>
                    upper entry (by simp [InsertResult.toList, member])), rightAfter⟩
              · rfl
              · exact congrArg (· + 1) (secondHeight.trans leftMiddle.symm)
              · intro entry member
                simp only [Node.toList, List.mem_append] at member
                rcases member with leftMember | firstMember
                · exact Nat.lt_trans (leftBefore entry leftMember)
                    firstSeparatorBeforePromoted
                · exact firstBefore entry firstMember
              · intro entry member
                simp only [Node.toList, List.mem_append] at member
                rcases member with secondMember | rightMember
                · exact secondAfter entry secondMember
                · exact Nat.le_trans (Nat.le_of_lt promotedBeforeSecond)
                    (rightAfter entry rightMember)
        next notMiddle =>
          have content := right.insertStep_toList rightValid.routes key value
          have lower : ∀ entry ∈ (right.insertStep key value).toList,
              secondSeparator ≤ entry.1 := by
            intro entry member
            rw [content] at member
            exact all_orderedInsert
              (fun candidate => secondSeparator ≤ candidate.1)
              (Nat.le_of_not_gt notMiddle) rightAfter entry member
          have childResult := rightInduction rightValid
          cases inserted : right.insertStep key value with
          | done updated =>
              rw [inserted] at childResult
              rcases childResult with ⟨updatedValid, updatedHeight⟩
              simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at lower ⊢
              refine ⟨⟨leftValid, middleValid, updatedValid, leftMiddle,
                middleRight.trans updatedHeight.symm, separatorsOrdered,
                leftBefore, middleBetween, lower⟩, rfl⟩
          | split first promoted second =>
              rw [inserted] at childResult
              rcases childResult with
                ⟨firstValid, secondValid, firstHeight, secondHeight,
                  firstBefore, secondAfter⟩
              simp only [inserted, InsertResult.ValidAt] at lower ⊢
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact ⟨leftValid, middleValid, leftMiddle, leftBefore,
                  fun entry member => (middleBetween entry member).1⟩
              · exact ⟨firstValid, secondValid,
                  firstHeight.trans secondHeight.symm, firstBefore, secondAfter⟩
              · rfl
              · exact congrArg (· + 1)
                  (firstHeight.trans (middleRight.symm.trans leftMiddle.symm))
              · intro entry member
                simp only [Node.toList, List.mem_append] at member
                rcases member with leftMember | middleMember
                · exact Nat.lt_trans (leftBefore entry leftMember)
                    separatorsOrdered
                · exact (middleBetween entry middleMember).2
              · intro entry member
                simp only [Node.toList, List.mem_append] at member
                rcases member with firstMember | secondMember
                · exact lower entry (by simp [InsertResult.toList, firstMember])
                · exact lower entry (by simp [InsertResult.toList, secondMember])

def Node.insert (node : Node Value) (key : Nat) (value : Value) : Node Value :=
  match node.insertStep key value with
  | .done updated => updated
  | .split left separator right => .branch2 left separator right

theorem Node.toList_insert (node : Node Value) (routes : node.Routes)
    (key : Nat) (value : Value) :
    (node.insert key value).toList =
      PagedBTree.orderedInsert key value node.toList := by
  have step := node.insertStep_toList routes key value
  unfold Node.insert
  cases inserted : node.insertStep key value with
  | done updated =>
      rw [inserted] at step
      simpa [InsertResult.toList] using step
  | split left separator right =>
      rw [inserted] at step
      simpa [InsertResult.toList, Node.toList] using step

theorem Node.insert_balanced (node : Node Value) (balanced : node.Balanced)
    (key : Nat) (value : Value) : (node.insert key value).Balanced := by
  have step := node.insertStep_balanced balanced key value
  unfold Node.insert
  cases inserted : node.insertStep key value with
  | done updated =>
      rw [inserted] at step
      exact step.1
  | split left separator right =>
      rw [inserted] at step
      rcases step with ⟨leftBalanced, rightBalanced, leftHeight, rightHeight⟩
      simp only [Node.Balanced]
      exact ⟨leftBalanced, rightBalanced, leftHeight.trans rightHeight.symm⟩

theorem Node.insert_rootValid_of_valid (node : Node Value) (valid : node.Valid)
    (key : Nat) (value : Value) : (node.insert key value).RootValid := by
  have step := node.insertStep_valid valid key value
  unfold Node.insert
  cases inserted : node.insertStep key value with
  | done updated =>
      rw [inserted] at step
      exact step.1.rootValid
  | split left separator right =>
      rw [inserted] at step
      rcases step with
        ⟨leftValid, rightValid, leftHeight, rightHeight, leftBefore, rightAfter⟩
      exact ⟨leftValid, rightValid, leftHeight.trans rightHeight.symm,
        leftBefore, rightAfter⟩

/-- Root validity is inductive from the empty tree through every insertion;
callers no longer need to assume the routing premise used by the raw
abstraction theorem. -/
theorem Node.insert_rootValid (node : Node Value) (valid : node.RootValid)
    (key : Nat) (value : Value) : (node.insert key value).RootValid := by
  cases node with
  | leaf entries =>
      by_cases empty : entries = []
      · subst entries
        simp [Node.insert, Node.insertStep, Node.RootValid,
          PagedBTree.orderedInsert, PagedBTree.KeysStrictlySorted]
      · exact Node.insert_rootValid_of_valid (.leaf entries)
          ⟨empty, valid.1, valid.2⟩ key value
  | branch2 left separator right =>
      exact Node.insert_rootValid_of_valid (.branch2 left separator right)
        valid key value
  | branch3 left firstSeparator middle secondSeparator right =>
      exact Node.insert_rootValid_of_valid
        (.branch3 left firstSeparator middle secondSeparator right)
        valid key value

theorem Node.toList_insert_rootValid (node : Node Value)
    (valid : node.RootValid) (key : Nat) (value : Value) :
    (node.insert key value).toList =
      PagedBTree.orderedInsert key value node.toList :=
  node.toList_insert valid.routes key value

def Node.insertAll (node : Node Value) (entries : List (Entry Value)) :
    Node Value :=
  entries.foldl (fun tree entry => tree.insert entry.1 entry.2) node

theorem Node.insertAll_rootValid (node : Node Value) (valid : node.RootValid) :
    (entries : List (Entry Value)) → (node.insertAll entries).RootValid
  | [] => valid
  | entry :: entries => by
      change ((node.insert entry.1 entry.2).insertAll entries).RootValid
      exact Node.insertAll_rootValid (node.insert entry.1 entry.2)
        (node.insert_rootValid valid entry.1 entry.2) entries

theorem Node.toList_insertAll (node : Node Value) (valid : node.RootValid) :
    (entries : List (Entry Value)) →
      (node.insertAll entries).toList =
        entries.foldl
          (fun contents entry =>
            PagedBTree.orderedInsert entry.1 entry.2 contents)
          node.toList
  | [] => rfl
  | entry :: entries => by
      change ((node.insert entry.1 entry.2).insertAll entries).toList = _
      rw [Node.toList_insertAll (node.insert entry.1 entry.2)
        (node.insert_rootValid valid entry.1 entry.2) entries]
      simp only [List.foldl_cons]
      rw [node.toList_insert_rootValid valid entry.1 entry.2]

private theorem orderedInsert_at_end (accumulated : List (Entry Value))
    (entry : Entry Value) (before : ∀ old ∈ accumulated, old.1 < entry.1) :
    PagedBTree.orderedInsert entry.1 entry.2 accumulated = accumulated ++ [entry] := by
  simpa [PagedBTree.orderedInsert] using orderedInsert_append_right entry.1 entry.2 accumulated [] before

private theorem fold_orderedInsert_append (accumulated : List (Entry Value)) :
    (suffix : List (Entry Value)) →
      PagedBTree.KeysStrictlySorted suffix →
      (∀ old ∈ accumulated, ∀ new ∈ suffix, old.1 < new.1) →
      suffix.foldl
          (fun contents entry =>
            PagedBTree.orderedInsert entry.1 entry.2 contents)
          accumulated = accumulated ++ suffix
  | [], _, _ => by simp
  | entry :: suffix, sorted, cross => by
      simp only [PagedBTree.KeysStrictlySorted, List.pairwise_cons] at sorted
      rw [List.foldl_cons, orderedInsert_at_end accumulated entry
        (fun old oldMember => cross old oldMember entry (by simp))]
      rw [fold_orderedInsert_append (accumulated ++ [entry]) suffix sorted.2]
      · simp [List.append_assoc]
      · intro old oldMember new newMember
        rw [List.mem_append] at oldMember
        rcases oldMember with oldMember | oldMember
        · exact cross old oldMember new (by simp [newMember])
        · simp only [List.mem_singleton] at oldMember
          subst old
          exact sorted.1 new newMember

theorem fold_orderedInsert_empty (entries : List (Entry Value))
    (sorted : PagedBTree.KeysStrictlySorted entries) :
    entries.foldl
        (fun contents entry =>
          PagedBTree.orderedInsert entry.1 entry.2 contents)
        [] = entries := by
  simpa using fold_orderedInsert_append ([] : List (Entry Value)) entries sorted
    (by simp)

/-- Deletion distinguishes a same-height result from an underflow propagated
to the parent.  This is the information the earlier `Option` deletion lacked
and is what permits local borrowing and merging without flattening the tree. -/
inductive DeleteResult (Value : Type) where
  | done (node : Node Value)
  | underflow (node : Node Value)
  | empty

def DeleteResult.toList : DeleteResult Value → List (Entry Value)
  | .done node | .underflow node => node.toList
  | .empty => []

def repairTwoLeft (separator : Nat) (deficit : Option (Node Value))
    (right : Node Value) : DeleteResult Value :=
  match deficit, right with
  | some under, .branch3 first firstSeparator middle secondSeparator last =>
      .done (.branch2 (.branch2 under separator first) firstSeparator
        (.branch2 middle secondSeparator last))
  | some under, .branch2 first middleSeparator last =>
      .underflow (.branch3 under separator first middleSeparator last)
  | some under, _ => .underflow (.branch2 under separator right)
  | none, _ => .underflow right

end RecursiveBPlusTree

end SQLeanite
