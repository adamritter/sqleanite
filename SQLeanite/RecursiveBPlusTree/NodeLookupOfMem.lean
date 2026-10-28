import SQLeanite.RecursiveBPlusTree.Entry

namespace SQLeanite
namespace RecursiveBPlusTree

/-- Lookup completeness for a valid routed tree. Together with
`lookup_some_mem`, this is the exact point-lookup refinement used by the live
primary-key access path. -/
theorem Node.lookup_of_mem {node : Node Value} {key : Nat} {value : Value}
    (valid : node.RootValid) (member : (key, value) ∈ node.toList) :
    node.lookup key = some value := by
  induction node with
  | leaf entries =>
      simp only [Node.RootValid] at valid
      simp only [Node.toList] at member
      unfold Node.lookup
      rw [findKey?_eq_some_of_mem valid.1 member]
      rfl
  | branch2 left separator right leftInduction rightInduction =>
      rcases valid with
        ⟨leftValid, rightValid, _, leftBefore, rightAfter⟩
      simp only [Node.toList, List.mem_append] at member
      rcases member with leftMember | rightMember
      · have routed := leftBefore (key, value) leftMember
        simp only [Node.lookup, if_pos routed]
        exact leftInduction leftValid.rootValid leftMember
      · have routed : ¬key < separator :=
          Nat.not_lt_of_ge (rightAfter (key, value) rightMember)
        simp only [Node.lookup, if_neg routed]
        exact rightInduction rightValid.rootValid rightMember
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases valid with
        ⟨leftValid, middleValid, rightValid, _, _, separatorsOrdered,
          leftBefore, middleBetween, rightAfter⟩
      simp only [Node.toList, List.mem_append] at member
      rcases member with (leftMember | middleMember) | rightMember
      · have routed := leftBefore (key, value) leftMember
        simp only [Node.lookup, if_pos routed]
        exact leftInduction leftValid.rootValid leftMember
      · have between := middleBetween (key, value) middleMember
        have notLeft : ¬key < firstSeparator := Nat.not_lt_of_ge between.1
        simp only [Node.lookup, if_neg notLeft, if_pos between.2]
        exact middleInduction middleValid.rootValid middleMember
      · have after := rightAfter (key, value) rightMember
        have notLeft : ¬key < firstSeparator :=
          Nat.not_lt_of_ge (Nat.le_trans
            (Nat.le_of_lt separatorsOrdered) after)
        have notMiddle : ¬key < secondSeparator := Nat.not_lt_of_ge after
        simp only [Node.lookup, if_neg notLeft, if_neg notMiddle]
        exact rightInduction rightValid.rootValid rightMember

theorem all_orderedInsert (predicate : Entry Value → Prop)
    (inserted : predicate (key, value))
    (old : ∀ entry ∈ entries, predicate entry) :
    ∀ entry ∈ PagedBTree.orderedInsert key value entries, predicate entry := by
  intro entry member
  rcases PagedBTree.mem_orderedInsert member with equal | previous
  · simpa [equal] using inserted
  · exact old entry previous

theorem orderedInsert_length_le (entries : List (Entry Value))
    (key : Nat) (value : Value) :
    (PagedBTree.orderedInsert key value entries).length ≤ entries.length + 1 := by
  induction entries with
  | nil => simp [PagedBTree.orderedInsert]
  | cons entry entries induction =>
      simp only [PagedBTree.orderedInsert]
      split
      next => simp
      next =>
        split
        next => simp only [List.length_cons]; omega
        next => simp

theorem orderedInsert_append_right (key : Nat) (value : Value) :
    ∀ (left right : List (Entry Value)),
      (∀ entry ∈ left, entry.1 < key) →
      PagedBTree.orderedInsert key value (left ++ right) =
        left ++ PagedBTree.orderedInsert key value right
  | [], _, _ => rfl
  | entry :: entries, right, before => by
      simp only [List.cons_append, PagedBTree.orderedInsert]
      rw [if_neg (Nat.not_lt_of_ge (Nat.le_of_lt (before entry (by simp))))]
      rw [if_pos (before entry (by simp))]
      simp only [List.cons_append, List.cons.injEq, true_and]
      exact orderedInsert_append_right key value entries right
        (fun candidate member => before candidate (by simp [member]))

private theorem orderedInsert_append_left (key : Nat) (value : Value) :
    ∀ (left right : List (Entry Value)),
      (∀ entry ∈ right, key < entry.1) →
      PagedBTree.orderedInsert key value (left ++ right) =
        PagedBTree.orderedInsert key value left ++ right
  | [], [], _ => rfl
  | [], entry :: entries, after => by
      simp [PagedBTree.orderedInsert, after entry (by simp)]
  | entry :: entries, right, after => by
      simp only [List.cons_append, PagedBTree.orderedInsert]
      split
      next keyBefore => rfl
      next notBefore =>
        split
        next entryBefore =>
          simp only [List.cons_append, List.cons.injEq, true_and]
          exact orderedInsert_append_left key value entries right after
        next notAfter => rfl

/-- Localized recursive insertion. A full leaf splits; a two-child interior
absorbs one propagated split; a full three-child interior splits and propagates
again. No flattening or whole-tree repagination occurs. -/
def Node.insertStep (key : Nat) (value : Value) :
    Node Value → InsertResult Value
  | .leaf entries =>
      match PagedBTree.orderedInsert key value entries with
      | [first, second, third] =>
          .split (.leaf [first]) second.1 (.leaf [second, third])
      | updated => .done (.leaf updated)
  | .branch2 left separator right =>
      if key < separator then
        match left.insertStep key value with
        | .done updated => .done (.branch2 updated separator right)
        | .split first promoted second =>
            .done (.branch3 first promoted second separator right)
      else
        match right.insertStep key value with
        | .done updated => .done (.branch2 left separator updated)
        | .split first promoted second =>
            .done (.branch3 left separator first promoted second)
  | .branch3 left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then
        match left.insertStep key value with
        | .done updated =>
            .done (.branch3 updated firstSeparator middle secondSeparator right)
        | .split first promoted second =>
            .split (.branch2 first promoted second) firstSeparator
              (.branch2 middle secondSeparator right)
      else if key < secondSeparator then
        match middle.insertStep key value with
        | .done updated =>
            .done (.branch3 left firstSeparator updated secondSeparator right)
        | .split first promoted second =>
            .split (.branch2 left firstSeparator first) promoted
              (.branch2 second secondSeparator right)
      else
        match right.insertStep key value with
        | .done updated =>
            .done (.branch3 left firstSeparator middle secondSeparator updated)
        | .split first promoted second =>
            .split (.branch2 left firstSeparator middle) secondSeparator
              (.branch2 first promoted second)

/-- Local insertion preserves bounded leaf occupancy and equal child heights.
A propagated split returns two balanced nodes at exactly the input height; a
completed insertion returns a balanced node whose height is unchanged. -/
theorem Node.insertStep_balanced (node : Node Value) (balanced : node.Balanced)
    (key : Nat) (value : Value) :
    (node.insertStep key value).BalancedAt node.height := by
  induction node with
  | leaf entries =>
      have lengthBound := orderedInsert_length_le entries key value
      simp only [Node.insertStep]
      generalize updatedEq : PagedBTree.orderedInsert key value entries = updated
      rw [updatedEq] at lengthBound
      cases updated with
      | nil => simp [InsertResult.BalancedAt, Node.Balanced, Node.height]
      | cons first rest =>
        cases rest with
        | nil => simp [InsertResult.BalancedAt, Node.Balanced, Node.height]
        | cons second rest =>
          cases rest with
          | nil => simp [InsertResult.BalancedAt, Node.Balanced, Node.height]
          | cons third rest =>
            cases rest with
            | nil => simp [InsertResult.BalancedAt, Node.Balanced, Node.height]
            | cons fourth rest =>
              simp only [Node.Balanced] at balanced
              simp only [List.length_cons, List.length_nil] at lengthBound
              omega
  | branch2 left separator right leftInduction rightInduction =>
      rcases balanced with ⟨leftBalanced, rightBalanced, equalHeight⟩
      simp only [Node.insertStep]
      split
      next =>
        have childResult := leftInduction leftBalanced
        cases inserted : left.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedBalanced, updatedHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              updatedBalanced, rightBalanced, updatedHeight, equalHeight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              firstBalanced, secondBalanced, rightBalanced, firstHeight,
              secondHeight, equalHeight]
      next =>
        have childResult := rightInduction rightBalanced
        cases inserted : right.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedBalanced, updatedHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              leftBalanced, updatedBalanced, updatedHeight, equalHeight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              leftBalanced, firstBalanced, secondBalanced, firstHeight,
              secondHeight, equalHeight]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases balanced with
        ⟨leftBalanced, middleBalanced, rightBalanced, leftMiddle, middleRight⟩
      simp only [Node.insertStep]
      split
      next =>
        have childResult := leftInduction leftBalanced
        cases inserted : left.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedBalanced, updatedHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              updatedBalanced, middleBalanced, rightBalanced, updatedHeight,
              leftMiddle, middleRight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              firstBalanced, secondBalanced, middleBalanced, rightBalanced,
              firstHeight, secondHeight, leftMiddle, middleRight]
      next =>
        split
        next =>
          have childResult := middleInduction middleBalanced
          cases inserted : middle.insertStep key value with
          | done updated =>
              rw [inserted] at childResult
              rcases childResult with ⟨updatedBalanced, updatedHeight⟩
              simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
                leftBalanced, updatedBalanced, rightBalanced, updatedHeight,
                leftMiddle, middleRight]
          | split first promoted second =>
              rw [inserted] at childResult
              rcases childResult with
                ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
              simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
                leftBalanced, firstBalanced, secondBalanced, rightBalanced,
                firstHeight, secondHeight, leftMiddle, middleRight]
        next =>
          have childResult := rightInduction rightBalanced
          cases inserted : right.insertStep key value with
          | done updated =>
              rw [inserted] at childResult
              rcases childResult with ⟨updatedBalanced, updatedHeight⟩
              simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
                leftBalanced, middleBalanced, updatedBalanced, updatedHeight,
                leftMiddle, middleRight]
          | split first promoted second =>
              rw [inserted] at childResult
              rcases childResult with
                ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
              simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
                leftBalanced, middleBalanced, firstBalanced, secondBalanced,
                firstHeight, secondHeight, leftMiddle, middleRight]

theorem Node.insertStep_toList (node : Node Value) (routes : node.Routes)
    (key : Nat) (value : Value) :
    (node.insertStep key value).toList =
      PagedBTree.orderedInsert key value node.toList := by
  induction node with
  | leaf entries =>
      simp only [Node.insertStep, Node.toList]
      generalize equal : PagedBTree.orderedInsert key value entries = updated
      cases updated with
      | nil => rfl
      | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
            cases rest <;> rfl
  | branch2 left separator right leftInduction rightInduction =>
      rcases routes with ⟨leftRoutes, rightRoutes, leftBefore, rightAfter⟩
      simp only [Node.insertStep]
      split
      next keyBefore =>
        have global := orderedInsert_append_left key value left.toList right.toList
          (fun entry member => Nat.lt_of_lt_of_le keyBefore
            (rightAfter entry member))
        cases inserted : left.insertStep key value with
        | done updated =>
          have localEq := leftInduction leftRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global]
        | split first promoted second =>
          have localEq := leftInduction leftRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global,
            List.append_assoc]
      next keyAfter =>
        have leftBeforeKey : ∀ entry ∈ left.toList, entry.1 < key := by
          intro entry member
          exact Nat.lt_of_lt_of_le (leftBefore entry member)
            (Nat.le_of_not_gt keyAfter)
        have global := orderedInsert_append_right key value left.toList right.toList
          leftBeforeKey
        cases inserted : right.insertStep key value with
        | done updated =>
          have localEq := rightInduction rightRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global]
        | split first promoted second =>
          have localEq := rightInduction rightRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global,
            List.append_assoc]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases routes with
        ⟨leftRoutes, middleRoutes, rightRoutes, separatorsOrdered, leftBefore,
          middleBetween, rightAfter⟩
      simp only [Node.insertStep]
      split
      next keyBefore =>
        have tailAfter : ∀ entry ∈ middle.toList ++ right.toList,
            key < entry.1 := by
          intro entry member
          simp only [List.mem_append] at member
          rcases member with middleMember | rightMember
          · exact Nat.lt_of_lt_of_le keyBefore
              (middleBetween entry middleMember).1
          · exact Nat.lt_of_lt_of_le
              (Nat.lt_trans keyBefore separatorsOrdered)
              (rightAfter entry rightMember)
        have global := orderedInsert_append_left key value left.toList
          (middle.toList ++ right.toList) tailAfter
        cases inserted : left.insertStep key value with
        | done updated =>
          have localEq := leftInduction leftRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global,
            List.append_assoc]
        | split first promoted second =>
          have localEq := leftInduction leftRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global,
            List.append_assoc]
      next notLeft =>
        split
        next beforeRight =>
          have leftBeforeKey : ∀ entry ∈ left.toList, entry.1 < key := by
            intro entry member
            exact Nat.lt_of_lt_of_le (leftBefore entry member)
              (Nat.le_of_not_gt notLeft)
          have rightAfterKey : ∀ entry ∈ right.toList, key < entry.1 := by
            intro entry member
            exact Nat.lt_of_lt_of_le beforeRight (rightAfter entry member)
          have first := orderedInsert_append_right key value left.toList
            (middle.toList ++ right.toList) leftBeforeKey
          have second := orderedInsert_append_left key value middle.toList
            right.toList rightAfterKey
          cases inserted : middle.insertStep key value with
          | done updated =>
            have localEq := middleInduction middleRoutes
            rw [inserted] at localEq
            simp only [InsertResult.toList] at localEq
            simp [inserted, InsertResult.toList, Node.toList, localEq, first,
              second, List.append_assoc]
          | split firstNode promoted secondNode =>
            have localEq := middleInduction middleRoutes
            rw [inserted] at localEq
            simp only [InsertResult.toList] at localEq
            simp [inserted, InsertResult.toList, Node.toList, localEq, first,
              second, List.append_assoc]
            rw [← List.append_assoc, localEq]
        next notMiddle =>
          have prefixBefore : ∀ entry ∈ left.toList ++ middle.toList,
              entry.1 < key := by
            intro entry member
            simp only [List.mem_append] at member
            rcases member with leftMember | middleMember
            · exact Nat.lt_of_lt_of_le (leftBefore entry leftMember)
                (Nat.le_of_not_gt notLeft)
            · exact Nat.lt_of_lt_of_le (middleBetween entry middleMember).2
                (Nat.le_of_not_gt notMiddle)
          have global := orderedInsert_append_right key value
            (left.toList ++ middle.toList) right.toList prefixBefore
          cases inserted : right.insertStep key value with
          | done updated =>
            have localEq := rightInduction rightRoutes
            rw [inserted] at localEq
            simp only [InsertResult.toList] at localEq
            simp [inserted, InsertResult.toList, Node.toList, localEq, global,
              List.append_assoc]
            simpa [List.append_assoc] using global.symm
          | split first promoted second =>
            have localEq := rightInduction rightRoutes
            rw [inserted] at localEq
            simp only [InsertResult.toList] at localEq
            simp [inserted, InsertResult.toList, Node.toList, localEq, global,
              List.append_assoc]
            simpa [List.append_assoc] using global.symm

end RecursiveBPlusTree

end SQLeanite
