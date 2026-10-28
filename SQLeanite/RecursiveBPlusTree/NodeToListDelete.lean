import SQLeanite.RecursiveBPlusTree.RepairTwoRight

namespace SQLeanite
namespace RecursiveBPlusTree

theorem Node.toList_delete (node : Node Value) (valid : node.RootValid)
    (key : Nat) :
    (node.delete key).toList =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  have localized := node.toList_deleteBalanced valid.routes key
  have filteredSorted :
      PagedBTree.KeysStrictlySorted
        (node.toList.filter (fun entry => entry.1 ≠ key)) :=
    valid.sorted.filter _
  simp only [Node.delete]
  split
  next => exact localized
  next =>
    rw [Node.toList_insertAll]
    · simp only [Node.toList]
      exact fold_orderedInsert_empty _ filteredSorted
    · simp [Node.RootValid, PagedBTree.KeysStrictlySorted]

/-- Local deletion has the exact abstract effect of removing the requested
key.  The proof follows the same routed child as the implementation and uses
the routing bounds to show that every untouched sibling is unchanged by the
abstract filter. -/
theorem Node.deleteStep_toList (node : Node Value) (routes : node.Routes)
    (key : Nat) :
    Node.deletedList (node.deleteStep key) =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  induction node with
  | leaf entries =>
      simp only [Node.deleteStep, PagedBTree.eraseKey_eq_filter, Node.toList]
      generalize remainingEq :
        List.filter (fun entry : Entry Value => entry.1 ≠ key) entries = remaining
      change Node.deletedList
          (match remaining with
          | [] => none
          | remaining => some (.leaf remaining)) = remaining
      cases remaining <;> rfl
  | branch2 left separator right leftInduction rightInduction =>
      rcases routes with ⟨leftRoutes, rightRoutes, leftBefore, rightAfter⟩
      simp only [Node.deleteStep]
      split
      next keyBefore =>
        have rightUnchanged :
            right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
          filter_key_eq_self right.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt keyBefore (rightAfter entry member)
        have localEq := leftInduction leftRoutes
        cases deleted : left.deleteStep key with
        | none =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change right.toList = List.filter (fun entry => entry.1 ≠ key)
              (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
            simp
        | some updated =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change updated.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
      next keyAfter =>
        have leftUnchanged :
            left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
          filter_key_eq_self left.toList key fun entry member equal => by
            subst key
            exact Nat.not_lt_of_ge (Nat.le_of_not_gt keyAfter)
              (leftBefore entry member)
        have localEq := rightInduction rightRoutes
        cases deleted : right.deleteStep key with
        | none =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change left.toList = List.filter (fun entry => entry.1 ≠ key)
              (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
            simp
        | some updated =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change left.toList ++ updated.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases routes with
        ⟨leftRoutes, middleRoutes, rightRoutes, separatorsOrdered, leftBefore,
          middleBetween, rightAfter⟩
      simp only [Node.deleteStep]
      split
      next keyBefore =>
        have middleUnchanged :
            middle.toList.filter (fun entry => entry.1 ≠ key) = middle.toList :=
          filter_key_eq_self middle.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt keyBefore (middleBetween entry member).1
        have rightUnchanged :
            right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
          filter_key_eq_self right.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt (Nat.lt_trans keyBefore separatorsOrdered)
              (rightAfter entry member)
        have localEq := leftInduction leftRoutes
        cases deleted : left.deleteStep key with
        | none =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
            simp
        | some updated =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change updated.toList ++ middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
      next notLeft =>
        split
        next beforeRight =>
          have leftUnchanged :
              left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
            filter_key_eq_self left.toList key fun entry member equal => by
              subst key
              exact Nat.not_lt_of_ge (Nat.le_of_not_gt notLeft)
                (leftBefore entry member)
          have rightUnchanged :
              right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
            filter_key_eq_self right.toList key fun entry member equal => by
              subst key
              exact Nat.not_le_of_gt beforeRight (rightAfter entry member)
          have localEq := middleInduction middleRoutes
          cases deleted : middle.deleteStep key with
          | none =>
              rw [deleted] at localEq
              simp only [Node.deletedList] at localEq
              change left.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
              simp
          | some updated =>
              rw [deleted] at localEq
              simp only [Node.deletedList] at localEq
              change left.toList ++ updated.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
        next notMiddle =>
          have leftUnchanged :
              left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
            filter_key_eq_self left.toList key fun entry member equal => by
              subst key
              exact Nat.not_lt_of_ge (Nat.le_of_not_gt notLeft)
                (leftBefore entry member)
          have middleUnchanged :
              middle.toList.filter (fun entry => entry.1 ≠ key) = middle.toList :=
            filter_key_eq_self middle.toList key fun entry member equal => by
              subst key
              exact Nat.not_lt_of_ge (Nat.le_of_not_gt notMiddle)
                (middleBetween entry member).2
          have localEq := rightInduction rightRoutes
          cases deleted : right.deleteStep key with
          | none =>
              rw [deleted] at localEq
              simp only [Node.deletedList] at localEq
              change left.toList ++ middle.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]
              simp
          | some updated =>
              rw [deleted] at localEq
              simp only [Node.deletedList] at localEq
              change left.toList ++ middle.toList ++ updated.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]

theorem Node.toList_deleteUnbalanced (node : Node Value) (routes : node.Routes)
    (key : Nat) :
    (node.deleteUnbalanced key).toList =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  have step := node.deleteStep_toList routes key
  unfold Node.deleteUnbalanced
  cases deleted : node.deleteStep key with
  | none =>
      rw [deleted] at step
      simpa only [Node.deletedList, Node.toList, Option.getD_none] using step
  | some updated =>
      rw [deleted] at step
      simpa only [Node.deletedList, Option.getD_some] using step

def Tree (Value : Type) := Node Value

def Tree.empty : Tree Value := .leaf []

theorem Node.toList_empty : (Tree.empty : Tree Value).toList = [] := rfl

theorem Node.range_eq_filter (node : Node Value) (lower upper : Nat) :
    node.range lower upper =
      node.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
  rfl

/-- The pruned recursive range iterator is exactly the abstract range filter.
The proof discharges each skipped subtree from its separator interval. -/
theorem Node.rangeScan_eq_range (node : Node Value) (routes : node.Routes)
    (lower upper : Nat) : node.rangeScan lower upper = node.range lower upper := by
  induction node with
  | leaf entries => rfl
  | branch2 left separator right leftInduction rightInduction =>
      rcases routes with ⟨leftRoutes, rightRoutes, leftBefore, rightAfter⟩
      have leftPart :
          (if lower < separator then left.rangeScan lower upper else []) =
            left.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact leftInduction leftRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          exact Nat.not_lt_of_ge inside.1
            (Nat.lt_of_lt_of_le (leftBefore entry member)
              (Nat.le_of_not_gt misses))
      have rightPart :
          (if separator < upper then right.rangeScan lower upper else []) =
            right.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact rightInduction rightRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          exact Nat.not_lt_of_ge
            (Nat.le_trans (Nat.le_of_not_gt misses) (rightAfter entry member))
            inside.2
      unfold Node.rangeScan Node.range Node.toList
      rw [leftPart, rightPart, List.filter_append]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases routes with
        ⟨leftRoutes, middleRoutes, rightRoutes, separatorsOrdered, leftBefore,
          middleBetween, rightAfter⟩
      have leftPart :
          (if lower < firstSeparator then left.rangeScan lower upper else []) =
            left.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact leftInduction leftRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          exact Nat.not_lt_of_ge inside.1
            (Nat.lt_of_lt_of_le (leftBefore entry member)
              (Nat.le_of_not_gt misses))
      have middlePart :
          (if lower < secondSeparator ∧ firstSeparator < upper then
              middle.rangeScan lower upper else []) =
            middle.toList.filter
              (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact middleInduction middleRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          have between := middleBetween entry member
          apply misses
          constructor <;> omega
      have rightPart :
          (if secondSeparator < upper then right.rangeScan lower upper else []) =
            right.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact rightInduction rightRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          exact Nat.not_lt_of_ge
            (Nat.le_trans (Nat.le_of_not_gt misses) (rightAfter entry member))
            inside.2
      unfold Node.rangeScan Node.range Node.toList
      rw [leftPart, middlePart, rightPart, List.filter_append,
        List.filter_append]

theorem Node.insert_empty (key : Nat) (value : Value) :
    (Tree.empty : Tree Value).insert key value = .leaf [(key, value)] := by
  rfl

theorem Node.empty_balanced : (Tree.empty : Tree Value).Balanced := by
  simp [Tree.empty, Node.Balanced]

theorem Node.empty_rootValid : (Tree.empty : Tree Value).RootValid := by
  simp [Tree.empty, Node.RootValid, PagedBTree.KeysStrictlySorted]

end RecursiveBPlusTree

end SQLeanite
