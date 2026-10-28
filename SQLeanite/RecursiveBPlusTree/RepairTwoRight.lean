import SQLeanite.RecursiveBPlusTree.NodeInsertStepValid

namespace SQLeanite
namespace RecursiveBPlusTree

def repairTwoRight (left : Node Value) (separator : Nat)
    (deficit : Option (Node Value)) : DeleteResult Value :=
  match left, deficit with
  | .branch3 first firstSeparator middle secondSeparator last, some under =>
      .done (.branch2 (.branch2 first firstSeparator middle) secondSeparator
        (.branch2 last separator under))
  | .branch2 first middleSeparator last, some under =>
      .underflow (.branch3 first middleSeparator last separator under)
  | _, some under => .underflow (.branch2 left separator under)
  | _, none => .underflow left

def repairThreeLeft (firstSeparator : Nat)
    (deficit : Option (Node Value)) (middle : Node Value)
    (secondSeparator : Nat) (right : Node Value) : DeleteResult Value :=
  match deficit, middle with
  | some under, .branch3 first middleFirst second middleSecond third =>
      .done (.branch3 (.branch2 under firstSeparator first) middleFirst
        (.branch2 second middleSecond third) secondSeparator right)
  | some under, .branch2 first middleSeparator second =>
      .done (.branch2
        (.branch3 under firstSeparator first middleSeparator second)
        secondSeparator right)
  | some under, _ =>
      .done (.branch3 under firstSeparator middle secondSeparator right)
  | none, _ => .done (.branch2 middle secondSeparator right)

def repairThreeMiddle (left : Node Value) (firstSeparator : Nat)
    (deficit : Option (Node Value)) (secondSeparator : Nat)
    (right : Node Value) : DeleteResult Value :=
  match left, deficit with
  | .branch3 first leftFirst second leftSecond third, some under =>
      .done (.branch3 (.branch2 first leftFirst second) leftSecond
        (.branch2 third firstSeparator under) secondSeparator right)
  | .branch2 first leftSeparator second, some under =>
      .done (.branch2
        (.branch3 first leftSeparator second firstSeparator under)
        secondSeparator right)
  | _, some under =>
      .done (.branch3 left firstSeparator under secondSeparator right)
  | _, none => .done (.branch2 left secondSeparator right)

def repairThreeRight (left : Node Value) (firstSeparator : Nat)
    (middle : Node Value) (secondSeparator : Nat)
    (deficit : Option (Node Value)) : DeleteResult Value :=
  match middle, deficit with
  | .branch3 first middleFirst second middleSecond third, some under =>
      .done (.branch3 left firstSeparator
        (.branch2 first middleFirst second) middleSecond
        (.branch2 third secondSeparator under))
  | .branch2 first middleSeparator second, some under =>
      .done (.branch2 left firstSeparator
        (.branch3 first middleSeparator second secondSeparator under))
  | _, some under =>
      .done (.branch3 left firstSeparator middle secondSeparator under)
  | _, none => .done (.branch2 left firstSeparator middle)

/-- Local 2-3-tree deletion with borrowing from a three-child sibling, merging
with a two-child sibling, underflow propagation, and root shrink. -/
def Node.deleteBalancedStep (key : Nat) : Node Value → DeleteResult Value
  | .leaf entries =>
      match PagedBTree.eraseKey key entries with
      | [] => .empty
      | remaining => .done (.leaf remaining)
  | .branch2 left separator right =>
      if key < separator then
        match left.deleteBalancedStep key with
        | .done updated => .done (.branch2 updated separator right)
        | .underflow under => repairTwoLeft separator (some under) right
        | .empty => repairTwoLeft separator none right
      else
        match right.deleteBalancedStep key with
        | .done updated => .done (.branch2 left separator updated)
        | .underflow under => repairTwoRight left separator (some under)
        | .empty => repairTwoRight left separator none
  | .branch3 left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then
        match left.deleteBalancedStep key with
        | .done updated =>
            .done (.branch3 updated firstSeparator middle secondSeparator right)
        | .underflow under =>
            repairThreeLeft firstSeparator (some under) middle secondSeparator right
        | .empty => repairThreeLeft firstSeparator none middle secondSeparator right
      else if key < secondSeparator then
        match middle.deleteBalancedStep key with
        | .done updated =>
            .done (.branch3 left firstSeparator updated secondSeparator right)
        | .underflow under =>
            repairThreeMiddle left firstSeparator (some under) secondSeparator right
        | .empty => repairThreeMiddle left firstSeparator none secondSeparator right
      else
        match right.deleteBalancedStep key with
        | .done updated =>
            .done (.branch3 left firstSeparator middle secondSeparator updated)
        | .underflow under =>
            repairThreeRight left firstSeparator middle secondSeparator (some under)
        | .empty => repairThreeRight left firstSeparator middle secondSeparator none

def Node.deleteBalanced (node : Node Value) (key : Nat) : Node Value :=
  match node.deleteBalancedStep key with
  | .done updated | .underflow updated => updated
  | .empty => .leaf []

private def optionalNodeList : Option (Node Value) → List (Entry Value)
  | none => []
  | some node => node.toList

private theorem repairTwoLeft_toList (separator : Nat)
    (deficit : Option (Node Value)) (right : Node Value) :
    (repairTwoLeft separator deficit right).toList =
      optionalNodeList deficit ++ right.toList := by
  cases deficit <;> cases right <;>
    simp [repairTwoLeft, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

private theorem repairTwoRight_toList (left : Node Value) (separator : Nat)
    (deficit : Option (Node Value)) :
    (repairTwoRight left separator deficit).toList =
      left.toList ++ optionalNodeList deficit := by
  cases left <;> cases deficit <;>
    simp [repairTwoRight, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

private theorem repairThreeLeft_toList (firstSeparator : Nat)
    (deficit : Option (Node Value)) (middle : Node Value)
    (secondSeparator : Nat) (right : Node Value) :
    (repairThreeLeft firstSeparator deficit middle secondSeparator right).toList =
      optionalNodeList deficit ++ middle.toList ++ right.toList := by
  cases deficit <;> cases middle <;>
    simp [repairThreeLeft, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

private theorem repairThreeMiddle_toList (left : Node Value)
    (firstSeparator : Nat) (deficit : Option (Node Value))
    (secondSeparator : Nat) (right : Node Value) :
    (repairThreeMiddle left firstSeparator deficit secondSeparator right).toList =
      left.toList ++ optionalNodeList deficit ++ right.toList := by
  cases left <;> cases deficit <;>
    simp [repairThreeMiddle, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

private theorem repairThreeRight_toList (left : Node Value)
    (firstSeparator : Nat) (middle : Node Value) (secondSeparator : Nat)
    (deficit : Option (Node Value)) :
    (repairThreeRight left firstSeparator middle secondSeparator deficit).toList =
      left.toList ++ middle.toList ++ optionalNodeList deficit := by
  cases middle <;> cases deficit <;>
    simp [repairThreeRight, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

/-- Local deletion removes only the routed leaf. Empty children are merged out
and a unary root is therefore shrunk automatically. -/
def Node.deleteStep (key : Nat) : Node Value → Option (Node Value)
  | .leaf entries =>
      match PagedBTree.eraseKey key entries with
      | [] => none
      | remaining => some (.leaf remaining)
  | .branch2 left separator right =>
      if key < separator then
        match left.deleteStep key with
        | some updated => some (.branch2 updated separator right)
        | none => some right
      else
        match right.deleteStep key with
        | some updated => some (.branch2 left separator updated)
        | none => some left
  | .branch3 left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then
        match left.deleteStep key with
        | some updated =>
            some (.branch3 updated firstSeparator middle secondSeparator right)
        | none => some (.branch2 middle secondSeparator right)
      else if key < secondSeparator then
        match middle.deleteStep key with
        | some updated =>
            some (.branch3 left firstSeparator updated secondSeparator right)
        | none => some (.branch2 left secondSeparator right)
      else
        match right.deleteStep key with
        | some updated =>
            some (.branch3 left firstSeparator middle secondSeparator updated)
        | none => some (.branch2 left firstSeparator middle)

def Node.deleteUnbalanced (node : Node Value) (key : Nat) : Node Value :=
  (node.deleteStep key).getD (.leaf [])

def Node.deletedList : Option (Node Value) → List (Entry Value)
  | none => []
  | some node => node.toList

theorem filter_key_eq_self (entries : List (Entry Value)) (key : Nat)
    (absent : ∀ entry ∈ entries, entry.1 ≠ key) :
    entries.filter (fun entry => entry.1 ≠ key) = entries := by
  apply List.filter_eq_self.2
  intro entry member
  simp [absent entry member]

/-- Balanced deletion has the exact abstract effect of removing the routed
key. Borrowing and merging only reassociate the same child contents. -/
theorem Node.deleteBalancedStep_toList (node : Node Value)
    (routes : node.Routes) (key : Nat) :
    (node.deleteBalancedStep key).toList =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  induction node with
  | leaf entries =>
      simp only [Node.deleteBalancedStep, PagedBTree.eraseKey_eq_filter,
        Node.toList]
      generalize remainingEq :
        List.filter (fun entry : Entry Value => entry.1 ≠ key) entries = remaining
      change DeleteResult.toList
          (match remaining with
          | [] => .empty
          | remaining => .done (.leaf remaining)) = remaining
      cases remaining <;> rfl
  | branch2 left separator right leftInduction rightInduction =>
      rcases routes with ⟨leftRoutes, rightRoutes, leftBefore, rightAfter⟩
      simp only [Node.deleteBalancedStep]
      split
      next keyBefore =>
        have rightUnchanged :
            right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
          filter_key_eq_self right.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt keyBefore (rightAfter entry member)
        have localEq := leftInduction leftRoutes
        cases changed : left.deleteBalancedStep key with
        | done updated =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            change updated.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
        | underflow under =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairTwoLeft_toList]
            change under.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
        | empty =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairTwoLeft_toList]
            simp only [optionalNodeList, Node.toList, List.append_nil,
              List.nil_append]
            change right.toList = List.filter (fun entry => entry.1 ≠ key)
              (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
            simp
      next keyAfter =>
        have leftUnchanged :
            left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
          filter_key_eq_self left.toList key fun entry member equal => by
            subst key
            exact Nat.not_lt_of_ge (Nat.le_of_not_gt keyAfter)
              (leftBefore entry member)
        have localEq := rightInduction rightRoutes
        cases changed : right.deleteBalancedStep key with
        | done updated =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            change left.toList ++ updated.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
        | underflow under =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairTwoRight_toList]
            change left.toList ++ under.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
        | empty =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairTwoRight_toList]
            simp only [optionalNodeList, Node.toList, List.append_nil,
              List.nil_append]
            change left.toList = List.filter (fun entry => entry.1 ≠ key)
              (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
            simp
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases routes with
        ⟨leftRoutes, middleRoutes, rightRoutes, separatorsOrdered, leftBefore,
          middleBetween, rightAfter⟩
      simp only [Node.deleteBalancedStep]
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
        cases changed : left.deleteBalancedStep key with
        | done updated =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            change updated.toList ++ middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
        | underflow under =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairThreeLeft_toList]
            change under.toList ++ middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
        | empty =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairThreeLeft_toList]
            simp only [optionalNodeList, Node.toList, List.append_nil,
              List.nil_append]
            change middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
            simp
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
          cases changed : middle.deleteBalancedStep key with
          | done updated =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              change left.toList ++ updated.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
          | underflow under =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              rw [repairThreeMiddle_toList]
              change left.toList ++ under.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
          | empty =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              rw [repairThreeMiddle_toList]
              simp only [optionalNodeList, Node.toList, List.append_nil,
                List.nil_append]
              change left.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
              simp
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
          cases changed : right.deleteBalancedStep key with
          | done updated =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              change left.toList ++ middle.toList ++ updated.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]
          | underflow under =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              rw [repairThreeRight_toList]
              change left.toList ++ middle.toList ++ under.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]
          | empty =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              rw [repairThreeRight_toList]
              simp only [optionalNodeList, Node.toList, List.append_nil,
                List.nil_append]
              change left.toList ++ middle.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]
              simp

theorem Node.toList_deleteBalanced (node : Node Value) (routes : node.Routes)
    (key : Nat) :
    (node.deleteBalanced key).toList =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  have step := node.deleteBalancedStep_toList routes key
  unfold Node.deleteBalanced
  cases changed : node.deleteBalancedStep key with
  | done updated =>
      rw [changed] at step
      exact step
  | underflow updated =>
      rw [changed] at step
      exact step
  | empty =>
      rw [changed] at step
      simpa [DeleteResult.toList, Node.toList] using step

/-- The public deletion uses the localized borrow/merge algorithm whenever its
full invariant check succeeds. A malformed or unexpectedly rejected candidate
is rebuilt through proved insertion, so callers receive a valid root by
construction rather than relying on an unchecked postcondition. -/
def Node.delete (node : Node Value) (key : Nat) : Node Value :=
  let candidate := node.deleteBalanced key
  if candidate.checkRootValid then candidate
  else
    (Node.leaf ([] : List (Entry Value))).insertAll
      (node.toList.filter fun entry => entry.1 ≠ key)

theorem Node.delete_rootValid (node : Node Value) (key : Nat) :
    (node.delete key).RootValid := by
  simp only [Node.delete]
  split
  next accepted => exact (Node.checkRootValid_iff _).mp accepted
  next =>
    apply Node.insertAll_rootValid
    simp [Node.RootValid, PagedBTree.KeysStrictlySorted]

end RecursiveBPlusTree

end SQLeanite
