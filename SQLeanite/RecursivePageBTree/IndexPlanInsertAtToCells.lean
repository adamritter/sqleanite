import SQLeanite.RecursivePageBTree.PlanEncodePagesFrom

namespace SQLeanite
namespace RecursivePageBTree

theorem IndexPlan.insertAt?_toCells {plan updated : IndexPlan}
    {position : Nat} {cell : List UInt8}
    (inserted : plan.insertAt? position cell = some updated) :
    updated.toCells = insertCellAt position cell plan.toCells := by
  induction plan generalizing position updated with
  | leaf cells =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        injection inserted with equal
        subst updated
        rfl
      next => contradiction
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next before =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.toCells]
        rw [leftInduction childResult]
        symm
        simpa [List.append_assoc] using insertCellAt_append_left left.toCells
          ([separator] ++ right.toCells) position cell before
      next after =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.toCells]
        rw [rightInduction childResult]
        have past : left.toCells.length < position := Nat.lt_of_not_ge after
        have positive : 0 < position - left.toCells.length := by omega
        have decomposed := insertCellAt_append_right left.toCells
          ([separator] ++ right.toCells) position cell (Nat.le_of_lt past)
        simp only [List.singleton_append] at decomposed
        rw [insertCellAt_cons_of_pos separator right.toCells
          (position - left.toCells.length) cell positive] at decomposed
        have offset : position - left.toCells.length - 1 =
            position - (left.toCells.length + 1) := by omega
        rw [offset] at decomposed
        simpa [List.append_assoc] using decomposed.symm
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next before =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.toCells]
        rw [leftInduction childResult]
        symm
        simpa [List.append_assoc] using insertCellAt_append_left left.toCells
          ([firstSeparator] ++ middle.toCells ++
            [secondSeparator] ++ right.toCells) position cell before
      next afterLeft =>
        split at inserted
        next beforeRight =>
          rcases Option.bind_eq_some_iff.mp inserted with
            ⟨child, childResult, inserted⟩
          injection inserted with equal
          subst updated
          simp only [IndexPlan.toCells]
          rw [middleInduction childResult]
          have past : left.toCells.length < position :=
            Nat.lt_of_not_ge afterLeft
          have positive : 0 < position - left.toCells.length := by omega
          have decomposed := insertCellAt_append_right left.toCells
            ([firstSeparator] ++ middle.toCells ++
              [secondSeparator] ++ right.toCells) position cell
                (Nat.le_of_lt past)
          simp only [List.singleton_append, List.cons_append,
            List.nil_append, List.append_assoc] at decomposed
          rw [insertCellAt_cons_of_pos firstSeparator
            (middle.toCells ++ (secondSeparator :: right.toCells))
            (position - left.toCells.length) cell positive] at decomposed
          have offset : position - left.toCells.length - 1 =
              position - (left.toCells.length + 1) := by omega
          rw [offset] at decomposed
          have middleBound : position - (left.toCells.length + 1) ≤
              middle.toCells.length := by
            omega
          rw [insertCellAt_append_left middle.toCells
            (secondSeparator :: right.toCells)
            (position - (left.toCells.length + 1)) cell middleBound]
              at decomposed
          simpa [List.append_assoc] using decomposed.symm
        next afterMiddle =>
          rcases Option.bind_eq_some_iff.mp inserted with
            ⟨child, childResult, inserted⟩
          injection inserted with equal
          subst updated
          simp only [IndexPlan.toCells]
          rw [rightInduction childResult]
          let beforeRightCells := left.toCells ++ [firstSeparator] ++ middle.toCells ++
            [secondSeparator]
          have prefixLength : beforeRightCells.length =
              left.toCells.length + 1 + middle.toCells.length + 1 := by
            simp [beforeRightCells]
            omega
          have past : beforeRightCells.length ≤ position := by
            rw [prefixLength]
            omega
          rw [show left.toCells ++ [firstSeparator] ++ middle.toCells ++
              [secondSeparator] ++ right.toCells =
                beforeRightCells ++ right.toCells by
                simp [beforeRightCells, List.append_assoc]]
          rw [insertCellAt_append_right beforeRightCells right.toCells
            position cell past]
          rw [prefixLength]

theorem IndexPlan.insertAt?_pageCount {plan updated : IndexPlan}
    {position : Nat} {cell : List UInt8}
    (inserted : plan.insertAt? position cell = some updated) :
    updated.pageCount = plan.pageCount := by
  induction plan generalizing position updated with
  | leaf cells =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        injection inserted with equal
        subst updated
        rfl
      next => contradiction
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.pageCount]
        rw [leftInduction childResult]
      next =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.pageCount]
        rw [rightInduction childResult]
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.pageCount]
        rw [leftInduction childResult]
      next =>
        split at inserted
        next =>
          rcases Option.bind_eq_some_iff.mp inserted with
            ⟨child, childResult, inserted⟩
          injection inserted with equal
          subst updated
          simp only [IndexPlan.pageCount]
          rw [middleInduction childResult]
        next =>
          rcases Option.bind_eq_some_iff.mp inserted with
            ⟨child, childResult, inserted⟩
          injection inserted with equal
          subst updated
          simp only [IndexPlan.pageCount]
          rw [rightInduction childResult]

theorem IndexPlan.pageCount_pos (plan : IndexPlan) : 0 < plan.pageCount := by
  cases plan <;> simp only [IndexPlan.pageCount] <;> omega

def IndexPlan.height : IndexPlan → Nat
  | .leaf _ => 0
  | .branch2 left _ _ => left.height + 1
  | .branch3 left _ _ _ _ => left.height + 1

def IndexPlan.Balanced : IndexPlan → Prop
  | .leaf _ => True
  | .branch2 left _ right =>
      left.Balanced ∧ right.Balanced ∧ left.height = right.height
  | .branch3 left _ middle _ right =>
      left.Balanced ∧ middle.Balanced ∧ right.Balanced ∧
      left.height = middle.height ∧ middle.height = right.height

theorem IndexPlan.insertAt?_height {plan updated : IndexPlan}
    {position : Nat} {cell : List UInt8}
    (inserted : plan.insertAt? position cell = some updated) :
    updated.height = plan.height := by
  induction plan generalizing position updated with
  | leaf cells =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        injection inserted with equal
        subst updated
        rfl
      next => contradiction
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.height]
        rw [leftInduction childResult]
      next =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        rfl
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.height]
        rw [leftInduction childResult]
      next =>
        split at inserted
        next =>
          rcases Option.bind_eq_some_iff.mp inserted with
            ⟨child, childResult, inserted⟩
          injection inserted with equal
          subst updated
          rfl
        next =>
          rcases Option.bind_eq_some_iff.mp inserted with
            ⟨child, childResult, inserted⟩
          injection inserted with equal
          subst updated
          rfl

theorem IndexPlan.insertAt?_balanced {plan updated : IndexPlan}
    {position : Nat} {cell : List UInt8} (balanced : plan.Balanced)
    (inserted : plan.insertAt? position cell = some updated) :
    updated.Balanced := by
  induction plan generalizing position updated with
  | leaf cells =>
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        injection inserted with equal
        subst updated
        trivial
      next => contradiction
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.Balanced] at balanced
      rcases balanced with ⟨leftBalanced, rightBalanced, heightEqual⟩
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.Balanced]
        refine ⟨leftInduction leftBalanced childResult, rightBalanced, ?_⟩
        rw [IndexPlan.insertAt?_height childResult]
        exact heightEqual
      next =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.Balanced]
        refine ⟨leftBalanced, rightInduction rightBalanced childResult, ?_⟩
        rw [IndexPlan.insertAt?_height childResult]
        exact heightEqual
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [IndexPlan.Balanced] at balanced
      rcases balanced with ⟨leftBalanced, middleBalanced, rightBalanced,
        leftMiddleHeight, middleRightHeight⟩
      simp only [IndexPlan.insertAt?] at inserted
      split at inserted
      next =>
        rcases Option.bind_eq_some_iff.mp inserted with
          ⟨child, childResult, inserted⟩
        injection inserted with equal
        subst updated
        simp only [IndexPlan.Balanced]
        refine ⟨leftInduction leftBalanced childResult, middleBalanced,
          rightBalanced, ?_, middleRightHeight⟩
        rw [IndexPlan.insertAt?_height childResult]
        exact leftMiddleHeight
      next =>
        split at inserted
        next =>
          rcases Option.bind_eq_some_iff.mp inserted with
            ⟨child, childResult, inserted⟩
          injection inserted with equal
          subst updated
          simp only [IndexPlan.Balanced]
          refine ⟨leftBalanced,
            middleInduction middleBalanced childResult, rightBalanced,
            ?_, ?_⟩
          · rw [IndexPlan.insertAt?_height childResult]
            exact leftMiddleHeight
          · rw [IndexPlan.insertAt?_height childResult]
            exact middleRightHeight
        next =>
          rcases Option.bind_eq_some_iff.mp inserted with
            ⟨child, childResult, inserted⟩
          injection inserted with equal
          subst updated
          simp only [IndexPlan.Balanced]
          refine ⟨leftBalanced, middleBalanced,
            rightInduction rightBalanced childResult, leftMiddleHeight, ?_⟩
          rw [IndexPlan.insertAt?_height childResult]
          exact middleRightHeight

theorem IndexPlan.height_lt_pageCount (plan : IndexPlan) :
    plan.height < plan.pageCount := by
  induction plan with
  | leaf => simp [IndexPlan.height, IndexPlan.pageCount]
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.height, IndexPlan.pageCount]
      have rightPositive := right.pageCount_pos
      omega
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [IndexPlan.height, IndexPlan.pageCount]
      have middlePositive := middle.pageCount_pos
      have rightPositive := right.pageCount_pos
      omega

def IndexPlan.checkBalanced : IndexPlan → Bool
  | .leaf _ => true
  | .branch2 left _ right =>
      left.checkBalanced && right.checkBalanced && decide (left.height = right.height)
  | .branch3 left _ middle _ right =>
      left.checkBalanced && middle.checkBalanced && right.checkBalanced &&
        decide (left.height = middle.height) && decide (middle.height = right.height)

theorem IndexPlan.checkBalanced_iff (plan : IndexPlan) :
    plan.checkBalanced = true ↔ plan.Balanced := by
  induction plan with
  | leaf => simp [IndexPlan.checkBalanced, IndexPlan.Balanced]
  | branch2 left separator right leftInduction rightInduction =>
      simp [IndexPlan.checkBalanced, IndexPlan.Balanced, leftInduction,
        rightInduction, and_assoc]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp [IndexPlan.checkBalanced, IndexPlan.Balanced, leftInduction,
        middleInduction, rightInduction, and_assoc]

theorem IndexPlan.replaceCells_height {plan updated : IndexPlan}
    {cells remaining : List (List UInt8)}
    (replaced : plan.replaceCells cells = some (updated, remaining)) :
    updated.height = plan.height := by
  induction plan generalizing cells updated remaining with
  | leaf previous =>
      simp only [IndexPlan.replaceCells, Option.some.injEq,
        Prod.mk.injEq] at replaced
      rw [← replaced.1]
      rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.replaceCells, Option.bind_eq_bind, Option.bind]
        at replaced
      cases leftResult : left.replaceCells cells with
      | none => simp [leftResult] at replaced
      | some leftPair =>
        rcases leftPair with ⟨left', afterLeft⟩
        simp only [leftResult] at replaced
        cases afterLeft with
        | nil => contradiction
        | cons replacement afterSeparator =>
          cases rightResult : right.replaceCells afterSeparator with
          | none => simp [rightResult] at replaced
          | some rightPair =>
            rcases rightPair with ⟨right', rest⟩
            simp only [rightResult, Option.some.injEq, Prod.mk.injEq]
              at replaced
            rcases replaced with ⟨rfl, rfl⟩
            simp only [IndexPlan.height]
            rw [leftInduction leftResult]
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [IndexPlan.replaceCells, Option.bind_eq_bind, Option.bind]
        at replaced
      cases leftResult : left.replaceCells cells with
      | none => simp [leftResult] at replaced
      | some leftPair =>
        rcases leftPair with ⟨left', afterLeft⟩
        simp only [leftResult] at replaced
        cases afterLeft with
        | nil => contradiction
        | cons first afterFirst =>
          cases middleResult : middle.replaceCells afterFirst with
          | none => simp [middleResult] at replaced
          | some middlePair =>
            rcases middlePair with ⟨middle', afterMiddle⟩
            simp only [middleResult] at replaced
            cases afterMiddle with
            | nil => contradiction
            | cons second afterSecond =>
              cases rightResult : right.replaceCells afterSecond with
              | none => simp [rightResult] at replaced
              | some rightPair =>
                rcases rightPair with ⟨right', rest⟩
                simp only [rightResult, Option.some.injEq, Prod.mk.injEq]
                  at replaced
                rcases replaced with ⟨rfl, rfl⟩
                simp only [IndexPlan.height]
                rw [leftInduction leftResult]

end RecursivePageBTree

end SQLeanite
