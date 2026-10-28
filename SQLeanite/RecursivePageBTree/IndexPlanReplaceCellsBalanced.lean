import SQLeanite.RecursivePageBTree.IndexPlanInsertAtToCells

namespace SQLeanite
namespace RecursivePageBTree

theorem IndexPlan.replaceCells_balanced {plan updated : IndexPlan}
    {cells remaining : List (List UInt8)} (balanced : plan.Balanced)
    (replaced : plan.replaceCells cells = some (updated, remaining)) :
    updated.Balanced := by
  induction plan generalizing cells updated remaining with
  | leaf previous =>
      simp only [IndexPlan.replaceCells, Option.some.injEq,
        Prod.mk.injEq] at replaced
      rw [← replaced.1]
      trivial
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.Balanced] at balanced
      rcases balanced with ⟨leftBalanced, rightBalanced, heightEqual⟩
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
            simp only [IndexPlan.Balanced]
            refine ⟨leftInduction leftBalanced leftResult,
              rightInduction rightBalanced rightResult, ?_⟩
            rw [IndexPlan.replaceCells_height leftResult,
              IndexPlan.replaceCells_height rightResult]
            exact heightEqual
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [IndexPlan.Balanced] at balanced
      rcases balanced with ⟨leftBalanced, middleBalanced, rightBalanced,
        leftMiddleHeight, middleRightHeight⟩
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
                simp only [IndexPlan.Balanced]
                refine ⟨leftInduction leftBalanced leftResult,
                  middleInduction middleBalanced middleResult,
                  rightInduction rightBalanced rightResult, ?_, ?_⟩
                · rw [IndexPlan.replaceCells_height leftResult,
                    IndexPlan.replaceCells_height middleResult]
                  exact leftMiddleHeight
                · rw [IndexPlan.replaceCells_height middleResult,
                    IndexPlan.replaceCells_height rightResult]
                  exact middleRightHeight

theorem IndexPlan.withCells?_balanced {plan updated : IndexPlan}
    {cells : List (List UInt8)} (balanced : plan.Balanced)
    (replaced : plan.withCells? cells = some updated) : updated.Balanced := by
  unfold IndexPlan.withCells? at replaced
  split at replaced
  next =>
    cases result : plan.replaceCells cells with
    | none => simp [result] at replaced
    | some pair =>
      rcases pair with ⟨candidate, remaining⟩
      simp only [result, Option.bind_eq_bind, Option.bind] at replaced
      split at replaced
      next =>
        injection replaced with equal
        subst updated
        exact IndexPlan.replaceCells_balanced balanced result
      next => contradiction
  next => contradiction

/-- Remove the greatest in-order key for promotion into a parent page. The
rightmost descent is local and never changes topology. -/
def IndexPlan.popMax : IndexPlan → Option (IndexPlan × List UInt8)
  | .leaf cells => do
      let key ← cells.getLast?
      some (.leaf cells.dropLast, key)
  | .branch2 left separator right => do
      let (updated, key) ← right.popMax
      some (.branch2 left separator updated, key)
  | .branch3 left firstSeparator middle secondSeparator right => do
      let (updated, key) ← right.popMax
      some (.branch3 left firstSeparator middle secondSeparator updated, key)

theorem IndexPlan.popMax_toCells {plan updated : IndexPlan} {key : List UInt8}
    (popped : plan.popMax = some (updated, key)) :
    updated.toCells ++ [key] = plan.toCells := by
  induction plan generalizing updated key with
  | leaf cells =>
      simp only [IndexPlan.popMax, Option.bind_eq_bind, Option.bind] at popped
      cases lastResult : cells.getLast? with
      | none => simp [lastResult] at popped
      | some last =>
        simp only [lastResult, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        have nonempty : cells ≠ [] := by
          intro empty
          simp [empty] at lastResult
        have lastEq : cells.getLast nonempty = last :=
          (List.getLast_eq_iff_getLast?_eq_some nonempty).2 lastResult
        simp only [IndexPlan.toCells]
        rw [← lastEq]
        exact List.dropLast_concat_getLast nonempty
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.popMax, Option.bind_eq_bind, Option.bind] at popped
      cases childResult : right.popMax with
      | none => simp [childResult] at popped
      | some result =>
        rcases result with ⟨rightUpdated, promoted⟩
        simp only [childResult, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        have childContents := rightInduction childResult
        simp only [IndexPlan.toCells]
        rw [List.append_assoc, childContents]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.popMax, Option.bind_eq_bind, Option.bind] at popped
      cases childResult : right.popMax with
      | none => simp [childResult] at popped
      | some result =>
        rcases result with ⟨rightUpdated, promoted⟩
        simp only [childResult, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        have childContents := rightInduction childResult
        simp only [IndexPlan.toCells]
        rw [List.append_assoc, childContents]

theorem IndexPlan.popMax_height {plan updated : IndexPlan} {key : List UInt8}
    (popped : plan.popMax = some (updated, key)) : updated.height = plan.height := by
  induction plan generalizing updated key with
  | leaf cells =>
      simp only [IndexPlan.popMax, Option.bind_eq_bind, Option.bind] at popped
      cases lastResult : cells.getLast? with
      | none => simp [lastResult] at popped
      | some last =>
        simp only [lastResult, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.popMax, Option.bind_eq_bind, Option.bind] at popped
      cases childResult : right.popMax with
      | none => simp [childResult] at popped
      | some result =>
        rcases result with ⟨rightUpdated, promoted⟩
        simp only [childResult, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        simp [IndexPlan.height, rightInduction childResult]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.popMax, Option.bind_eq_bind, Option.bind] at popped
      cases childResult : right.popMax with
      | none => simp [childResult] at popped
      | some result =>
        rcases result with ⟨rightUpdated, promoted⟩
        simp only [childResult, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        simp [IndexPlan.height, rightInduction childResult]

theorem IndexPlan.popMax_balanced {plan updated : IndexPlan} {key : List UInt8}
    (balanced : plan.Balanced)
    (popped : plan.popMax = some (updated, key)) : updated.Balanced := by
  induction plan generalizing updated key with
  | leaf cells =>
      simp only [IndexPlan.popMax, Option.bind_eq_bind, Option.bind] at popped
      cases lastResult : cells.getLast? with
      | none => simp [lastResult] at popped
      | some last =>
        simp only [lastResult, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        trivial
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.popMax, Option.bind_eq_bind, Option.bind] at popped
      cases childResult : right.popMax with
      | none => simp [childResult] at popped
      | some result =>
        rcases result with ⟨rightUpdated, promoted⟩
        simp only [childResult, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        rcases balanced with ⟨leftBalanced, rightBalanced, heights⟩
        exact ⟨leftBalanced, rightInduction rightBalanced childResult,
          heights.trans (IndexPlan.popMax_height childResult).symm⟩
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.popMax, Option.bind_eq_bind, Option.bind] at popped
      cases childResult : right.popMax with
      | none => simp [childResult] at popped
      | some result =>
        rcases result with ⟨rightUpdated, promoted⟩
        simp only [childResult, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        rcases balanced with
          ⟨leftBalanced, middleBalanced, rightBalanced, leftHeight, rightHeight⟩
        exact ⟨leftBalanced, middleBalanced,
          rightInduction rightBalanced childResult, leftHeight,
          rightHeight.trans (IndexPlan.popMax_height childResult).symm⟩

/-- Apply index-key promotion to a balanced table-style topology. -/
def IndexPlan.ofPlan : Plan → Option IndexPlan
  | .leaf cells => some (.leaf cells)
  | .branch2 left right => do
      let left ← ofPlan left
      let right ← ofPlan right
      let (left, separator) ← left.popMax
      some (.branch2 left separator right)
  | .branch3 left middle right => do
      let left ← ofPlan left
      let middle ← ofPlan middle
      let right ← ofPlan right
      let (left, firstSeparator) ← left.popMax
      let (middle, secondSeparator) ← middle.popMax
      some (.branch3 left firstSeparator middle secondSeparator right)

theorem IndexPlan.ofPlan_toCells {plan : Plan} {indexPlan : IndexPlan}
    (converted : IndexPlan.ofPlan plan = some indexPlan) :
    indexPlan.toCells = plan.toCells := by
  induction plan generalizing indexPlan with
  | leaf cells =>
      simp only [IndexPlan.ofPlan, Option.some.injEq] at converted
      subst indexPlan
      rfl
  | branch2 left right leftInduction rightInduction =>
      simp only [IndexPlan.ofPlan, Option.bind_eq_bind, Option.bind] at converted
      cases leftResult : IndexPlan.ofPlan left with
      | none => simp [leftResult] at converted
      | some leftPlan =>
        simp only [leftResult] at converted
        cases rightResult : IndexPlan.ofPlan right with
        | none => simp [rightResult] at converted
        | some rightPlan =>
          simp only [rightResult] at converted
          cases promotedResult : leftPlan.popMax with
          | none => simp [promotedResult] at converted
          | some promoted =>
            rcases promoted with ⟨leftUpdated, separator⟩
            simp only [promotedResult, Option.some.injEq] at converted
            subst indexPlan
            simp only [IndexPlan.toCells, Plan.toCells]
            have leftContents := IndexPlan.popMax_toCells promotedResult
            calc
              leftUpdated.toCells ++ [separator] ++ rightPlan.toCells =
                  (leftUpdated.toCells ++ [separator]) ++ rightPlan.toCells := rfl
              _ = leftPlan.toCells ++ rightPlan.toCells := by rw [leftContents]
              _ = left.toCells ++ right.toCells := by
                rw [leftInduction leftResult, rightInduction rightResult]
  | branch3 left middle right leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.ofPlan, Option.bind_eq_bind, Option.bind] at converted
      cases leftResult : IndexPlan.ofPlan left with
      | none => simp [leftResult] at converted
      | some leftPlan =>
        simp only [leftResult] at converted
        cases middleResult : IndexPlan.ofPlan middle with
        | none => simp [middleResult] at converted
        | some middlePlan =>
          simp only [middleResult] at converted
          cases rightResult : IndexPlan.ofPlan right with
          | none => simp [rightResult] at converted
          | some rightPlan =>
            simp only [rightResult] at converted
            cases leftPromoted : leftPlan.popMax with
            | none => simp [leftPromoted] at converted
            | some leftPair =>
              rcases leftPair with ⟨leftUpdated, firstSeparator⟩
              simp only [leftPromoted] at converted
              cases middlePromoted : middlePlan.popMax with
              | none => simp [middlePromoted] at converted
              | some middlePair =>
                rcases middlePair with ⟨middleUpdated, secondSeparator⟩
                simp only [middlePromoted, Option.some.injEq] at converted
                subst indexPlan
                simp only [IndexPlan.toCells, Plan.toCells]
                have leftContents := IndexPlan.popMax_toCells leftPromoted
                have middleContents := IndexPlan.popMax_toCells middlePromoted
                calc
                  leftUpdated.toCells ++ [firstSeparator] ++
                      middleUpdated.toCells ++ [secondSeparator] ++
                      rightPlan.toCells =
                    (leftUpdated.toCells ++ [firstSeparator]) ++
                      (middleUpdated.toCells ++ [secondSeparator]) ++
                      rightPlan.toCells := by simp [List.append_assoc]
                  _ = leftPlan.toCells ++ middlePlan.toCells ++
                      rightPlan.toCells := by rw [leftContents, middleContents]
                  _ = left.toCells ++ middle.toCells ++ right.toCells := by
                    rw [leftInduction leftResult, middleInduction middleResult,
                      rightInduction rightResult]

theorem IndexPlan.ofPlan_height {plan : Plan} {indexPlan : IndexPlan}
    (converted : IndexPlan.ofPlan plan = some indexPlan) :
    indexPlan.height = plan.height := by
  induction plan generalizing indexPlan with
  | leaf cells =>
      simp only [IndexPlan.ofPlan, Option.some.injEq] at converted
      subst indexPlan
      rfl
  | branch2 left right leftInduction rightInduction =>
      simp only [IndexPlan.ofPlan, Option.bind_eq_bind, Option.bind] at converted
      cases leftResult : IndexPlan.ofPlan left with
      | none => simp [leftResult] at converted
      | some leftPlan =>
        simp only [leftResult] at converted
        cases rightResult : IndexPlan.ofPlan right with
        | none => simp [rightResult] at converted
        | some rightPlan =>
          simp only [rightResult] at converted
          cases promotedResult : leftPlan.popMax with
          | none => simp [promotedResult] at converted
          | some promoted =>
            rcases promoted with ⟨leftUpdated, separator⟩
            simp only [promotedResult, Option.some.injEq] at converted
            subst indexPlan
            simp [IndexPlan.height, Plan.height,
              IndexPlan.popMax_height promotedResult,
              leftInduction leftResult]
  | branch3 left middle right leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.ofPlan, Option.bind_eq_bind, Option.bind] at converted
      cases leftResult : IndexPlan.ofPlan left with
      | none => simp [leftResult] at converted
      | some leftPlan =>
        simp only [leftResult] at converted
        cases middleResult : IndexPlan.ofPlan middle with
        | none => simp [middleResult] at converted
        | some middlePlan =>
          simp only [middleResult] at converted
          cases rightResult : IndexPlan.ofPlan right with
          | none => simp [rightResult] at converted
          | some rightPlan =>
            simp only [rightResult] at converted
            cases leftPromoted : leftPlan.popMax with
            | none => simp [leftPromoted] at converted
            | some leftPair =>
              rcases leftPair with ⟨leftUpdated, firstSeparator⟩
              simp only [leftPromoted] at converted
              cases middlePromoted : middlePlan.popMax with
              | none => simp [middlePromoted] at converted
              | some middlePair =>
                rcases middlePair with ⟨middleUpdated, secondSeparator⟩
                simp only [middlePromoted, Option.some.injEq] at converted
                subst indexPlan
                simp [IndexPlan.height, Plan.height,
                  IndexPlan.popMax_height leftPromoted,
                  leftInduction leftResult]

theorem IndexPlan.ofPlan_balanced {plan : Plan} {indexPlan : IndexPlan}
    (balanced : plan.Balanced)
    (converted : IndexPlan.ofPlan plan = some indexPlan) :
    indexPlan.Balanced := by
  induction plan generalizing indexPlan with
  | leaf cells =>
      simp only [IndexPlan.ofPlan, Option.some.injEq] at converted
      subst indexPlan
      trivial
  | branch2 left right leftInduction rightInduction =>
      simp only [IndexPlan.ofPlan, Option.bind_eq_bind, Option.bind] at converted
      cases leftResult : IndexPlan.ofPlan left with
      | none => simp [leftResult] at converted
      | some leftPlan =>
        simp only [leftResult] at converted
        cases rightResult : IndexPlan.ofPlan right with
        | none => simp [rightResult] at converted
        | some rightPlan =>
          simp only [rightResult] at converted
          cases promotedResult : leftPlan.popMax with
          | none => simp [promotedResult] at converted
          | some promoted =>
            rcases promoted with ⟨leftUpdated, separator⟩
            simp only [promotedResult, Option.some.injEq] at converted
            subst indexPlan
            rcases balanced with ⟨leftBalanced, rightBalanced, heights⟩
            refine ⟨IndexPlan.popMax_balanced
                (leftInduction leftBalanced leftResult) promotedResult,
              rightInduction rightBalanced rightResult, ?_⟩
            rw [IndexPlan.popMax_height promotedResult,
              IndexPlan.ofPlan_height leftResult,
              IndexPlan.ofPlan_height rightResult]
            exact heights
  | branch3 left middle right leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.ofPlan, Option.bind_eq_bind, Option.bind] at converted
      cases leftResult : IndexPlan.ofPlan left with
      | none => simp [leftResult] at converted
      | some leftPlan =>
        simp only [leftResult] at converted
        cases middleResult : IndexPlan.ofPlan middle with
        | none => simp [middleResult] at converted
        | some middlePlan =>
          simp only [middleResult] at converted
          cases rightResult : IndexPlan.ofPlan right with
          | none => simp [rightResult] at converted
          | some rightPlan =>
            simp only [rightResult] at converted
            cases leftPromoted : leftPlan.popMax with
            | none => simp [leftPromoted] at converted
            | some leftPair =>
              rcases leftPair with ⟨leftUpdated, firstSeparator⟩
              simp only [leftPromoted] at converted
              cases middlePromoted : middlePlan.popMax with
              | none => simp [middlePromoted] at converted
              | some middlePair =>
                rcases middlePair with ⟨middleUpdated, secondSeparator⟩
                simp only [middlePromoted, Option.some.injEq] at converted
                subst indexPlan
                rcases balanced with
                  ⟨leftBalanced, middleBalanced, rightBalanced,
                    leftHeight, rightHeight⟩
                refine ⟨IndexPlan.popMax_balanced
                    (leftInduction leftBalanced leftResult) leftPromoted,
                  IndexPlan.popMax_balanced
                    (middleInduction middleBalanced middleResult) middlePromoted,
                  rightInduction rightBalanced rightResult, ?_, ?_⟩
                · rw [IndexPlan.popMax_height leftPromoted,
                    IndexPlan.popMax_height middlePromoted,
                    IndexPlan.ofPlan_height leftResult,
                    IndexPlan.ofPlan_height middleResult]
                  exact leftHeight
                · rw [IndexPlan.popMax_height middlePromoted,
                    IndexPlan.ofPlan_height middleResult,
                    IndexPlan.ofPlan_height rightResult]
                  exact rightHeight

def buildIndex (leaves : List (List (List UInt8))) : Option IndexPlan := do
  let topology ← build leaves
  IndexPlan.ofPlan topology

theorem buildIndex_toCells {leaves : List (List (List UInt8))}
    {plan : IndexPlan} (built : buildIndex leaves = some plan) :
    plan.toCells = leaves.flatten := by
  unfold buildIndex at built
  cases topologyResult : build leaves with
  | none => simp [topologyResult] at built
  | some topology =>
    simp only [topologyResult, Option.bind_eq_bind, Option.bind] at built
    rw [IndexPlan.ofPlan_toCells built, build_toCells topologyResult]

theorem buildIndex_balanced {leaves : List (List (List UInt8))}
    {plan : IndexPlan} (built : buildIndex leaves = some plan) : plan.Balanced := by
  unfold buildIndex at built
  cases topologyResult : build leaves with
  | none => simp [topologyResult] at built
  | some topology =>
    simp only [topologyResult, Option.bind_eq_bind, Option.bind] at built
    exact IndexPlan.ofPlan_balanced (build_balanced topologyResult) built

end RecursivePageBTree

end SQLeanite
