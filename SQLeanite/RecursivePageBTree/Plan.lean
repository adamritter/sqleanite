import SQLeanite.CoreFile.Page

namespace SQLeanite
namespace RecursivePageBTree

inductive Plan where
  | leaf (cells : List (List UInt8))
  | branch2 (left right : Plan)
  | branch3 (left middle right : Plan)
  deriving Repr

def Plan.toCells : Plan → List (List UInt8)
  | .leaf cells => cells
  | .branch2 left right => left.toCells ++ right.toCells
  | .branch3 left middle right =>
      left.toCells ++ middle.toCells ++ right.toCells

def Plan.pageCount : Plan → Nat
  | .leaf _ => 1
  | .branch2 left right => 1 + left.pageCount + right.pageCount
  | .branch3 left middle right =>
      1 + left.pageCount + middle.pageCount + right.pageCount

/-- Replace leaf payloads from left to right without changing the page graph.
The returned suffix is the input not consumed by the existing leaf slots.
This is the topology-preserving operation needed when fixed-width provisional
overflow pointers are replaced by their final page numbers. -/
def Plan.replaceCells : Plan → List (List UInt8) → Plan × List (List UInt8)
  | .leaf previous, cells =>
      (.leaf (cells.take previous.length), cells.drop previous.length)
  | .branch2 left right, cells =>
      let (left', afterLeft) := left.replaceCells cells
      let (right', remaining) := right.replaceCells afterLeft
      (.branch2 left' right', remaining)
  | .branch3 left middle right, cells =>
      let (left', afterLeft) := left.replaceCells cells
      let (middle', afterMiddle) := middle.replaceCells afterLeft
      let (right', remaining) := right.replaceCells afterMiddle
      (.branch3 left' middle' right', remaining)

def Plan.withCells (plan : Plan) (cells : List (List UInt8)) : Plan :=
  (plan.replaceCells cells).1

def Plan.withCells? (plan : Plan) (cells : List (List UInt8)) : Option Plan :=
  if _sameCardinality : cells.length = plan.toCells.length then
    some (plan.withCells cells)
  else none

theorem Plan.replaceCells_pageCount (plan : Plan)
    (cells : List (List UInt8)) :
    (plan.replaceCells cells).1.pageCount = plan.pageCount := by
  induction plan generalizing cells with
  | leaf => rfl
  | branch2 left right leftInduction rightInduction =>
      simp [Plan.replaceCells, Plan.pageCount, leftInduction, rightInduction]
  | branch3 left middle right leftInduction middleInduction rightInduction =>
      simp [Plan.replaceCells, Plan.pageCount, leftInduction,
        middleInduction, rightInduction]

theorem Plan.withCells_pageCount (plan : Plan) (cells : List (List UInt8)) :
    (plan.withCells cells).pageCount = plan.pageCount := by
  exact plan.replaceCells_pageCount cells

theorem Plan.replaceCells_contents (plan : Plan)
    (cells : List (List UInt8)) :
    (plan.replaceCells cells).1.toCells ++
        (plan.replaceCells cells).2 = cells := by
  induction plan generalizing cells with
  | leaf previous =>
      simp [Plan.replaceCells, Plan.toCells, List.take_append_drop]
  | branch2 left right leftInduction rightInduction =>
      simp [Plan.replaceCells, Plan.toCells, leftInduction, rightInduction,
        List.append_assoc]
  | branch3 left middle right leftInduction middleInduction rightInduction =>
      simp [Plan.replaceCells, Plan.toCells, leftInduction, middleInduction,
        rightInduction, List.append_assoc]

theorem Plan.replaceCells_remaining_length (plan : Plan)
    (cells : List (List UInt8)) :
    (plan.replaceCells cells).2.length = cells.length - plan.toCells.length := by
  induction plan generalizing cells with
  | leaf previous =>
      simp [Plan.replaceCells, Plan.toCells]
  | branch2 left right leftInduction rightInduction =>
      simp only [Plan.replaceCells, Plan.toCells, List.length_append]
      rw [rightInduction, leftInduction]
      omega
  | branch3 left middle right leftInduction middleInduction rightInduction =>
      simp only [Plan.replaceCells, Plan.toCells, List.length_append]
      rw [rightInduction, middleInduction, leftInduction]
      omega

theorem Plan.withCells_toCells {plan : Plan} {cells : List (List UInt8)}
    (sameLength : cells.length = plan.toCells.length) :
    (plan.withCells cells).toCells = cells := by
  have contents := plan.replaceCells_contents cells
  have remainingLength := plan.replaceCells_remaining_length cells
  rw [sameLength, Nat.sub_self] at remainingLength
  have remainingEmpty : (plan.replaceCells cells).2 = [] :=
    List.length_eq_zero_iff.mp remainingLength
  simpa [Plan.withCells, remainingEmpty] using contents

theorem Plan.withCells?_pageCount {plan updated : Plan}
    {cells : List (List UInt8)}
    (replaced : plan.withCells? cells = some updated) :
    updated.pageCount = plan.pageCount := by
  unfold Plan.withCells? at replaced
  split at replaced
  next =>
    injection replaced with equal
    rw [← equal]
    exact plan.withCells_pageCount cells
  next => contradiction

theorem Plan.withCells?_toCells {plan updated : Plan}
    {cells : List (List UInt8)}
    (replaced : plan.withCells? cells = some updated) :
    updated.toCells = cells := by
  unfold Plan.withCells? at replaced
  split at replaced
  next sameLength =>
    injection replaced with equal
    rw [← equal]
    exact Plan.withCells_toCells sameLength
  next => contradiction

theorem Plan.pageCount_pos (plan : Plan) : 0 < plan.pageCount := by
  cases plan <;> simp only [Plan.pageCount] <;> omega

def Plan.height : Plan → Nat
  | .leaf _ => 0
  | .branch2 left _ => left.height + 1
  | .branch3 left _ _ => left.height + 1

def Plan.Balanced : Plan → Prop
  | .leaf _ => True
  | .branch2 left right =>
      left.Balanced ∧ right.Balanced ∧ left.height = right.height
  | .branch3 left middle right =>
      left.Balanced ∧ middle.Balanced ∧ right.Balanced ∧
      left.height = middle.height ∧ middle.height = right.height

def Plan.checkBalanced : Plan → Bool
  | .leaf _ => true
  | .branch2 left right =>
      left.checkBalanced && right.checkBalanced && decide (left.height = right.height)
  | .branch3 left middle right =>
      left.checkBalanced && middle.checkBalanced && right.checkBalanced &&
        decide (left.height = middle.height) && decide (middle.height = right.height)

theorem Plan.checkBalanced_iff (plan : Plan) :
    plan.checkBalanced = true ↔ plan.Balanced := by
  induction plan with
  | leaf => simp [Plan.checkBalanced, Plan.Balanced]
  | branch2 left right leftInduction rightInduction =>
      simp [Plan.checkBalanced, Plan.Balanced, leftInduction, rightInduction,
        and_assoc]
  | branch3 left middle right leftInduction middleInduction rightInduction =>
      simp [Plan.checkBalanced, Plan.Balanced, leftInduction, middleInduction,
        rightInduction, and_assoc]

/-- Combine one same-height layer.  The explicit four-node case prevents the
tail from becoming a singleton: every non-root interior node has two or three
children. -/
def combineLevel : List Plan → List Plan
  | [] => []
  | [only] => [only]
  | [first, second] => [.branch2 first second]
  | [first, second, third] => [.branch3 first second third]
  | [first, second, third, fourth] =>
      [.branch2 first second, .branch2 third fourth]
  | first :: second :: third :: remaining =>
      .branch3 first second third :: combineLevel remaining

theorem combineLevel_toCells : (nodes : List Plan) →
    (combineLevel nodes).flatMap Plan.toCells = nodes.flatMap Plan.toCells
  | [] => rfl
  | [only] => rfl
  | [first, second] => by simp [combineLevel, Plan.toCells]
  | [first, second, third] => by simp [combineLevel, Plan.toCells]
  | [first, second, third, fourth] => by
      simp [combineLevel, Plan.toCells, List.append_assoc]
  | first :: second :: third :: fourth :: fifth :: remaining => by
      simp only [combineLevel, List.flatMap_cons, Plan.toCells]
      rw [combineLevel_toCells (fourth :: fifth :: remaining)]
      simp [List.append_assoc]

def LayerAt (height : Nat) (nodes : List Plan) : Prop :=
  ∀ node ∈ nodes, node.Balanced ∧ node.height = height

private theorem combineLevel_layer : ∀ (nodes : List Plan) (height : Nat),
    2 ≤ nodes.length → LayerAt height nodes →
      LayerAt (height + 1) (combineLevel nodes)
  | [], _, enough, _ => by simp at enough
  | [_], _, enough, _ => by simp at enough
  | [first, second], height, _, layer => by
      have firstAt := layer first (by simp)
      have secondAt := layer second (by simp)
      intro node member
      simp only [combineLevel, List.mem_singleton] at member
      subst node
      simp [Plan.Balanced, Plan.height, firstAt, secondAt]
  | [first, second, third], height, _, layer => by
      have firstAt := layer first (by simp)
      have secondAt := layer second (by simp)
      have thirdAt := layer third (by simp)
      intro node member
      simp only [combineLevel, List.mem_singleton] at member
      subst node
      simp [Plan.Balanced, Plan.height, firstAt, secondAt, thirdAt]
  | [first, second, third, fourth], height, _, layer => by
      have firstAt := layer first (by simp)
      have secondAt := layer second (by simp)
      have thirdAt := layer third (by simp)
      have fourthAt := layer fourth (by simp)
      intro node member
      simp only [combineLevel, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp [Plan.Balanced, Plan.height, firstAt, secondAt]
      · simp [Plan.Balanced, Plan.height, thirdAt, fourthAt]
  | first :: second :: third :: fourth :: fifth :: remaining, height, _, layer => by
      have firstAt := layer first (by simp)
      have secondAt := layer second (by simp)
      have thirdAt := layer third (by simp)
      have tailLayer : LayerAt height (fourth :: fifth :: remaining) := by
        intro node member
        exact layer node (by simp [member])
      have tailCombined := combineLevel_layer (fourth :: fifth :: remaining)
        height (by simp) tailLayer
      intro node member
      simp only [combineLevel, List.mem_cons] at member
      rcases member with rfl | member
      · simp [Plan.Balanced, Plan.height, firstAt, secondAt, thirdAt]
      · exact tailCombined node member

/-- Fuel-bounded layer construction. `nodes.length` is sufficient for every
nonempty input; retaining fuel makes totality independent of a termination
proof and rejects malformed future grouping changes rather than looping. -/
def buildFromNodes : Nat → List Plan → Option Plan
  | 0, [root] => some root
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [root] => some root
  | fuel + 1, nodes => buildFromNodes fuel (combineLevel nodes)

def build (leaves : List (List (List UInt8))) : Option Plan :=
  buildFromNodes leaves.length (leaves.map Plan.leaf)

theorem buildFromNodes_toCells : ∀ (fuel : Nat) (nodes : List Plan)
    (plan : Plan), buildFromNodes fuel nodes = some plan →
      plan.toCells = nodes.flatMap Plan.toCells
  | 0, [], _, built => by simp [buildFromNodes] at built
  | 0, [root], plan, built => by
      simp only [buildFromNodes, Option.some.injEq] at built
      subst plan
      simp
  | 0, first :: second :: nodes, _, built => by
      simp [buildFromNodes] at built
  | fuel + 1, [], _, built => by simp [buildFromNodes] at built
  | fuel + 1, [root], plan, built => by
      simp only [buildFromNodes, Option.some.injEq] at built
      subst plan
      simp
  | fuel + 1, first :: second :: nodes, plan, built => by
      have recursive := buildFromNodes_toCells fuel
        (combineLevel (first :: second :: nodes)) plan (by
          simpa [buildFromNodes] using built)
      rw [recursive, combineLevel_toCells]

theorem buildFromNodes_balanced : ∀ (fuel : Nat) (nodes : List Plan)
    (plan : Plan), (∃ height, LayerAt height nodes) →
      buildFromNodes fuel nodes = some plan → plan.Balanced
  | 0, [], _, _, built => by simp [buildFromNodes] at built
  | 0, [root], plan, layer, built => by
      simp only [buildFromNodes, Option.some.injEq] at built
      subst plan
      rcases layer with ⟨height, layer⟩
      exact (layer root (by simp)).1
  | 0, first :: second :: nodes, _, _, built => by
      simp [buildFromNodes] at built
  | fuel + 1, [], _, _, built => by simp [buildFromNodes] at built
  | fuel + 1, [root], plan, layer, built => by
      simp only [buildFromNodes, Option.some.injEq] at built
      subst plan
      rcases layer with ⟨height, layer⟩
      exact (layer root (by simp)).1
  | fuel + 1, first :: second :: nodes, plan, layer, built => by
      rcases layer with ⟨height, layer⟩
      apply buildFromNodes_balanced fuel (combineLevel (first :: second :: nodes))
        plan ⟨height + 1, combineLevel_layer _ height (by simp) layer⟩
      simpa [buildFromNodes] using built

theorem build_toCells {leaves : List (List (List UInt8))} {plan : Plan}
    (built : build leaves = some plan) : plan.toCells = leaves.flatten := by
  unfold build at built
  have preserved := buildFromNodes_toCells leaves.length
    (leaves.map Plan.leaf) plan built
  simpa [List.flatMap_map, Function.comp_def, Plan.toCells, List.flatten]
    using preserved

theorem build_balanced {leaves : List (List (List UInt8))} {plan : Plan}
    (built : build leaves = some plan) : plan.Balanced := by
  apply buildFromNodes_balanced leaves.length (leaves.map Plan.leaf) plan
  · refine ⟨0, ?_⟩
    intro node member
    rcases List.mem_map.mp member with ⟨leaf, _, rfl⟩
    simp [Plan.Balanced, Plan.height]
  · exact built

/-- Immediate child roots under preorder allocation. -/
def Plan.childRoots (startPage : Nat) : Plan → List Nat
  | .leaf _ => []
  | .branch2 left _ =>
      [startPage + 1, startPage + 1 + left.pageCount]
  | .branch3 left middle _ =>
      [startPage + 1,
       startPage + 1 + left.pageCount,
       startPage + 1 + left.pageCount + middle.pageCount]

theorem Plan.childRoots_bounded (plan : Plan) (startPage child : Nat)
    (member : child ∈ plan.childRoots startPage) :
    startPage < child ∧ child < startPage + plan.pageCount := by
  cases plan with
  | leaf cells => simp [Plan.childRoots] at member
  | branch2 left right =>
      simp only [Plan.childRoots, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      all_goals
        have leftPositive := left.pageCount_pos
        have rightPositive := right.pageCount_pos
        simp only [Plan.pageCount]
        omega
  | branch3 left middle right =>
      simp only [Plan.childRoots, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals
        have leftPositive := left.pageCount_pos
        have middlePositive := middle.pageCount_pos
        have rightPositive := right.pageCount_pos
        simp only [Plan.pageCount]
        omega

structure PageReference where
  parent : Nat
  child : Nat
  deriving DecidableEq, Repr

def Plan.references (startPage : Nat) : Plan → List PageReference
  | .leaf _ => []
  | .branch2 left right =>
      let leftRoot := startPage + 1
      let rightRoot := leftRoot + left.pageCount
      [⟨startPage, leftRoot⟩, ⟨startPage, rightRoot⟩] ++
        left.references leftRoot ++ right.references rightRoot
  | .branch3 left middle right =>
      let leftRoot := startPage + 1
      let middleRoot := leftRoot + left.pageCount
      let rightRoot := middleRoot + middle.pageCount
      [⟨startPage, leftRoot⟩, ⟨startPage, middleRoot⟩,
        ⟨startPage, rightRoot⟩] ++
        left.references leftRoot ++ middle.references middleRoot ++
        right.references rightRoot

theorem Plan.references_bounded (plan : Plan) (startPage : Nat)
    (reference : PageReference) (member : reference ∈ plan.references startPage) :
    startPage ≤ reference.parent ∧
    reference.parent < startPage + plan.pageCount ∧
    startPage < reference.child ∧
    reference.child < startPage + plan.pageCount := by
  induction plan generalizing startPage with
  | leaf cells => simp [Plan.references] at member
  | branch2 left right leftInduction rightInduction =>
      simp only [Plan.references, List.mem_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at member
      rcases member with beforeRight | rightMember
      · rcases beforeRight with immediate | leftMember
        · rcases immediate with rfl | rfl
          all_goals
            have leftPositive := left.pageCount_pos
            have rightPositive := right.pageCount_pos
            simp only [Plan.pageCount]
            omega
        · have bounded := leftInduction (startPage := startPage + 1)
            leftMember
          rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
          simp only [Plan.pageCount]
          omega
      · have bounded := rightInduction
          (startPage := startPage + 1 + left.pageCount) rightMember
        rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
        simp only [Plan.pageCount]
        omega
  | branch3 left middle right leftInduction middleInduction rightInduction =>
      simp only [Plan.references, List.mem_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at member
      rcases member with beforeRight | rightMember
      · rcases beforeRight with beforeMiddle | middleMember
        · rcases beforeMiddle with immediate | leftMember
          · rcases immediate with rfl | rfl | rfl
            all_goals
              have leftPositive := left.pageCount_pos
              have middlePositive := middle.pageCount_pos
              have rightPositive := right.pageCount_pos
              simp only [Plan.pageCount]
              omega
          · have bounded := leftInduction (startPage := startPage + 1)
              leftMember
            rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
            simp only [Plan.pageCount]
            omega
        · have bounded := middleInduction
            (startPage := startPage + 1 + left.pageCount)
            middleMember
          rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
          simp only [Plan.pageCount]
          omega
      · have bounded := rightInduction
          (startPage := startPage + 1 + left.pageCount + middle.pageCount)
          rightMember
        rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
        simp only [Plan.pageCount]
        omega

def separatorKey? (plan : Plan) : Option Nat :=
  CoreFile.leafSeparatorKey? plan.toCells

def boundedU32? (value : Nat) : Option FileFormat.U32Value :=
  if bound : value < 2 ^ 32 then some ⟨value, by simpa using bound⟩ else none

def boundedU64? (value : Nat) : Option FileFormat.U64Value :=
  if bound : value < 2 ^ 64 then some ⟨value, by simpa using bound⟩ else none

def interiorCell? (childPage key : Nat) : Option (List UInt8) := do
  let child ← boundedU32? childPage
  let separator ← boundedU64? key
  some (FileFormat.encodeU32Bytes child ++
    FileFormat.encodeVarint separator)

def interiorPage? (children : List (Nat × Nat)) (rightmostPage : Nat) :
    Option CoreFile.Page := do
  let rightmost ← boundedU32? rightmostPage
  let cells ← children.mapM fun child => interiorCell? child.1 child.2
  if fits : PhysicalTableBTree.InteriorPageFit cells then
    some {
      bytes := PhysicalTableBTree.interiorPageBody rightmost cells
      length_eq := PhysicalTableBTree.interiorPageBody_length rightmost cells fits }
  else none

end RecursivePageBTree

end SQLeanite
