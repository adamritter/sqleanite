import SQLeanite.CoreFile

namespace SQLeanite
namespace RecursivePageBTree

/-!
# Arbitrary-depth SQLite table-page plans

This module is the physical refinement layer between a sequence of already
encoded table cells and SQLite's page graph.  Leaves retain the page-sized
chunks produced by `CellPagination`; interior pages form a capacity-three
2-3 tree.  Page allocation is preorder and every child reference is derived
from `pageCount`, rather than accepted as an unchecked integer.
-/

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

/-- Encode a plan in preorder.  Root page number is `startPage`; every child
number is calculated from the exact size of the preceding subtree. -/
def Plan.encodePagesFrom (startPage : Nat) : Plan → Option (List CoreFile.Page)
  | .leaf cells => do
      let page ← CoreFile.tableLeafPage? cells
      some [page]
  | .branch2 left right => do
      let leftKey ← separatorKey? left
      let leftRoot := startPage + 1
      let rightRoot := leftRoot + left.pageCount
      let root ← interiorPage? [(leftRoot, leftKey)] rightRoot
      let leftPages ← left.encodePagesFrom leftRoot
      let rightPages ← right.encodePagesFrom rightRoot
      some (root :: (leftPages ++ rightPages))
  | .branch3 left middle right => do
      let leftKey ← separatorKey? left
      let middleKey ← separatorKey? middle
      let leftRoot := startPage + 1
      let middleRoot := leftRoot + left.pageCount
      let rightRoot := middleRoot + middle.pageCount
      let root ← interiorPage?
        [(leftRoot, leftKey), (middleRoot, middleKey)] rightRoot
      let leftPages ← left.encodePagesFrom leftRoot
      let middlePages ← middle.encodePagesFrom middleRoot
      let rightPages ← right.encodePagesFrom rightRoot
      some (root :: (leftPages ++ middlePages ++ rightPages))

theorem Plan.encodePagesFrom_length {plan : Plan} {startPage : Nat}
    {pages : List CoreFile.Page} (encoded : plan.encodePagesFrom startPage = some pages) :
    pages.length = plan.pageCount := by
  induction plan generalizing startPage pages with
  | leaf cells =>
      simp only [Plan.encodePagesFrom, Option.bind_eq_bind, Option.bind] at encoded
      cases pageResult : CoreFile.tableLeafPage? cells with
      | none => simp [pageResult] at encoded
      | some page =>
          simp only [pageResult, Option.some.injEq] at encoded
          subst pages
          rfl
  | branch2 left right leftInduction rightInduction =>
      simp only [Plan.encodePagesFrom, Option.bind_eq_bind, Option.bind] at encoded
      cases leftKeyResult : separatorKey? left with
      | none => simp [leftKeyResult] at encoded
      | some leftKey =>
        simp only [leftKeyResult] at encoded
        cases rootResult : interiorPage?
            [(startPage + 1, leftKey)]
            (startPage + 1 + left.pageCount) with
        | none => simp [rootResult] at encoded
        | some root =>
          simp only [rootResult] at encoded
          cases leftResult : left.encodePagesFrom (startPage + 1) with
          | none => simp [leftResult] at encoded
          | some leftPages =>
            simp only [leftResult] at encoded
            cases rightResult : right.encodePagesFrom
                (startPage + 1 + left.pageCount) with
            | none => simp [rightResult] at encoded
            | some rightPages =>
              simp only [rightResult, Option.some.injEq] at encoded
              subst pages
              simp only [List.length_cons, List.length_append, Plan.pageCount]
              rw [leftInduction leftResult, rightInduction rightResult]
              omega
  | branch3 left middle right leftInduction middleInduction rightInduction =>
      simp only [Plan.encodePagesFrom, Option.bind_eq_bind, Option.bind] at encoded
      cases leftKeyResult : separatorKey? left with
      | none => simp [leftKeyResult] at encoded
      | some leftKey =>
        simp only [leftKeyResult] at encoded
        cases middleKeyResult : separatorKey? middle with
        | none => simp [middleKeyResult] at encoded
        | some middleKey =>
          simp only [middleKeyResult] at encoded
          cases rootResult : interiorPage?
              [(startPage + 1, leftKey),
                (startPage + 1 + left.pageCount, middleKey)]
              (startPage + 1 + left.pageCount + middle.pageCount) with
          | none => simp [rootResult] at encoded
          | some root =>
            simp only [rootResult] at encoded
            cases leftResult : left.encodePagesFrom (startPage + 1) with
            | none => simp [leftResult] at encoded
            | some leftPages =>
              simp only [leftResult] at encoded
              cases middleResult : middle.encodePagesFrom
                  (startPage + 1 + left.pageCount) with
              | none => simp [middleResult] at encoded
              | some middlePages =>
                simp only [middleResult] at encoded
                cases rightResult : right.encodePagesFrom
                    (startPage + 1 + left.pageCount + middle.pageCount) with
                | none => simp [rightResult] at encoded
                | some rightPages =>
                  simp only [rightResult, Option.some.injEq] at encoded
                  subst pages
                  simp only [List.length_cons, List.length_append, Plan.pageCount]
                  rw [leftInduction leftResult, middleInduction middleResult,
                    rightInduction rightResult]
                  omega

/-- A complete arbitrary-depth SQLite image for the one-table/no-index slice.
This is an integration seam, not a second logical codec: catalog and leaf cells
come from `CoreFile`, while only table-page topology is replaced. -/
def encodeSingleTable (database : Core.Database) : Option CoreFile.Image := do
  let table ← match database.tables with
    | [table] => some table
    | _ => none
  if _noIndexes : table.indexes = [] then
    let leaves ← CoreFile.tableLeaves table
    let plan ← build leaves
    let tablePages ← plan.encodePagesFrom 2
    let total := 1 + tablePages.length
    if countBound : total < 2 ^ 32 then
      let count : FileFormat.U32Value := ⟨total, by simpa using countBound⟩
      let entry : CoreFile.CatalogEntry := {
        kind := "table"
        name := table.schema.name
        table := table.schema.name
        rootPage := 2
        sql := CoreFile.tableSQL table }
      let schema ← CoreFile.schemaPageForEntries? [entry] count
      some ⟨database, schema :: tablePages⟩
    else none
  else none

theorem encodeSingleTable_pageCount {database : Core.Database}
    {image : CoreFile.Image} (encoded : encodeSingleTable database = some image) :
    ∃ table leaves plan tablePages,
      database.tables = [table] ∧
      CoreFile.tableLeaves table = some leaves ∧
      build leaves = some plan ∧
      plan.encodePagesFrom 2 = some tablePages ∧
      image.pageCount = 1 + plan.pageCount := by
  unfold encodeSingleTable at encoded
  cases tablesShape : database.tables with
  | nil => simp [tablesShape] at encoded
  | cons table tables =>
    cases tailShape : tables with
    | cons next rest => simp [tablesShape, tailShape] at encoded
    | nil =>
      simp only [tablesShape, tailShape, Option.bind_eq_bind, Option.bind] at encoded
      split at encoded
      next noIndexes =>
        cases leavesResult : CoreFile.tableLeaves table with
        | none => simp [leavesResult] at encoded
        | some leaves =>
          simp only [leavesResult] at encoded
          cases planResult : build leaves with
          | none => simp [planResult] at encoded
          | some plan =>
            simp only [planResult] at encoded
            cases pagesResult : plan.encodePagesFrom 2 with
            | none => simp [pagesResult] at encoded
            | some tablePages =>
              simp only [pagesResult] at encoded
              split at encoded
              next countBound =>
                cases schemaResult : CoreFile.schemaPageForEntries? [
                    { kind := "table", name := table.schema.name,
                      table := table.schema.name, rootPage := 2,
                      sql := CoreFile.tableSQL table }]
                    ⟨1 + tablePages.length, by simpa using countBound⟩ with
                | none => simp [schemaResult] at encoded
                | some schema =>
                  simp only [schemaResult, Option.some.injEq] at encoded
                  subst image
                  refine ⟨table, leaves, plan, tablePages, ?_, leavesResult,
                    planResult, pagesResult, ?_⟩
                  · simp [tablesShape, tailShape]
                  · simp only [CoreFile.Image.pageCount, List.length_cons]
                    rw [plan.encodePagesFrom_length pagesResult]
                    omega
              next => contradiction
      next => contradiction

/-! ## Recursive physical index trees -/

inductive IndexPlan where
  | leaf (cells : List (List UInt8))
  | branch2 (left : IndexPlan) (separator : List UInt8) (right : IndexPlan)
  | branch3 (left : IndexPlan) (firstSeparator : List UInt8)
      (middle : IndexPlan) (secondSeparator : List UInt8) (right : IndexPlan)
  deriving Repr

/-- In-order index contents include promoted interior keys exactly once. -/
def IndexPlan.toCells : IndexPlan → List (List UInt8)
  | .leaf cells => cells
  | .branch2 left separator right =>
      left.toCells ++ [separator] ++ right.toCells
  | .branch3 left firstSeparator middle secondSeparator right =>
      left.toCells ++ [firstSeparator] ++ middle.toCells ++
        [secondSeparator] ++ right.toCells

def IndexPlan.pageCount : IndexPlan → Nat
  | .leaf _ => 1
  | .branch2 left _ right => 1 + left.pageCount + right.pageCount
  | .branch3 left _ middle _ right =>
      1 + left.pageCount + middle.pageCount + right.pageCount

/-- Replace index entries in their in-order positions while retaining the
existing page graph. Interior entries are consumed explicitly: in a SQLite
index B-tree they are promoted records, not synthetic separators. -/
def IndexPlan.replaceCells : IndexPlan → List (List UInt8) →
    Option (IndexPlan × List (List UInt8))
  | .leaf previous, cells =>
      some (.leaf (cells.take previous.length), cells.drop previous.length)
  | .branch2 left _ right, cells => do
      let (left', afterLeft) ← left.replaceCells cells
      let separator :: afterSeparator := afterLeft | none
      let (right', remaining) ← right.replaceCells afterSeparator
      some (.branch2 left' separator right', remaining)
  | .branch3 left _ middle _ right, cells => do
      let (left', afterLeft) ← left.replaceCells cells
      let firstSeparator :: afterFirst := afterLeft | none
      let (middle', afterMiddle) ← middle.replaceCells afterFirst
      let secondSeparator :: afterSecond := afterMiddle | none
      let (right', remaining) ← right.replaceCells afterSecond
      some (.branch3 left' firstSeparator middle' secondSeparator right', remaining)

def IndexPlan.withCells? (plan : IndexPlan) (cells : List (List UInt8)) :
    Option IndexPlan :=
  if _sameCardinality : cells.length = plan.toCells.length then do
    let (updated, remaining) ← plan.replaceCells cells
    if remaining.isEmpty then some updated else none
  else none

theorem IndexPlan.replaceCells_pageCount {plan updated : IndexPlan}
    {cells remaining : List (List UInt8)}
    (replaced : plan.replaceCells cells = some (updated, remaining)) :
    updated.pageCount = plan.pageCount := by
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
                  simp only [IndexPlan.pageCount]
                  rw [leftInduction leftResult, rightInduction rightResult]
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
                          simp only [rightResult, Option.some.injEq,
                            Prod.mk.injEq] at replaced
                          rcases replaced with ⟨rfl, rfl⟩
                          simp only [IndexPlan.pageCount]
                          rw [leftInduction leftResult,
                            middleInduction middleResult,
                            rightInduction rightResult]

theorem IndexPlan.withCells?_pageCount {plan updated : IndexPlan}
    {cells : List (List UInt8)}
    (replaced : plan.withCells? cells = some updated) :
    updated.pageCount = plan.pageCount := by
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
          exact IndexPlan.replaceCells_pageCount result
        next => contradiction
  next => contradiction

theorem IndexPlan.replaceCells_contents {plan updated : IndexPlan}
    {cells remaining : List (List UInt8)}
    (replaced : plan.replaceCells cells = some (updated, remaining)) :
    updated.toCells ++ remaining = cells := by
  induction plan generalizing cells updated remaining with
  | leaf previous =>
      simp only [IndexPlan.replaceCells, Option.some.injEq,
        Prod.mk.injEq] at replaced
      rw [← replaced.1, ← replaced.2]
      simp [IndexPlan.toCells, List.take_append_drop]
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
                  have leftContents := leftInduction leftResult
                  have rightContents := rightInduction rightResult
                  simp only [IndexPlan.toCells]
                  rw [List.append_assoc, List.append_assoc, rightContents]
                  simpa [List.append_assoc] using leftContents
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
                          simp only [rightResult, Option.some.injEq,
                            Prod.mk.injEq] at replaced
                          rcases replaced with ⟨rfl, rfl⟩
                          have leftContents := leftInduction leftResult
                          have middleContents := middleInduction middleResult
                          have rightContents := rightInduction rightResult
                          simp only [IndexPlan.toCells]
                          rw [List.append_assoc, List.append_assoc,
                            List.append_assoc, List.append_assoc, rightContents]
                          have middleNormalized :
                              middle'.toCells ++ ([second] ++ afterSecond) =
                                afterFirst := by
                            simpa [List.append_assoc] using middleContents
                          rw [middleNormalized]
                          simpa [List.append_assoc] using leftContents

theorem IndexPlan.withCells?_toCells {plan updated : IndexPlan}
    {cells : List (List UInt8)}
    (replaced : plan.withCells? cells = some updated) :
    updated.toCells = cells := by
  unfold IndexPlan.withCells? at replaced
  split at replaced
  next =>
    cases result : plan.replaceCells cells with
    | none => simp [result] at replaced
    | some pair =>
        rcases pair with ⟨candidate, remaining⟩
        simp only [result, Option.bind_eq_bind, Option.bind] at replaced
        split at replaced
        next remainingEmpty =>
          injection replaced with equal
          subst updated
          have empty : remaining = [] := by
            exact List.isEmpty_iff.mp remainingEmpty
          simpa [empty] using IndexPlan.replaceCells_contents result
        next => contradiction
  next => contradiction

/-- Insert one cell at an in-order position. The surrounding physical index
topology is unchanged; callers accept the result only when re-encoding the
affected leaf still fits its SQLite page. -/
def insertCellAt (position : Nat) (cell : List UInt8)
    (cells : List (List UInt8)) : List (List UInt8) :=
  cells.take position ++ cell :: cells.drop position

theorem insertCellAt_append_left (left right : List (List UInt8))
    (position : Nat) (cell : List UInt8) (bound : position ≤ left.length) :
    insertCellAt position cell (left ++ right) =
      insertCellAt position cell left ++ right := by
  simp [insertCellAt, List.take_append_of_le_length bound,
    List.drop_append_of_le_length bound, List.append_assoc]

theorem insertCellAt_append_right (left right : List (List UInt8))
    (position : Nat) (cell : List UInt8) (after : left.length ≤ position) :
    insertCellAt position cell (left ++ right) =
      left ++ insertCellAt (position - left.length) cell right := by
  rw [insertCellAt, List.take_append,
    List.drop_append, List.take_of_length_le after,
    List.drop_eq_nil_of_le after]
  simp [insertCellAt, List.append_assoc]

theorem insertCellAt_cons_of_pos (head : List UInt8)
    (tail : List (List UInt8)) (position : Nat) (cell : List UInt8)
    (positive : 0 < position) :
    insertCellAt position cell (head :: tail) =
      head :: insertCellAt (position - 1) cell tail := by
  cases position with
  | zero => contradiction
  | succ position => simp [insertCellAt]

def IndexPlan.insertAt? (plan : IndexPlan) (position : Nat)
    (cell : List UInt8) : Option IndexPlan :=
  match plan with
  | .leaf cells =>
      if position ≤ cells.length then
        some (.leaf (insertCellAt position cell cells))
      else none
  | .branch2 left separator right =>
      let leftLength := left.toCells.length
      if position ≤ leftLength then do
        let updated ← left.insertAt? position cell
        some (.branch2 updated separator right)
      else do
        let updated ← right.insertAt? (position - (leftLength + 1)) cell
        some (.branch2 left separator updated)
  | .branch3 left firstSeparator middle secondSeparator right =>
      let leftLength := left.toCells.length
      let middleEnd := leftLength + 1 + middle.toCells.length
      if position ≤ leftLength then do
        let updated ← left.insertAt? position cell
        some (.branch3 updated firstSeparator middle secondSeparator right)
      else if position ≤ middleEnd then do
        let updated ← middle.insertAt? (position - (leftLength + 1)) cell
        some (.branch3 left firstSeparator updated secondSeparator right)
      else do
        let updated ← right.insertAt? (position - (middleEnd + 1)) cell
        some (.branch3 left firstSeparator middle secondSeparator updated)

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

/-- The single owner of an index page topology.  Construction performs the
byte-capacity pagination once; later payload-pointer resolution may replace
cells, but cannot silently choose a different page graph. -/
structure IndexStore where
  plan : IndexPlan
  cells : List (List UInt8)
  balanced : plan.Balanced
  represents : plan.toCells = cells

def IndexStore.build? (cells : List (List UInt8)) : Option IndexStore :=
  let leaves := CellPagination.paginateCells cells
  match built : buildIndex leaves with
  | none => none
  | some plan => some {
      plan
      cells
      balanced := buildIndex_balanced built
      represents := (buildIndex_toCells built).trans
        (CellPagination.flatten_paginateCells cells) }

theorem IndexStore.build?_cells {cells : List (List UInt8)}
    {store : IndexStore} (built : IndexStore.build? cells = some store) :
    store.cells = cells := by
  simp only [IndexStore.build?] at built
  split at built
  next => contradiction
  next plan result =>
    simp only [Option.some.injEq] at built
    subst store
    rfl

theorem IndexStore.build?_balanced {cells : List (List UInt8)}
    {store : IndexStore} (_built : IndexStore.build? cells = some store) :
    store.plan.Balanced := by
  exact store.balanced

/-- Retarget bytes in in-order positions without recomputing pagination.
This is the index analogue of retaining `PersistentPageTree.Store` identities
while changing its logical witness. -/
def IndexStore.retarget? (store : IndexStore)
    (cells : List (List UInt8)) : Option IndexStore :=
  match replaced : store.plan.withCells? cells with
  | none => none
  | some plan => some {
      plan
      cells
      balanced := IndexPlan.withCells?_balanced store.balanced replaced
      represents := IndexPlan.withCells?_toCells replaced }

theorem IndexStore.retarget?_pageCount {store updated : IndexStore}
    {cells : List (List UInt8)}
    (retargeted : store.retarget? cells = some updated) :
    updated.plan.pageCount = store.plan.pageCount := by
  unfold IndexStore.retarget? at retargeted
  split at retargeted
  next => contradiction
  next plan replaced =>
    simp only [Option.some.injEq] at retargeted
    subst updated
    exact IndexPlan.withCells?_pageCount replaced

theorem IndexStore.retarget?_represents {store updated : IndexStore}
    {cells : List (List UInt8)}
    (retargeted : store.retarget? cells = some updated) :
    updated.plan.toCells = cells := by
  unfold IndexStore.retarget? at retargeted
  split at retargeted
  next => contradiction
  next plan replaced =>
    simp only [Option.some.injEq] at retargeted
    subst updated
    exact IndexPlan.withCells?_toCells replaced

/-- Insert one encoded index cell while preserving the existing page graph.
The caller still has to prove that the changed leaf serializes within its
SQLite page; failure at that boundary falls back to the bulk encoder. -/
def IndexStore.insertAt? (store : IndexStore) (position : Nat)
    (cell : List UInt8) : Option IndexStore :=
  match inserted : store.plan.insertAt? position cell with
  | none => none
  | some plan => some {
      plan
      cells := insertCellAt position cell store.cells
      balanced := IndexPlan.insertAt?_balanced store.balanced inserted
      represents := by
        rw [IndexPlan.insertAt?_toCells inserted, store.represents] }

theorem IndexStore.insertAt?_pageCount {store updated : IndexStore}
    {position : Nat} {cell : List UInt8}
    (inserted : store.insertAt? position cell = some updated) :
    updated.plan.pageCount = store.plan.pageCount := by
  unfold IndexStore.insertAt? at inserted
  split at inserted
  next => contradiction
  next plan planInserted =>
    simp only [Option.some.injEq] at inserted
    subst updated
    exact IndexPlan.insertAt?_pageCount planInserted

theorem IndexStore.insertAt?_cells {store updated : IndexStore}
    {position : Nat} {cell : List UInt8}
    (inserted : store.insertAt? position cell = some updated) :
    updated.cells = insertCellAt position cell store.cells := by
  unfold IndexStore.insertAt? at inserted
  split at inserted
  next => contradiction
  next =>
    simp only [Option.some.injEq] at inserted
    subst updated
    rfl

theorem IndexStore.insertAt?_represents {store updated : IndexStore}
    {position : Nat} {cell : List UInt8}
    (inserted : store.insertAt? position cell = some updated) :
    updated.plan.toCells = insertCellAt position cell store.cells := by
  rw [updated.represents, IndexStore.insertAt?_cells inserted]

def IndexPlan.references (startPage : Nat) : IndexPlan → List PageReference
  | .leaf _ => []
  | .branch2 left _ right =>
      let leftRoot := startPage + 1
      let rightRoot := leftRoot + left.pageCount
      [⟨startPage, leftRoot⟩, ⟨startPage, rightRoot⟩] ++
        left.references leftRoot ++ right.references rightRoot
  | .branch3 left _ middle _ right =>
      let leftRoot := startPage + 1
      let middleRoot := leftRoot + left.pageCount
      let rightRoot := middleRoot + middle.pageCount
      [⟨startPage, leftRoot⟩, ⟨startPage, middleRoot⟩,
        ⟨startPage, rightRoot⟩] ++
        left.references leftRoot ++ middle.references middleRoot ++
        right.references rightRoot

theorem IndexPlan.references_bounded (plan : IndexPlan) (startPage : Nat)
    (reference : PageReference) (member : reference ∈ plan.references startPage) :
    startPage ≤ reference.parent ∧
    reference.parent < startPage + plan.pageCount ∧
    startPage < reference.child ∧
    reference.child < startPage + plan.pageCount := by
  induction plan generalizing startPage with
  | leaf cells => simp [IndexPlan.references] at member
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.references, List.mem_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at member
      rcases member with beforeRight | rightMember
      · rcases beforeRight with immediate | leftMember
        · rcases immediate with rfl | rfl
          all_goals
            have leftPositive := left.pageCount_pos
            have rightPositive := right.pageCount_pos
            simp only [IndexPlan.pageCount]
            omega
        · have bounded := leftInduction (startPage := startPage + 1)
            leftMember
          rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
          simp only [IndexPlan.pageCount]
          omega
      · have bounded := rightInduction
          (startPage := startPage + 1 + left.pageCount) rightMember
        rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
        simp only [IndexPlan.pageCount]
        omega
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.references, List.mem_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at member
      rcases member with beforeRight | rightMember
      · rcases beforeRight with beforeMiddle | middleMember
        · rcases beforeMiddle with immediate | leftMember
          · rcases immediate with rfl | rfl | rfl
            all_goals
              have leftPositive := left.pageCount_pos
              have middlePositive := middle.pageCount_pos
              have rightPositive := right.pageCount_pos
              simp only [IndexPlan.pageCount]
              omega
          · have bounded := leftInduction (startPage := startPage + 1)
              leftMember
            rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
            simp only [IndexPlan.pageCount]
            omega
        · have bounded := middleInduction
            (startPage := startPage + 1 + left.pageCount) middleMember
          rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
          simp only [IndexPlan.pageCount]
          omega
      · have bounded := rightInduction
          (startPage := startPage + 1 + left.pageCount + middle.pageCount)
          rightMember
        rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
        simp only [IndexPlan.pageCount]
        omega

def indexInteriorPage? (children : List (Nat × List UInt8))
    (rightmostPage : Nat) : Option CoreFile.Page := do
  let rightmost ← boundedU32? rightmostPage
  let cells ← children.mapM fun child => do
    let childPage ← boundedU32? child.1
    some (PhysicalTableBTree.encodeU32Nat childPage.val ++ child.2)
  if fits : PhysicalTableBTree.InteriorPageFit cells then
    some {
      bytes := CoreFile.replaceFirst 2
        (PhysicalTableBTree.interiorPageBody rightmost cells)
      length_eq := by
        rw [CoreFile.replaceFirst_length]
        exact PhysicalTableBTree.interiorPageBody_length rightmost cells fits }
  else none

def IndexPlan.encodePagesFrom (startPage : Nat) :
    IndexPlan → Option (List CoreFile.Page)
  | .leaf cells => do
      let page ← CoreFile.indexLeafPage? cells
      some [page]
  | .branch2 left separator right => do
      let leftRoot := startPage + 1
      let rightRoot := leftRoot + left.pageCount
      let root ← indexInteriorPage? [(leftRoot, separator)] rightRoot
      let leftPages ← left.encodePagesFrom leftRoot
      let rightPages ← right.encodePagesFrom rightRoot
      some (root :: (leftPages ++ rightPages))
  | .branch3 left firstSeparator middle secondSeparator right => do
      let leftRoot := startPage + 1
      let middleRoot := leftRoot + left.pageCount
      let rightRoot := middleRoot + middle.pageCount
      let root ← indexInteriorPage?
        [(leftRoot, firstSeparator), (middleRoot, secondSeparator)] rightRoot
      let leftPages ← left.encodePagesFrom leftRoot
      let middlePages ← middle.encodePagesFrom middleRoot
      let rightPages ← right.encodePagesFrom rightRoot
      some (root :: (leftPages ++ middlePages ++ rightPages))

theorem IndexPlan.encodePagesFrom_length {plan : IndexPlan} {startPage : Nat}
    {pages : List CoreFile.Page} (encoded : plan.encodePagesFrom startPage = some pages) :
    pages.length = plan.pageCount := by
  induction plan generalizing startPage pages with
  | leaf cells =>
      simp only [IndexPlan.encodePagesFrom, Option.bind_eq_bind, Option.bind]
        at encoded
      cases pageResult : CoreFile.indexLeafPage? cells with
      | none => simp [pageResult] at encoded
      | some page =>
        simp only [pageResult, Option.some.injEq] at encoded
        subst pages
        rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.encodePagesFrom, Option.bind_eq_bind, Option.bind]
        at encoded
      cases rootResult : indexInteriorPage?
          [(startPage + 1, separator)]
          (startPage + 1 + left.pageCount) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult] at encoded
        cases leftResult : left.encodePagesFrom (startPage + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases rightResult : right.encodePagesFrom
              (startPage + 1 + left.pageCount) with
          | none => simp [rightResult] at encoded
          | some rightPages =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst pages
            simp only [List.length_cons, List.length_append,
              IndexPlan.pageCount]
            rw [leftInduction leftResult, rightInduction rightResult]
            omega
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.encodePagesFrom, Option.bind_eq_bind, Option.bind]
        at encoded
      cases rootResult : indexInteriorPage?
          [(startPage + 1, firstSeparator),
            (startPage + 1 + left.pageCount, secondSeparator)]
          (startPage + 1 + left.pageCount + middle.pageCount) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult] at encoded
        cases leftResult : left.encodePagesFrom (startPage + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases middleResult : middle.encodePagesFrom
              (startPage + 1 + left.pageCount) with
          | none => simp [middleResult] at encoded
          | some middlePages =>
            simp only [middleResult] at encoded
            cases rightResult : right.encodePagesFrom
                (startPage + 1 + left.pageCount + middle.pageCount) with
            | none => simp [rightResult] at encoded
            | some rightPages =>
              simp only [rightResult, Option.some.injEq] at encoded
              subst pages
              simp only [List.length_cons, List.length_append,
                IndexPlan.pageCount]
              rw [leftInduction leftResult, middleInduction middleResult,
                rightInduction rightResult]
              omega

structure TableEncoding where
  table : Core.Table
  rootPage : Nat
  plan : Plan
  pages : List CoreFile.Page

def encodeTable (rootPage : Nat) (table : Core.Table) : Option TableEncoding := do
  let leaves ← CoreFile.tableLeaves table
  let plan ← build leaves
  let pages ← plan.encodePagesFrom rootPage
  some ⟨table, rootPage, plan, pages⟩

/-- Physical planning refines the table's row-cell sequence, not merely its
length: every encoded cell occurs once and in rowid order. -/
theorem encodeTable_refines {rootPage : Nat} {table : Core.Table}
    {encoding : TableEncoding} (encoded : encodeTable rootPage table = some encoding) :
    ∃ cells leaves,
      CoreFile.tableCells table = some cells ∧
      CoreFile.tableLeaves table = some leaves ∧
      encoding.plan.toCells = cells := by
  unfold encodeTable at encoded
  cases leavesResult : CoreFile.tableLeaves table with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : build leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        unfold CoreFile.tableLeaves at leavesResult
        cases cellsResult : CoreFile.tableCells table with
        | none => simp [cellsResult] at leavesResult
        | some cells =>
          simp only [cellsResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at leavesResult
          subst leaves
          refine ⟨cells, CellPagination.paginateCells cells, rfl, ?_, ?_⟩
          · simp [CoreFile.tableLeaves, cellsResult]
          · rw [build_toCells planResult]
            exact CellPagination.flatten_paginateCells cells

def TableEncoding.catalogEntry (encoding : TableEncoding) : CoreFile.CatalogEntry := {
  kind := "table"
  name := encoding.table.schema.name
  table := encoding.table.schema.name
  rootPage := encoding.rootPage
  sql := CoreFile.tableSQL encoding.table }

theorem encodeTable_table {rootPage : Nat} {table : Core.Table}
    {encoding : TableEncoding} (encoded : encodeTable rootPage table = some encoding) :
    encoding.table = table := by
  unfold encodeTable at encoded
  cases leavesResult : CoreFile.tableLeaves table with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : build leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        rfl

def encodeTables : Nat → List Core.Table → Option (List TableEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let encoded ← encodeTable nextPage table
      let remaining ← encodeTables (nextPage + encoded.plan.pageCount) tables
      some (encoded :: remaining)

def tablePagesOf (encodings : List TableEncoding) : List CoreFile.Page :=
  encodings.flatMap (fun encoding => encoding.pages)

def tableEntriesOf (encodings : List TableEncoding) : List CoreFile.CatalogEntry :=
  encodings.map TableEncoding.catalogEntry

theorem encodeTable_pages_length {rootPage : Nat} {table : Core.Table}
    {encoding : TableEncoding} (encoded : encodeTable rootPage table = some encoding) :
    encoding.pages.length = encoding.plan.pageCount := by
  unfold encodeTable at encoded
  cases leavesResult : CoreFile.tableLeaves table with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : build leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        exact plan.encodePagesFrom_length pagesResult

theorem encodeTables_tables : ∀ (nextPage : Nat) (tables : List Core.Table)
    (encodings : List TableEncoding), encodeTables nextPage tables = some encodings →
      encodings.map (fun encoding => encoding.table) = tables
  | _, [], encodings, encoded => by
      simp only [encodeTables, Option.some.injEq] at encoded
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, encoded => by
      simp only [encodeTables, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeTable nextPage table with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : encodeTables
            (nextPage + head.plan.pageCount) tables with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          have headTable : head.table = table := encodeTable_table headResult
          simp [headTable,
            encodeTables_tables (nextPage + head.plan.pageCount) tables tail
              tailResult]

structure IndexEncoding where
  table : Core.Table
  index : Core.Index
  rootPage : Nat
  plan : IndexPlan
  pages : List CoreFile.Page

def encodeIndex (rootPage : Nat) (table : Core.Table) (index : Core.Index) :
    Option IndexEncoding := do
  let leaves ← CoreFile.indexLeaves table index
  let plan ← buildIndex leaves
  let pages ← plan.encodePagesFrom rootPage
  some ⟨table, index, rootPage, plan, pages⟩

theorem encodeIndex_refines {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {encoding : IndexEncoding}
    (encoded : encodeIndex rootPage table index = some encoding) :
    ∃ cells leaves,
      CoreFile.indexCells table index = some cells ∧
      CoreFile.indexLeaves table index = some leaves ∧
      encoding.plan.toCells = cells := by
  unfold encodeIndex at encoded
  cases leavesResult : CoreFile.indexLeaves table index with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : buildIndex leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        unfold CoreFile.indexLeaves at leavesResult
        cases cellsResult : CoreFile.indexCells table index with
        | none => simp [cellsResult] at leavesResult
        | some cells =>
          simp only [cellsResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at leavesResult
          subst leaves
          refine ⟨cells, CellPagination.paginateCells cells, rfl, ?_, ?_⟩
          · simp [CoreFile.indexLeaves, cellsResult]
          · rw [buildIndex_toCells planResult]
            exact CellPagination.flatten_paginateCells cells

def encodeIndexes : Nat → List (Core.Table × Core.Index) →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, indexed :: indexes => do
      let encoded ← encodeIndex nextPage indexed.1 indexed.2
      let remaining ← encodeIndexes (nextPage + encoded.plan.pageCount) indexes
      some (encoded :: remaining)

def indexPagesOf (encodings : List IndexEncoding) : List CoreFile.Page :=
  encodings.flatMap (fun encoding => encoding.pages)

def IndexEncoding.catalogEntry (encoding : IndexEncoding) : CoreFile.CatalogEntry := {
  kind := "index"
  name := encoding.index.name
  table := encoding.table.schema.name
  rootPage := encoding.rootPage
  sql := CoreFile.indexSQL encoding.table encoding.index
  sqlIsNull := encoding.index.isImplicitPrimary encoding.table.schema }

def indexEntriesOf (encodings : List IndexEncoding) : List CoreFile.CatalogEntry :=
  encodings.map IndexEncoding.catalogEntry

theorem encodeIndex_pages_length {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {encoding : IndexEncoding}
    (encoded : encodeIndex rootPage table index = some encoding) :
    encoding.pages.length = encoding.plan.pageCount := by
  unfold encodeIndex at encoded
  cases leavesResult : CoreFile.indexLeaves table index with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : buildIndex leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        exact plan.encodePagesFrom_length pagesResult

/-- General Core image encoder with recursive table and index trees. -/
def encode (database : Core.Database) : Option CoreFile.Image := do
  let tableEncodings ← encodeTables 2 database.tables
  let tablePages := tablePagesOf tableEncodings
  let indexEncodings ← encodeIndexes (2 + tablePages.length)
    (CoreFile.indexedIndexes database)
  let entries := tableEntriesOf tableEncodings ++
    indexEntriesOf indexEncodings
  let remaining := tablePages ++ indexPagesOf indexEncodings
  let total := 1 + remaining.length
  if countBound : total < 2 ^ 32 then
    let count : FileFormat.U32Value := ⟨total, by simpa using countBound⟩
    let schema ← CoreFile.schemaPageForEntries? entries count
    some ⟨database, schema :: remaining⟩
  else none

theorem encode_tables_aligned {database : Core.Database} {image : CoreFile.Image}
    (encoded : encode database = some image) :
    ∃ tableEncodings,
      encodeTables 2 database.tables = some tableEncodings ∧
      tableEncodings.map (fun encoding => encoding.table) = database.tables := by
  unfold encode at encoded
  cases tableResult : encodeTables 2 database.tables with
  | none => simp [tableResult] at encoded
  | some tableEncodings =>
    refine ⟨tableEncodings, rfl,
      encodeTables_tables 2 database.tables tableEncodings tableResult⟩

end RecursivePageBTree
end SQLeanite
