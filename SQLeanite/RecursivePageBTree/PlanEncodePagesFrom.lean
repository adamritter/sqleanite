import SQLeanite.CoreFile.EncodeIndexTableGroupsCanonicalize
import SQLeanite.RecursivePageBTree.Plan

namespace SQLeanite
namespace RecursivePageBTree

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

end RecursivePageBTree

end SQLeanite
