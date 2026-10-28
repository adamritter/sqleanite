import SQLeanite.CoreFile.Page

namespace SQLeanite
namespace CoreFile
attribute [local instance] lexOrd
open FileFormat

def tableInteriorPage? (firstLeaf : Nat) (leaves : List (List (List UInt8))) :
    Option Page := do
  let rightmostNumber := firstLeaf + leaves.length - 1
  if rightmostBound : rightmostNumber < 2 ^ 32 then
    let rightmost : U32Value := ⟨rightmostNumber, by simpa using rightmostBound⟩
    let cells ← tableInteriorCells? firstLeaf leaves
    if fits : PhysicalTableBTree.InteriorPageFit cells then
      some {
        bytes := PhysicalTableBTree.interiorPageBody rightmost cells
        length_eq := PhysicalTableBTree.interiorPageBody_length rightmost cells fits }
    else none
  else none

/-- Pages for one table, in page-number order: root first, then leaves. -/
def tablePages? (layout : TableLayout) : Option (List Page) :=
  match layout.leaves with
  | [] => do let page ← tableLeafPage? []; some [page]
  | [only] => do let page ← tableLeafPage? only; some [page]
  | _ => do
      let root ← tableInteriorPage? (layout.rootPage + 1) layout.leaves
      let leafPages ← layout.leaves.mapM tableLeafPage?
      some (root :: leafPages)

private theorem optionMapM_length {α β : Type} (f : α → Option β) :
    ∀ (input : List α) (output : List β),
      input.mapM f = some output → output.length = input.length
  | [], output, success => by
      simp only [List.mapM_nil, pure, Pure.pure] at success
      injection success with equal
      subst output
      rfl
  | value :: input, output, success => by
      cases headResult : f value with
      | none => simp [List.mapM_cons, headResult] at success
      | some result =>
          cases tailResult : input.mapM f with
          | none => simp [List.mapM_cons, headResult, tailResult] at success
          | some remaining =>
              simp only [List.mapM_cons, headResult, tailResult,
                Option.bind_eq_bind, Option.bind] at success
              injection success with equal
              subst output
              simp [optionMapM_length f input remaining tailResult]

theorem tablePages_length_of_success {layout : TableLayout} {pages : List Page}
    (built : tablePages? layout = some pages) :
    pages.length = tableFootprint layout.leaves := by
  cases leavesShape : layout.leaves with
  | nil =>
      unfold tablePages? at built
      rw [leavesShape] at built
      cases pageResult : tableLeafPage? [] with
      | none => simp [pageResult] at built
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at built
          injection built with equal
          subst pages
          rfl
  | cons first rest =>
    cases restShape : rest with
    | nil =>
      unfold tablePages? at built
      rw [leavesShape, restShape] at built
      cases pageResult : tableLeafPage? first with
      | none => simp [pageResult] at built
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at built
          injection built with equal
          subst pages
          rfl
    | cons second remaining =>
      unfold tablePages? at built
      rw [leavesShape, restShape] at built
      cases rootResult : tableInteriorPage? (layout.rootPage + 1)
          (first :: second :: remaining) with
      | none => simp [rootResult] at built
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at built
        cases leafResult : (first :: second :: remaining).mapM tableLeafPage? with
        | none => simp [leafResult] at built
        | some leaves =>
          simp only [leafResult] at built
          injection built with equal
          subst pages
          have leafLength := optionMapM_length tableLeafPage?
            (first :: second :: remaining) leaves leafResult
          simp [tableFootprint, leavesShape, restShape, leafLength]

/-- Cells a table layout stores, read back off the layout in page order. -/
def TableLayout.storedCells (layout : TableLayout) : List (List UInt8) :=
  layout.leaves.flatten

/-- **Multi-page layout is contents-preserving.** Whatever the split, the cells
distributed across a table's leaves are exactly the cells the table encoded, in
the same order. Nothing is lost, duplicated or reordered by paging.

This is the part of `decode (encode db) = db` that the multi-page work is
responsible for. The remaining gap is the catalog's SQL text: `decode` recovers
a schema by running the real parser over the `CREATE TABLE` string that
`encode` printed, so closing the full round trip needs
`parseTableSchema (tableSQL s) = some s`, a parser-correctness result that is
tracked separately in `docs/TRUST.md`. -/
theorem tableLeaves_storedCells (table : Core.Table)
    {leaves : List (List (List UInt8))} {cells : List (List UInt8)}
    (encoded : tableCells table = some cells)
    (paged : tableLeaves table = some leaves) :
    (TableLayout.storedCells ⟨0, leaves⟩) = cells := by
  unfold tableLeaves at paged
  rw [encoded] at paged
  simp at paged
  subst paged
  exact CellPagination.flatten_paginateCells cells

/-- Every leaf a layout emits fits a page, so page construction cannot fail for
size reasons once each individual cell fits. -/
theorem tableLeaves_fit (table : Core.Table)
    {leaves : List (List (List UInt8))} {cells : List (List UInt8)}
    (encoded : tableCells table = some cells)
    (paged : tableLeaves table = some leaves)
    (singles : ∀ cell ∈ cells, PhysicalCodec.PageFit 0 [cell]) :
    ∀ page ∈ leaves, PhysicalCodec.PageFit 0 page := by
  unfold tableLeaves at paged
  rw [encoded] at paged
  simp at paged
  subst paged
  exact CellPagination.paginateCells_fits cells singles

def indexRecord? (index : Core.Index)
    (row : Core.Row) : Option PhysicalRecord :=
  physicalRecord? [
    (row.value index.column).recordField,
    (PhysicalCodec.Value.integer row.rowid).recordField]

def indexCell? (index : Core.Index)
    (row : Core.Row) : Option (List UInt8) := do
  let record ← indexRecord? index row
  if bound : record.encode.length < 2 ^ 64 then
    let payloadSize : U64Value := ⟨record.encode.length, by simpa using bound⟩
    some (encodeVarint payloadSize ++ record.encode)
  else none

def indexRowLess (index : Core.Index)
    (left right : Core.Row) : Bool :=
  match PhysicalQuery.compareValue (left.value index.column) (right.value index.column) with
  | .lt => true
  | .gt => false
  | .eq => left.rowid.value < right.rowid.value

def indexRowValueLe (index : Core.Index) (left right : Core.Row) : Prop :=
  PhysicalQuery.compareValue (left.value index.column)
    (right.value index.column) ≠ .gt

theorem indexRowLess_true_valueLe (index : Core.Index)
    (left right : Core.Row)
    (less : indexRowLess index left right = true) :
    indexRowValueLe index left right := by
  unfold indexRowLess at less
  unfold indexRowValueLe
  intro greater
  rw [greater] at less
  simp at less

theorem indexRowLess_false_reverse_valueLe (index : Core.Index)
    (left right : Core.Row)
    (leftInteger : ∃ value : Core.Integer,
      left.value index.column = .integer value)
    (rightInteger : ∃ value : Core.Integer,
      right.value index.column = .integer value)
    (notLess : indexRowLess index left right = false) :
    indexRowValueLe index right left := by
  rcases leftInteger with ⟨leftValue, leftEqual⟩
  rcases rightInteger with ⟨rightValue, rightEqual⟩
  unfold indexRowLess at notLess
  unfold indexRowValueLe
  simp only [leftEqual, rightEqual, PhysicalQuery.compareValue] at notLess ⊢
  have forwardLt : compare leftValue.value rightValue.value = .lt ↔
      leftValue.value < rightValue.value := by
    change compareOfLessAndEq leftValue.value rightValue.value = .lt ↔ _
    exact compareOfLessAndEq_eq_lt
  have reverseGt : compare rightValue.value leftValue.value = .gt ↔
      leftValue.value < rightValue.value := by
    change compareOfLessAndEq rightValue.value leftValue.value = .gt ↔ _
    exact compareOfLessAndEq_eq_gt Int.le_antisymm Int.le_total Int.not_le _ _
  intro greater
  have forward := forwardLt.mpr (reverseGt.mp greater)
  rw [forward] at notLess
  simp at notLess

theorem indexRowValueLe_trans_integer (index : Core.Index)
    (left middle right : Core.Row)
    (leftInteger : ∃ value : Core.Integer,
      left.value index.column = .integer value)
    (middleInteger : ∃ value : Core.Integer,
      middle.value index.column = .integer value)
    (rightInteger : ∃ value : Core.Integer,
      right.value index.column = .integer value)
    (leftMiddle : indexRowValueLe index left middle)
    (middleRight : indexRowValueLe index middle right) :
    indexRowValueLe index left right := by
  rcases leftInteger with ⟨leftValue, leftEqual⟩
  rcases middleInteger with ⟨middleValue, middleEqual⟩
  rcases rightInteger with ⟨rightValue, rightEqual⟩
  unfold indexRowValueLe at leftMiddle middleRight ⊢
  simp only [leftEqual, middleEqual, rightEqual,
    PhysicalQuery.compareValue] at leftMiddle middleRight ⊢
  have gtIff (left right : Int) : compare left right = .gt ↔ right < left := by
    change compareOfLessAndEq left right = .gt ↔ _
    exact compareOfLessAndEq_eq_gt Int.le_antisymm Int.le_total Int.not_le _ _
  have notMiddleLeft : ¬ middleValue.value < leftValue.value := by
    intro less
    exact leftMiddle ((gtIff _ _).mpr less)
  have notRightMiddle : ¬ rightValue.value < middleValue.value := by
    intro less
    exact middleRight ((gtIff _ _).mpr less)
  intro greater
  have rightLeft := (gtIff _ _).mp greater
  omega

theorem indexRowLess_false_reverse_valueLe_text (index : Core.Index)
    (left right : Core.Row)
    (leftText : ∃ value : PhysicalCodec.Text,
      left.value index.column = .text value)
    (rightText : ∃ value : PhysicalCodec.Text,
      right.value index.column = .text value)
    (notLess : indexRowLess index left right = false) :
    indexRowValueLe index right left := by
  rcases leftText with ⟨leftValue, leftEqual⟩
  rcases rightText with ⟨rightValue, rightEqual⟩
  unfold indexRowLess at notLess
  unfold indexRowValueLe
  simp only [leftEqual, rightEqual, PhysicalQuery.compareValue] at notLess ⊢
  intro greater
  have forward : compare leftValue.bytes rightValue.bytes = .lt :=
    Std.OrientedCmp.lt_of_gt greater
  rw [forward] at notLess
  contradiction

theorem indexRowValueLe_trans_text (index : Core.Index)
    (left middle right : Core.Row)
    (leftText : ∃ value : PhysicalCodec.Text,
      left.value index.column = .text value)
    (middleText : ∃ value : PhysicalCodec.Text,
      middle.value index.column = .text value)
    (rightText : ∃ value : PhysicalCodec.Text,
      right.value index.column = .text value)
    (leftMiddle : indexRowValueLe index left middle)
    (middleRight : indexRowValueLe index middle right) :
    indexRowValueLe index left right := by
  rcases leftText with ⟨leftValue, leftEqual⟩
  rcases middleText with ⟨middleValue, middleEqual⟩
  rcases rightText with ⟨rightValue, rightEqual⟩
  unfold indexRowValueLe at leftMiddle middleRight ⊢
  simp only [leftEqual, middleEqual, rightEqual,
    PhysicalQuery.compareValue] at leftMiddle middleRight ⊢
  have leftMiddleLE :
      (compare leftValue.bytes middleValue.bytes).isLE := by
    cases result : compare leftValue.bytes middleValue.bytes <;>
      simp_all
  have middleRightLE :
      (compare middleValue.bytes rightValue.bytes).isLE := by
    cases result : compare middleValue.bytes rightValue.bytes <;>
      simp_all
  have leftRightLE :=
    Std.TransOrd.isLE_trans leftMiddleLE middleRightLE
  intro greater
  rw [greater] at leftRightLE
  contradiction

def insertIndexRow (index : Core.Index) (row : Core.Row) :
    List Core.Row → List Core.Row
  | [] => [row]
  | candidate :: rows =>
      if indexRowLess index row candidate then row :: candidate :: rows
      else candidate :: insertIndexRow index row rows

theorem insertIndexRow_perm (index : Core.Index) (row : Core.Row)
    (rows : List Core.Row) :
    (insertIndexRow index row rows).Perm (row :: rows) := by
  induction rows with
  | nil => rfl
  | cons candidate rows induction =>
      unfold insertIndexRow
      split
      · exact List.Perm.refl _
      · exact (induction.cons candidate).trans
          (List.Perm.swap row candidate rows)

theorem insertIndexRow_pairwise (index : Core.Index) (row : Core.Row) :
    ∀ (rows : List Core.Row),
      (∃ value : Core.Integer, row.value index.column = .integer value) →
      (∀ candidate ∈ rows, ∃ value : Core.Integer,
        candidate.value index.column = .integer value) →
      rows.Pairwise (indexRowValueLe index) →
      (insertIndexRow index row rows).Pairwise (indexRowValueLe index)
  | [], _, _, _ => by simp [insertIndexRow]
  | candidate :: rows, rowInteger, allInteger, sorted => by
      have candidateInteger := allInteger candidate (by simp)
      have tailInteger : ∀ current ∈ rows, ∃ value : Core.Integer,
          current.value index.column = .integer value := by
        intro current member
        exact allInteger current (by simp [member])
      have candidateBefore : ∀ current ∈ rows,
          indexRowValueLe index candidate current :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted := (List.pairwise_cons.mp sorted).2
      unfold insertIndexRow
      split
      next less =>
        have rowBeforeCandidate := indexRowLess_true_valueLe index row candidate
          less
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          rcases List.mem_cons.mp member with rfl | member
          · exact rowBeforeCandidate
          · exact indexRowValueLe_trans_integer index row candidate current
              rowInteger candidateInteger (tailInteger current member)
              rowBeforeCandidate
              (candidateBefore current member)
        · exact sorted
      next notLess =>
        have notLessFalse : indexRowLess index row candidate = false :=
          (Bool.not_eq_true _).mp notLess
        have candidateBeforeRow := indexRowLess_false_reverse_valueLe index
          row candidate rowInteger candidateInteger notLessFalse
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          have sourceMember : current ∈ row :: rows :=
            (insertIndexRow_perm index row rows).subset member
          rcases List.mem_cons.mp sourceMember with rfl | sourceMember
          · exact candidateBeforeRow
          · exact candidateBefore current sourceMember
        · exact insertIndexRow_pairwise index row rows rowInteger tailInteger
            tailSorted

theorem insertIndexRow_pairwise_text (index : Core.Index) (row : Core.Row) :
    ∀ (rows : List Core.Row),
      (∃ value : PhysicalCodec.Text,
        row.value index.column = .text value) →
      (∀ candidate ∈ rows, ∃ value : PhysicalCodec.Text,
        candidate.value index.column = .text value) →
      rows.Pairwise (indexRowValueLe index) →
      (insertIndexRow index row rows).Pairwise (indexRowValueLe index)
  | [], _, _, _ => by simp [insertIndexRow]
  | candidate :: rows, rowText, allText, sorted => by
      have candidateText := allText candidate (by simp)
      have tailText : ∀ current ∈ rows, ∃ value : PhysicalCodec.Text,
          current.value index.column = .text value := by
        intro current member
        exact allText current (by simp [member])
      have candidateBefore : ∀ current ∈ rows,
          indexRowValueLe index candidate current :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted := (List.pairwise_cons.mp sorted).2
      unfold insertIndexRow
      split
      next less =>
        have rowBeforeCandidate := indexRowLess_true_valueLe index row candidate
          less
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          rcases List.mem_cons.mp member with rfl | member
          · exact rowBeforeCandidate
          · exact indexRowValueLe_trans_text index row candidate current
              rowText candidateText (tailText current member)
              rowBeforeCandidate (candidateBefore current member)
        · exact sorted
      next notLess =>
        have notLessFalse : indexRowLess index row candidate = false :=
          (Bool.not_eq_true _).mp notLess
        have candidateBeforeRow := indexRowLess_false_reverse_valueLe_text index
          row candidate rowText candidateText notLessFalse
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          have sourceMember : current ∈ row :: rows :=
            (insertIndexRow_perm index row rows).subset member
          rcases List.mem_cons.mp sourceMember with rfl | sourceMember
          · exact candidateBeforeRow
          · exact candidateBefore current sourceMember
        · exact insertIndexRow_pairwise_text index row rows rowText tailText
            tailSorted

theorem foldInsertIndexRow_pairwise (index : Core.Index) :
    ∀ (rows accumulator : List Core.Row),
      (∀ row ∈ rows, ∃ value : Core.Integer,
        row.value index.column = .integer value) →
      (∀ row ∈ accumulator, ∃ value : Core.Integer,
        row.value index.column = .integer value) →
      accumulator.Pairwise (indexRowValueLe index) →
      (rows.foldl (fun sorted row => insertIndexRow index row sorted)
        accumulator).Pairwise (indexRowValueLe index)
  | [], _, _, _, sorted => by simpa
  | row :: rows, accumulator, allRows, allAccumulator, sorted => by
      have rowInteger := allRows row (by simp)
      have tailInteger : ∀ current ∈ rows, ∃ value : Core.Integer,
          current.value index.column = .integer value := by
        intro current member
        exact allRows current (by simp [member])
      have insertedInteger : ∀ current ∈ insertIndexRow index row accumulator,
          ∃ value : Core.Integer,
            current.value index.column = .integer value := by
        intro current member
        have sourceMember : current ∈ row :: accumulator :=
          (insertIndexRow_perm index row accumulator).subset member
        rcases List.mem_cons.mp sourceMember with rfl | sourceMember
        · exact rowInteger
        · exact allAccumulator current sourceMember
      exact foldInsertIndexRow_pairwise index rows
        (insertIndexRow index row accumulator) tailInteger insertedInteger
        (insertIndexRow_pairwise index row accumulator rowInteger
          allAccumulator sorted)

theorem foldInsertIndexRow_pairwise_text (index : Core.Index) :
    ∀ (rows accumulator : List Core.Row),
      (∀ row ∈ rows, ∃ value : PhysicalCodec.Text,
        row.value index.column = .text value) →
      (∀ row ∈ accumulator, ∃ value : PhysicalCodec.Text,
        row.value index.column = .text value) →
      accumulator.Pairwise (indexRowValueLe index) →
      (rows.foldl (fun sorted row => insertIndexRow index row sorted)
        accumulator).Pairwise (indexRowValueLe index)
  | [], _, _, _, sorted => by simpa
  | row :: rows, accumulator, allRows, allAccumulator, sorted => by
      have rowText := allRows row (by simp)
      have tailText : ∀ current ∈ rows, ∃ value : PhysicalCodec.Text,
          current.value index.column = .text value := by
        intro current member
        exact allRows current (by simp [member])
      have insertedText : ∀ current ∈ insertIndexRow index row accumulator,
          ∃ value : PhysicalCodec.Text,
            current.value index.column = .text value := by
        intro current member
        have sourceMember : current ∈ row :: accumulator :=
          (insertIndexRow_perm index row accumulator).subset member
        rcases List.mem_cons.mp sourceMember with rfl | sourceMember
        · exact rowText
        · exact allAccumulator current sourceMember
      exact foldInsertIndexRow_pairwise_text index rows
        (insertIndexRow index row accumulator) tailText insertedText
        (insertIndexRow_pairwise_text index row accumulator rowText
          allAccumulator sorted)

/-- The executable INTEGER key used by the verified merge-sort fast path.
Non-INTEGER values receive a harmless default; the fast path is selected only
after `indexValuesInteger` has certified every source row.  Keeping the key
total makes the comparator's order laws unconditional and therefore suitable
for `List.mergeSort`. -/
def integerIndexKey (index : Core.Index) (row : Core.Row) : Int :=
  match row.value index.column with
  | .integer value => value.value
  | _ => 0

/-- Lexicographic non-strict order on `(indexed INTEGER value, rowid)`.
The rowid component makes the physical index order deterministic when indexed
values are equal. -/
def integerIndexRowLe (index : Core.Index)
    (left right : Core.Row) : Bool :=
  decide (integerIndexKey index left < integerIndexKey index right ∨
    (integerIndexKey index left = integerIndexKey index right ∧
      left.rowid.value ≤ right.rowid.value))

end CoreFile

end SQLeanite
