import SQLeanite.CoreDistinct
import SQLeanite.CoreJoin.Side

namespace SQLeanite
namespace CoreJoin

private theorem filterMappedRight_leftOnly (on : Option Predicate)
    {where_ : Predicate} (only : where_.leftOnly = true)
    (left : Core.Row) (right : List Core.Row) :
    ((right.map fun row => (left, row)).filter fun joined =>
        selects on joined && selects (some where_) joined) =
      if selectsLeft where_ left then
        (right.map fun row => (left, row)).filter (selects on)
      else [] := by
  induction right with
  | nil => simp
  | cons row rows induction =>
      simp only [List.map_cons, List.filter_cons]
      rw [selects_leftOnly only left row]
      by_cases passes : selectsLeft where_ left = true <;>
        simp [List.filter_cons, passes, induction]

private theorem matchingMappedRight_leftOnly (on : Option Predicate)
    {where_ : Predicate} (only : where_.leftOnly = true)
    (left : Core.Row) (right : List Core.Row) :
    matchingRows on (some where_) (right.map fun row => (left, row)) =
      if selectsLeft where_ left then
        matchingRows on none (right.map fun row => (left, row))
      else [] := by
  unfold matchingRows
  have withoutWhere : (fun row : JoinedRow => selects on row && selects none row) =
      selects on := by
    funext row
    simp [selects]
  rw [withoutWhere]
  exact filterMappedRight_leftOnly on only left right

theorem matchingRows_pushLeft (on : Option Predicate)
    {where_ : Predicate} (only : where_.leftOnly = true)
    (left right : List Core.Row) :
    matchingRows on (some where_) (crossRows left right) =
      matchingRows on none
        (crossRows (left.filter (selectsLeft where_)) right) := by
  induction left with
  | nil => rfl
  | cons row rows induction =>
      rw [show crossRows (row :: rows) right =
        (right.map fun rightRow => (row, rightRow)) ++
          crossRows rows right by rfl]
      rw [show matchingRows on (some where_)
          ((right.map fun rightRow => (row, rightRow)) ++
            crossRows rows right) =
        matchingRows on (some where_)
            (right.map fun rightRow => (row, rightRow)) ++
          matchingRows on (some where_) (crossRows rows right) by
            simp [matchingRows]]
      rw [matchingMappedRight_leftOnly on only row right]
      rw [induction]
      by_cases passes : selectsLeft where_ row = true <;>
        simp [List.filter_cons, passes, crossRows, matchingRows]

def leftOuterFor (on : Option Predicate) (rightWidth : Nat)
    (left : Core.Row) (right : List Core.Row) : List JoinedRow :=
  let candidates := (right.map fun row => (left, row)).filter (selects on)
  if candidates.isEmpty then [(left, nullRow rightWidth)] else candidates

def leftOuterRows (on : Option Predicate) (rightWidth : Nat)
    (left right : List Core.Row) : List JoinedRow :=
  left.flatMap fun row => leftOuterFor on rightWidth row right

theorem leftOuterFor_unconstrained_empty (rightWidth : Nat) (left : Core.Row) :
    leftOuterFor none rightWidth left [] = [(left, nullRow rightWidth)] := rfl

theorem leftOuterFor_nonempty (on : Option Predicate) (rightWidth : Nat)
    (left : Core.Row) (right : List Core.Row) :
    (leftOuterFor on rightWidth left right).isEmpty = false := by
  unfold leftOuterFor
  generalize (List.map (fun row => (left, row)) right).filter (selects on) = candidates
  cases empty : candidates.isEmpty <;> simp [empty]

theorem leftOuterFor_eq_null_of_no_match (on : Option Predicate)
    (rightWidth : Nat) (left : Core.Row) (right : List Core.Row)
    (noneMatch : ((right.map fun row => (left, row)).filter (selects on)).isEmpty = true) :
    leftOuterFor on rightWidth left right = [(left, nullRow rightWidth)] := by
  simp [leftOuterFor, noneMatch]

theorem leftOuterFor_eq_matches_of_some_match (on : Option Predicate)
    (rightWidth : Nat) (left : Core.Row) (right : List Core.Row)
    (someMatch : ((right.map fun row => (left, row)).filter (selects on)).isEmpty = false) :
    leftOuterFor on rightWidth left right =
      (right.map fun row => (left, row)).filter (selects on) := by
  simp [leftOuterFor, someMatch]

theorem leftOuterFor_preserves_left (on : Option Predicate) (rightWidth : Nat)
    (left : Core.Row) (right : List Core.Row) (joined : JoinedRow)
    (member : joined ∈ leftOuterFor on rightWidth left right) :
    joined.1 = left := by
  simp only [leftOuterFor] at member
  split at member
  · simp only [List.mem_singleton] at member
    subst joined
    rfl
  · simp only [List.mem_filter, List.mem_map] at member
    rcases member.1 with ⟨rightRow, _, equal⟩
    rw [← equal]

private theorem filterLeftOuterFor_leftOnly (on : Option Predicate)
    (rightWidth : Nat) {where_ : Predicate}
    (only : where_.leftOnly = true) (left : Core.Row)
    (right : List Core.Row) :
    (leftOuterFor on rightWidth left right).filter (selects (some where_)) =
      if selectsLeft where_ left then leftOuterFor on rightWidth left right
      else [] := by
  by_cases passes : selectsLeft where_ left = true
  · rw [if_pos passes]
    apply List.filter_eq_self.2
    intro joined member
    rw [selects_leftOnly only joined.1 joined.2]
    rw [leftOuterFor_preserves_left on rightWidth left right joined member]
    exact passes
  · rw [if_neg passes]
    apply List.filter_eq_nil_iff.2
    intro joined member
    simp only [Bool.not_eq_true]
    rw [selects_leftOnly only joined.1 joined.2]
    rw [leftOuterFor_preserves_left on rightWidth left right joined member]
    cases result : selectsLeft where_ left <;> simp_all

theorem leftOuterRows_pushLeft (on : Option Predicate) (rightWidth : Nat)
    {where_ : Predicate} (only : where_.leftOnly = true)
    (left right : List Core.Row) :
    (leftOuterRows on rightWidth left right).filter (selects (some where_)) =
      leftOuterRows on rightWidth (left.filter (selectsLeft where_)) right := by
  induction left with
  | nil => rfl
  | cons row rows induction =>
      rw [show leftOuterRows on rightWidth (row :: rows) right =
        leftOuterFor on rightWidth row right ++
          leftOuterRows on rightWidth rows right by rfl]
      rw [List.filter_append]
      rw [filterLeftOuterFor_leftOnly on rightWidth only row right]
      rw [induction]
      by_cases passes : selectsLeft where_ row = true <;>
        simp [List.filter_cons, passes, leftOuterRows]

def rowidOn (leftPrimaryKey rightPrimaryKey : Nat) : Predicate :=
  .equal (.column ⟨.left, leftPrimaryKey⟩)
    (.column ⟨.right, rightPrimaryKey⟩)

private theorem selects_rowidOn (leftSchema rightSchema : Core.Schema)
    (left right : Core.Row)
    (leftWellFormed : left.WellFormed leftSchema)
    (rightWellFormed : right.WellFormed rightSchema) :
    selects (some (rowidOn leftSchema.primaryKey rightSchema.primaryKey))
      (left, right) = decide (left.rowid = right.rowid) := by
  have leftValue : left.values[leftSchema.primaryKey]?.getD .null =
      .integer left.rowid := by
    rw [leftWellFormed.2.1]
    rfl
  have rightValue : right.values[rightSchema.primaryKey]?.getD .null =
      .integer right.rowid := by
    rw [rightWellFormed.2.1]
    rfl
  simp [selects, rowidOn, Predicate.eval, Operand.value, ColumnRef.value,
    leftValue, rightValue, PhysicalQuery.sqlEquals]

private theorem rowidMatches_eq_filter (leftSchema rightSchema : Core.Schema)
    (left : Core.Row) (right : List Core.Row)
    (leftWellFormed : left.WellFormed leftSchema)
    (rightWellFormed : ∀ row ∈ right, row.WellFormed rightSchema) :
    rowidMatches left right =
      (right.map fun row => (left, row)).filter
        (selects (some (rowidOn leftSchema.primaryKey rightSchema.primaryKey))) := by
  induction right with
  | nil => rfl
  | cons row rows induction =>
      have rowWellFormed := rightWellFormed row (by simp)
      have rowsWellFormed : ∀ candidate ∈ rows,
          candidate.WellFormed rightSchema := by
        intro candidate member
        exact rightWellFormed candidate (by simp [member])
      simp only [rowidMatches, List.filterMap_cons, List.map_cons,
        List.filter_cons]
      rw [selects_rowidOn leftSchema rightSchema left row leftWellFormed
        rowWellFormed]
      by_cases equal : left.rowid = row.rowid
      · rw [if_pos equal]
        have decision : decide (left.rowid = row.rowid) = true :=
          decide_eq_true equal
        rw [decision]
        simp only [Bool.true_eq, if_true, List.cons.injEq, true_and]
        exact induction rowsWellFormed
      · rw [if_neg equal]
        have decision : decide (left.rowid = row.rowid) = false :=
          decide_eq_false equal
        rw [decision]
        simp only [Bool.false_eq, if_false]
        exact induction rowsWellFormed

theorem rowidJoinSpec_eq_matchingRows (leftSchema rightSchema : Core.Schema)
    (left right : List Core.Row)
    (leftWellFormed : ∀ row ∈ left, row.WellFormed leftSchema)
    (rightWellFormed : ∀ row ∈ right, row.WellFormed rightSchema) :
    rowidJoinSpec left right =
      matchingRows
        (some (rowidOn leftSchema.primaryKey rightSchema.primaryKey)) none
        (crossRows left right) := by
  induction left with
  | nil => simp [rowidJoinSpec, matchingRows, crossRows]
  | cons row rows induction =>
      have rowWellFormed := leftWellFormed row (by simp)
      have rowsWellFormed : ∀ candidate ∈ rows,
          candidate.WellFormed leftSchema := by
        intro candidate member
        exact leftWellFormed candidate (by simp [member])
      simp only [rowidJoinSpec, crossRows, List.flatMap_cons, matchingRows,
        List.filter_append]
      rw [rowidMatches_eq_filter leftSchema rightSchema row right rowWellFormed
        rightWellFormed]
      have tail := induction rowsWellFormed
      unfold rowidJoinSpec matchingRows crossRows at tail
      rw [tail]
      congr 1
      apply List.filter_congr
      intro pair member
      simp [selects]

def projectRow (columns : List Operand) (row : JoinedRow) :
    List Core.Value :=
  columns.map fun column => column.value row

theorem projectRow_length (columns : List Operand) (row : JoinedRow) :
    (projectRow columns row).length = columns.length := by
  simp [projectRow]

/-- Existing column projections keep exactly their original values when
embedded in the operand projection used by literal and column atoms. -/
theorem projectRow_columns (columns : List ColumnRef) (row : JoinedRow) :
    projectRow (columns.map Operand.column) row = columns.map (fun column => column.value row) := by
  simp [projectRow, Operand.value, List.map_map]

def rowLess : List (ColumnRef × Bool) → JoinedRow → JoinedRow → Bool
  | [], _, _ => false
  | term :: terms, left, right =>
      let order := PhysicalQuery.compareValue (term.1.value left) (term.1.value right)
      if order == .eq then rowLess terms left right
      else if term.2 then order == .gt else order == .lt

def insertOrdered (terms : List (ColumnRef × Bool)) (row : JoinedRow) :
    List JoinedRow → List JoinedRow
  | [] => [row]
  | candidate :: rows =>
      if rowLess terms row candidate then row :: candidate :: rows
      else candidate :: insertOrdered terms row rows

theorem insertOrdered_perm (terms : List (ColumnRef × Bool)) (row : JoinedRow)
    (rows : List JoinedRow) :
    (insertOrdered terms row rows).Perm (row :: rows) := by
  induction rows with
  | nil => exact List.Perm.refl _
  | cons candidate rows induction =>
      unfold insertOrdered
      split
      · exact List.Perm.refl _
      · exact (induction.cons candidate).trans (List.Perm.swap row candidate rows)

theorem foldInsertOrdered_perm (terms : List (ColumnRef × Bool))
    (rows accumulator : List JoinedRow) :
    (rows.foldl (fun sorted row => insertOrdered terms row sorted) accumulator).Perm
      (rows ++ accumulator) := by
  induction rows generalizing accumulator with
  | nil => exact List.Perm.refl _
  | cons row rows induction =>
      have tail := induction (insertOrdered terms row accumulator)
      have inserted := (insertOrdered_perm terms row accumulator).append_left rows
      exact tail.trans (inserted.trans List.perm_middle)

/-- Compare projected SQL numeric keys while retaining the first original
joined row. Its unprojected values remain available to ORDER BY. -/
def distinctRows (columns : List Operand) (rows : List JoinedRow) : List JoinedRow :=
  Core.stableDistinctBy (fun row => Core.distinctRowKey (projectRow columns row)) rows

theorem distinctRows_keys (columns : List Operand) (rows : List JoinedRow)
    (key : List Core.Value) :
    key ∈ (distinctRows columns rows).map (fun row => Core.distinctRowKey (projectRow columns row)) ↔
      key ∈ rows.map (fun row => Core.distinctRowKey (projectRow columns row)) :=
  Core.mem_keys_stableDistinctBy _ _ _

theorem distinctRows_key_nodup (columns : List Operand) (rows : List JoinedRow) :
    ((distinctRows columns rows).map (fun row => Core.distinctRowKey (projectRow columns row))).Nodup :=
  Core.stableDistinctBy_key_nodup _ _

/-- Compare projected values using each result slot's explicit collation.
Unspecified trailing slots retain the schema's BINARY comparison. -/
def projectionEqual : List Operand → List SQLite.Collation.Kind → JoinedRow → JoinedRow → Bool
  | [], _, _, _ => true
  | column :: columns, kinds, left, right =>
      SQLite.Collation.compareValue (kinds.headD .binary)
        (column.value left) (column.value right) == .eq &&
          projectionEqual columns kinds.tail left right

/-- Keep original joined rows so nonselected ORDER BY columns remain available.
Only comparison metadata affects duplicate elimination. -/
def distinctCollatedRows (columns : List Operand) (kinds : List SQLite.Collation.Kind) :
    List JoinedRow → List JoinedRow
  | [] => []
  | row :: rows => row :: (distinctCollatedRows columns kinds rows).filter
      (fun other => !projectionEqual columns kinds row other)

theorem distinctCollatedRows_subset (columns : List Operand) (kinds : List SQLite.Collation.Kind)
    (rows : List JoinedRow) : distinctCollatedRows columns kinds rows ⊆ rows := by
  induction rows with
  | nil => simp [distinctCollatedRows]
  | cons first rest ih =>
      intro row member
      simp only [distinctCollatedRows, List.mem_cons, List.mem_filter] at member
      rcases member with rfl | ⟨kept, _⟩
      · simp
      · exact List.mem_cons_of_mem first (ih kept)

theorem distinctCollatedRows_pairwise (columns : List Operand) (kinds : List SQLite.Collation.Kind)
    (rows : List JoinedRow) :
    (distinctCollatedRows columns kinds rows).Pairwise
      (fun left right => projectionEqual columns kinds left right = false) := by
  induction rows with
  | nil => simp [distinctCollatedRows]
  | cons first rest ih =>
      simp only [distinctCollatedRows, List.pairwise_cons]
      constructor
      · intro row member
        simpa using (List.mem_filter.mp member).2
      · exact ih.filter _

structure OrderTerm where
  reference : ColumnRef
  descending : Bool := false
  nullsFirst : Option Bool := none
  collation : SQLite.Collation.Kind := .binary
  valueOperand : Option Operand := none

def OrderTerm.value (term : OrderTerm) (row : JoinedRow) : Core.Value :=
  (term.valueOperand.getD (.column term.reference)).value row

def OrderTerm.compareValues (term : OrderTerm) (left right : Core.Value) : Ordering :=
  match left, right with
  | .null, .null => .eq
  | .null, _ => if term.nullsFirst.getD (!term.descending) then .lt else .gt
  | _, .null => if term.nullsFirst.getD (!term.descending) then .gt else .lt
  | _, _ =>
      if term.descending then SQLite.Collation.compareValue term.collation right left
      else SQLite.Collation.compareValue term.collation left right

theorem OrderTerm.compareValues_null_left (term : OrderTerm) (right : Core.Value)
    (present : right ≠ .null) : term.compareValues .null right =
      if term.nullsFirst.getD (!term.descending) then .lt else .gt := by
  cases right <;> simp_all [OrderTerm.compareValues]

theorem OrderTerm.compareValues_null_right (term : OrderTerm) (left : Core.Value)
    (present : left ≠ .null) : term.compareValues left .null =
      if term.nullsFirst.getD (!term.descending) then .gt else .lt := by
  cases left <;> simp_all [OrderTerm.compareValues]

def orderedRowLess : List OrderTerm → JoinedRow → JoinedRow → Bool
  | [], _, _ => false
  | term :: terms, left, right =>
      let order := term.compareValues (term.value left) (term.value right)
      if order == .eq then orderedRowLess terms left right else order == .lt

def orderedRowLe (terms : List OrderTerm) (left right : JoinedRow) : Bool :=
  !orderedRowLess terms right left

structure Query where
  columns : List Operand
  on : Option Predicate
  kind : JoinKind := .inner
  rightWidth : Nat := 0
  where_ : Option Predicate := none
  orderBy : List OrderTerm := []
  limit : Option Nat := none
  offset : Nat := 0
  distinct : Bool := false
  distinctScanOrder : List (ColumnRef × Bool) := []
  lookupScanOrder : List (ColumnRef × Bool) := []
  distinctCollations : List SQLite.Collation.Kind := []

/-- Stable merge sort by the same strict order, replacing an O(n^2) insertion
sort. `a ≤ b` is `¬ (b < a)`, so equal rows keep input order. -/
def rowLe (terms : List (ColumnRef × Bool)) (left right : JoinedRow) : Bool :=
  !rowLess terms right left

def Query.orderedRows (query : Query) (rows : List JoinedRow) : List JoinedRow :=
  if query.orderBy.isEmpty then rows
  else rows.mergeSort (orderedRowLe query.orderBy)

theorem Query.orderedRows_perm (query : Query) (rows : List JoinedRow) :
    (query.orderedRows rows).Perm rows := by
  by_cases empty : query.orderBy.isEmpty
  · simp [Query.orderedRows, empty]
  · simpa [Query.orderedRows, empty] using List.mergeSort_perm rows (orderedRowLe query.orderBy)

/-- DISTINCT chooses its original representative in physical scan order.
The SQL translator supplies a rowid traversal order when ORDER BY is satisfied
by ordered table scans. A point-lookup plan already fixes its traversal;
the final output sorter remains independent. -/
def Query.distinctInputRows (query : Query) (rows : List JoinedRow) : List JoinedRow :=
  if !query.lookupScanOrder.isEmpty || query.distinctScanOrder.isEmpty then rows
  else rows.mergeSort (rowLe query.distinctScanOrder)

theorem Query.distinctInputRows_perm (query : Query) (rows : List JoinedRow) :
    (query.distinctInputRows rows).Perm rows := by
  by_cases empty : (!query.lookupScanOrder.isEmpty || query.distinctScanOrder.isEmpty) = true
  · simp [Query.distinctInputRows, empty]
  · simpa [Query.distinctInputRows, empty] using
      List.mergeSort_perm rows (rowLe query.distinctScanOrder)

/-- The SQL translator can recognize a right scan probing the left rowid.
This order applies before DISTINCT, stable output sorting and row windows. -/
def Query.lookupInputRows (query : Query) (rows : List JoinedRow) : List JoinedRow :=
  if query.lookupScanOrder.isEmpty then rows
  else rows.mergeSort (rowLe query.lookupScanOrder)

theorem Query.lookupInputRows_perm (query : Query) (rows : List JoinedRow) :
    (query.lookupInputRows rows).Perm rows := by
  by_cases empty : query.lookupScanOrder.isEmpty
  · simp [Query.lookupInputRows, empty]
  · simpa [Query.lookupInputRows, empty] using
      List.mergeSort_perm rows (rowLe query.lookupScanOrder)

def Query.distinctOutputRows (query : Query) (rows : List JoinedRow) : List JoinedRow :=
  if query.distinctCollations.isEmpty then distinctRows query.columns rows
  else distinctCollatedRows query.columns query.distinctCollations rows

def Query.finishRows (query : Query) (rows : List JoinedRow) : List JoinedRow :=
  let rows := query.lookupInputRows rows
  let rows := if query.distinct then query.distinctInputRows rows else rows
  let rows := if query.distinct then query.distinctOutputRows rows else rows
  let rows := (query.orderedRows rows).drop query.offset
  match query.limit with
  | none => rows
  | some limit => rows.take limit

theorem Query.finishRows_limit_zero (query : Query) (rows : List JoinedRow)
    (zero : query.limit = some 0) : query.finishRows rows = [] := by
  simp [Query.finishRows, zero]

def Query.selectedRows (query : Query) (left right : List Core.Row) :
    List JoinedRow :=
  let selected := match query.kind with
    | .inner => matchingRows query.on query.where_ (crossRows left right)
    | .left =>
        (leftOuterRows query.on query.rightWidth left right).filter
          (selects query.where_)
  query.finishRows selected

def Query.eval (query : Query) (left right : List Core.Row) :
    List (List Core.Value) :=
  (query.selectedRows left right).map (projectRow query.columns)

theorem Query.eval_limit_zero (query : Query) (left right : List Core.Row)
    (zero : query.limit = some 0) : query.eval left right = [] := by
  simp [Query.eval, Query.selectedRows, Query.finishRows, zero]

theorem Query.finishRows_nil (query : Query) : query.finishRows [] = [] := by
  simp [Query.finishRows, Query.lookupInputRows, Query.distinctInputRows,
    Query.orderedRows, Query.distinctOutputRows, distinctRows, distinctCollatedRows, Core.stableDistinctBy]
  split <;> rfl

end CoreJoin

end SQLeanite
