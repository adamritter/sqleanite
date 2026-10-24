import SQLeanite.PhysicalStore
import SQLeanite.Value
import SQLeanite.Binary64

namespace SQLeanite.PhysicalQuery

open PhysicalCodec

inductive Column where
  | id
  | first
  | second
  deriving Repr, DecidableEq

def Column.value : Column → Row → PhysicalCodec.Value
  | .id, row => .integer row.rowid
  | .first, row => row.first
  | .second, row => row.second

def sqlEquals : PhysicalCodec.Value → PhysicalCodec.Value → Truth
  | .null, _ | _, .null => .unknown
  | .realBits left, .realBits right =>
      if Binary64.compareBits left right = .eq then .true else .false
  | .integer left, .realBits right =>
      if Binary64.compareInteger left.value right = .eq then .true else .false
  | .realBits left, .integer right =>
      if Binary64.compareInteger right.value left = .eq then .true else .false
  | left, right => if left = right then .true else .false

theorem sqlEquals_real_zero (left right : FileFormat.U64Value)
    (leftZero : Binary64.isZero left = true)
    (rightZero : Binary64.isZero right = true) :
    sqlEquals (.realBits left) (.realBits right) = .true := by
  simp [sqlEquals, Binary64.compareBits_zero_signs left right leftZero rightZero]

def valueClass : PhysicalCodec.Value → Nat
  | .null => 0
  | .integer _ | .realBits _ => 1
  | .text _ => 2
  | .blob _ => 3

def compareValue : PhysicalCodec.Value → PhysicalCodec.Value → Ordering
  | .null, .null => .eq
  | .integer left, .integer right => compare left.value right.value
  | .realBits left, .realBits right => Binary64.compareBits left right
  | .integer left, .realBits right => Binary64.compareInteger left.value right
  | .realBits left, .integer right =>
      Binary64.reverse (Binary64.compareInteger right.value left)
  | .text left, .text right => compare left.bytes right.bytes
  | .blob left, .blob right => compare left.bytes right.bytes
  | left, right => compare (valueClass left) (valueClass right)

/-- Lexicographic BINARY SQL order for tuples of physical values. -/
def compareValues : List PhysicalCodec.Value → List PhysicalCodec.Value → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      let order := compareValue a b
      if order == .eq then compareValues as bs else order

theorem compareValue_self (value : PhysicalCodec.Value) : compareValue value value = .eq := by
  cases value <;> simp [compareValue, Binary64.compareBits_self]

theorem compareValues_self (values : List PhysicalCodec.Value) : compareValues values values = .eq := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [compareValues, compareValue_self, ih]

/-- SQL equality implies equality in the B-tree comparison order. This is the
bridge used when a separator proof rules out a subtree containing the sought
value, including integer/REAL numeric equality and signed zero. -/
theorem compareValue_eq_of_sqlEquals_true {left right : PhysicalCodec.Value}
    (equal : sqlEquals left right = .true) : compareValue left right = .eq := by
  cases left <;> cases right <;>
    simp [sqlEquals, compareValue] at equal ⊢
  all_goals simp [equal, Binary64.reverse]

inductive Comparison where
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, DecidableEq

def Comparison.holds : Comparison → Ordering → Bool
  | .less, order => order == .lt
  | .lessEqual, order => order != .gt
  | .greater, order => order == .gt
  | .greaterEqual, order => order != .lt

def sqlCompare (operation : Comparison) :
    PhysicalCodec.Value → PhysicalCodec.Value → Truth
  | .null, _ | _, .null => .unknown
  | left, right =>
      if operation.holds (compareValue left right) then .true else .false

inductive Predicate where
  | equal (column : Column) (value : PhysicalCodec.Value)
  | notEqual (column : Column) (value : PhysicalCodec.Value)
  | compare (operation : Comparison) (column : Column) (value : PhysicalCodec.Value)
  | isNull (column : Column)
  | not (predicate : Predicate)
  | and (left right : Predicate)
  | or (left right : Predicate)

def Predicate.eval : Predicate → Row → Truth
  | .equal column value, row => sqlEquals (column.value row) value
  | .notEqual column value, row => Truth.not (sqlEquals (column.value row) value)
  | .compare operation column value, row =>
      sqlCompare operation (column.value row) value
  | .isNull column, row => if column.value row = .null then .true else .false
  | .not predicate, row => Truth.not (predicate.eval row)
  | .and left right, row => Truth.and (left.eval row) (right.eval row)
  | .or left right, row => Truth.or (left.eval row) (right.eval row)

def selects : Option Predicate → Row → Bool
  | none, _ => true
  | some predicate, row => predicate.eval row = .true

def matchingRows (predicate : Option Predicate) (rows : List Row) : List Row :=
  match predicate with
  | none => rows
  | some _ => rows.filter (selects predicate)

theorem mem_matchingRows_iff (predicate : Option Predicate) (rows : List Row)
    (row : Row) :
    row ∈ matchingRows predicate rows ↔
      row ∈ rows ∧ ∀ selected ∈ predicate, selected.eval row = .true := by
  cases predicate with
  | none => simp [matchingRows]
  | some predicate => simp [matchingRows, selects]

def projectRow (columns : List Column) (row : Row) : List PhysicalCodec.Value :=
  columns.map (fun column => column.value row)

theorem projectRow_length (columns : List Column) (row : Row) :
    (projectRow columns row).length = columns.length := by
  simp [projectRow]

structure Query where
  columns : List Column
  predicate : Option Predicate := none
  orderBy : List (Column × Bool) := []
  limit : Option Nat := none

def rowLess : List (Column × Bool) → Row → Row → Bool
  | [], _, _ => false
  | term :: terms, left, right =>
      let order := compareValue (term.1.value left) (term.1.value right)
      if order == .eq then rowLess terms left right
      else if term.2 then order == .gt else order == .lt

def insertOrdered (terms : List (Column × Bool)) (row : Row) : List Row → List Row
  | [] => [row]
  | candidate :: rows =>
      if rowLess terms row candidate then row :: candidate :: rows
      else candidate :: insertOrdered terms row rows

theorem insertOrdered_perm (terms : List (Column × Bool)) (row : Row) (rows : List Row) :
    (insertOrdered terms row rows).Perm (row :: rows) := by
  induction rows with
  | nil => exact List.Perm.refl _
  | cons candidate rows induction =>
      unfold insertOrdered
      split
      · exact List.Perm.refl _
      · exact (induction.cons candidate).trans (List.Perm.swap row candidate rows)

theorem foldInsertOrdered_perm (terms : List (Column × Bool)) (rows accumulator : List Row) :
    (rows.foldl (fun sorted row => insertOrdered terms row sorted) accumulator).Perm
      (rows ++ accumulator) := by
  induction rows generalizing accumulator with
  | nil => exact List.Perm.refl _
  | cons row rows induction =>
      have tail := induction (insertOrdered terms row accumulator)
      have inserted := (insertOrdered_perm terms row accumulator).append_left rows
      exact tail.trans (inserted.trans List.perm_middle)

/-- Stable merge sort by the same strict order, replacing an O(n^2) insertion
sort. `a ≤ b` is `¬ (b < a)`, so equal rows keep input order. -/
def rowLe (terms : List (Column × Bool)) (left right : Row) : Bool :=
  !rowLess terms right left

def Query.orderedRows (query : Query) (rows : List Row) : List Row :=
  if query.orderBy.isEmpty then rows
  else rows.mergeSort (rowLe query.orderBy)

theorem Query.orderedRows_perm (query : Query) (rows : List Row) :
    (query.orderedRows rows).Perm rows := by
  by_cases empty : query.orderBy.isEmpty
  · simp [Query.orderedRows, empty]
  · simpa [Query.orderedRows, empty] using List.mergeSort_perm rows (rowLe query.orderBy)

def Query.selectedRows (query : Query) (rows : List Row) : List Row :=
  let rows := matchingRows query.predicate rows
  let rows := query.orderedRows rows
  match query.limit with
  | none => rows
  | some limit => rows.take limit

def Query.eval (query : Query) (rows : List Row) : List (List PhysicalCodec.Value) :=
  (query.selectedRows rows).map (projectRow query.columns)

theorem matchingRows_id_equal (database : PhysicalCodec.Database)
    (rowid : FileFormat.SignedInteger .eight) :
    matchingRows (some (.equal .id (.integer rowid))) database.rows =
      database.lookupRowid rowid.value := by
  rw [database.lookupRowid_eq_filter]
  unfold matchingRows
  apply List.filter_congr
  intro row _
  by_cases equal : row.rowid.value = rowid.value
  · have signedEqual : row.rowid = rowid := FileFormat.SignedInteger.ext equal
    simp [selects, Predicate.eval, Column.value, sqlEquals, equal, signedEqual]
  · have signedDifferent : row.rowid ≠ rowid := fun signedEqual =>
      equal (congrArg FileFormat.SignedInteger.value signedEqual)
    simp [selects, Predicate.eval, Column.value, sqlEquals, equal, signedDifferent]

/-- Use the ordered primary-key path for the predicate shape it covers. -/
def Query.evalDatabase (query : Query) (database : PhysicalCodec.Database) :
    List (List PhysicalCodec.Value) :=
  match query.predicate with
  | some (.equal .id (.integer rowid)) =>
      ({ query with predicate := none }).eval (database.lookupRowid rowid.value)
  | _ => query.eval database.rows

theorem Query.evalDatabase_eq_eval (query : Query) (database : PhysicalCodec.Database) :
    query.evalDatabase database = query.eval database.rows := by
  unfold Query.evalDatabase
  split <;> try rfl
  next rowid matched =>
    rw [← matchingRows_id_equal]
    unfold Query.eval Query.selectedRows
    simp [matchingRows, Query.orderedRows, matched]

theorem Query.eval_width (query : Query) (rows : List Row) :
    ∀ values ∈ query.eval rows, values.length = query.columns.length := by
  intro values membership
  simp only [Query.eval, List.mem_map] at membership
  obtain ⟨row, _, rfl⟩ := membership
  exact projectRow_length query.columns row

theorem Query.selectedRows_length_le_limit (query : Query) (rows : List Row)
    (limit : Nat) (bounded : query.limit = some limit) :
    (query.selectedRows rows).length ≤ limit := by
  simp [Query.selectedRows, bounded]
  omega

end SQLeanite.PhysicalQuery
