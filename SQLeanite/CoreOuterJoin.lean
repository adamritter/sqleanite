import SQLeanite.CoreJoin.FilterMappedRightLeftOnly

/-! RIGHT/FULL joins keep match accounting independent of WHERE filtering.
Matched rows follow the left scan, then unmatched right rows are appended.
The existing query finishes projection, DISTINCT, sorting and row windows. -/
namespace SQLeanite.CoreOuterJoin

open CoreJoin

def unmatchedRights (on : Option Predicate) (left right : List Core.Row) : List Core.Row :=
  right.filter (fun row => !(left.any (fun candidate => selects on (candidate, row))))

theorem unmatchedRights_member (on : Option Predicate) (left right : List Core.Row)
    (row : Core.Row) : row ∈ unmatchedRights on left right ↔
      row ∈ right ∧ ∀ candidate ∈ left, selects on (candidate, row) = false := by
  simp [unmatchedRights, List.any_eq_false]

def joinedRows (full : Bool) (leftWidth rightWidth : Nat) (on : Option Predicate)
    (left right : List Core.Row) : List JoinedRow :=
  let initial :=  if full then leftOuterRows on rightWidth left right
    else matchingRows on none (crossRows left right)
  initial ++ (unmatchedRights on left right).map (fun row => (nullRow leftWidth, row))

theorem joinedRows_empty_left (full : Bool) (leftWidth rightWidth : Nat)
    (on : Option Predicate) (right : List Core.Row) :
    joinedRows full leftWidth rightWidth on [] right =
      right.map (fun row => (nullRow leftWidth, row)) := by
  have filtered : right.filter (fun _ => true) = right := by simp
  cases full <;> simp [joinedRows, leftOuterRows, crossRows, matchingRows, unmatchedRights, filtered]

theorem joinedRows_right_empty (leftWidth rightWidth : Nat)
    (on : Option Predicate) (left : List Core.Row) :
    joinedRows false leftWidth rightWidth on left [] = [] := by
  simp [joinedRows, unmatchedRights, matchingRows, crossRows]

theorem joinedRows_full_empty_right (leftWidth rightWidth : Nat)
    (on : Option Predicate) (left : List Core.Row) :
    joinedRows true leftWidth rightWidth on left [] =
      left.map (fun row => (row, nullRow rightWidth)) := by
  simp [joinedRows, unmatchedRights, leftOuterRows, leftOuterFor, ← List.map_eq_flatMap]

/-- RIGHT/FULL append unmatched rows after the matching scan. A left-rowid
scan cannot imply global ordering across that appended suffix. -/
def finishQuery (query : Query) : Query :=
  { query with lookupScanOrder := [], distinctScanOrder := [] }

def eval (full : Bool) (leftWidth : Nat) (query : Query)
    (left right : List Core.Row) : List (List Core.Value) :=
  let rows := (joinedRows full leftWidth query.rightWidth query.on left right).filter
    (selects query.where_)
  ((finishQuery query).finishRows rows).map (projectRow query.columns)

theorem eval_width (full : Bool) (leftWidth : Nat) (query : Query)
    (left right : List Core.Row) (row : List Core.Value)
    (member : row ∈ eval full leftWidth query left right) : row.length = query.columns.length := by
  simp only [eval, List.mem_map] at member
  obtain ⟨joined, _, rfl⟩ := member
  exact projectRow_length query.columns joined

theorem eval_limit_zero (full : Bool) (leftWidth : Nat) (query : Query)
    (left right : List Core.Row) (zero : query.limit = some 0) :
    eval full leftWidth query left right = [] := by
  simp [eval, Query.finishRows_limit_zero (finishQuery query) _ (by simpa [finishQuery] using zero)]

end SQLeanite.CoreOuterJoin
