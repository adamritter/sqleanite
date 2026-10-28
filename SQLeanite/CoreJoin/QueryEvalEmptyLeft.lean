import SQLeanite.Core.Table
import SQLeanite.CoreJoin.FilterMappedRightLeftOnly

namespace SQLeanite
namespace CoreJoin

theorem Query.eval_empty_left (query : Query) (right : List Core.Row) :
    query.eval [] right = [] := by
  cases kind : query.kind <;>
    simp [Query.eval, Query.selectedRows, kind, crossRows, matchingRows,
      leftOuterRows, Query.finishRows_nil]

theorem Query.eval_empty_right_on (query : Query) (left : List Core.Row)
    (on : Option Predicate) (outer : query.kind = .left) :
    { query with on }.eval left [] = query.eval left [] := by
  simp [Query.eval, Query.selectedRows, outer, leftOuterRows, leftOuterFor,
    Query.finishRows, Query.lookupInputRows, Query.distinctInputRows, Query.orderedRows, Query.distinctOutputRows]

/-- Execute the certified primary-key join after a page reader has discarded
left rows above the greatest possible right key. -/
def Query.evalPrimaryKeyCandidates (query : Query)
    (leftCandidates right : List Core.Row) : List (List Core.Value) :=
  (query.finishRows (mergeRowids leftCandidates right)).map
    (projectRow query.columns)

def Query.evalPrimaryKeyBounded (query : Query) (left right : List Core.Row)
    (bound : Core.Integer) : List (List Core.Value) :=
  query.evalPrimaryKeyCandidates (left.filter (rowidAtMost bound)) right

/-- The bounded page-directed join is extensionally the ordinary SQL inner
join for the primary-key equality shape.  ORDER BY, LIMIT and projection stay
inside `finishRows`/`projectRow`, so this is an equality of complete query
results rather than only of intermediate pairs. -/
theorem Query.evalPrimaryKeyBounded_eq_eval (query : Query)
    (leftSchema rightSchema : Core.Schema) (left right : List Core.Row)
    (bound : Core.Integer)
    (onShape : query.on = some
      (rowidOn leftSchema.primaryKey rightSchema.primaryKey))
    (whereShape : query.where_ = none) (kindShape : query.kind = .inner)
    (leftWellFormed : Core.RowsWellFormed leftSchema left)
    (rightWellFormed : Core.RowsWellFormed rightSchema right)
    (rightBounded : ∀ row ∈ right, row.rowid.value ≤ bound.value) :
    query.evalPrimaryKeyBounded left right bound = query.eval left right := by
  unfold Query.evalPrimaryKeyBounded Query.evalPrimaryKeyCandidates Query.eval
  rw [mergeRowids_filter_left_atMost_eq_spec left right bound
    leftWellFormed.2 rightWellFormed.2 rightBounded]
  rw [rowidJoinSpec_eq_matchingRows leftSchema rightSchema left right
    leftWellFormed.1 rightWellFormed.1]
  simp [Query.selectedRows, onShape, whereShape, kindShape]

/-- Candidate form used by the IO boundary: the byte-level range theorem
supplies `candidatesEq`, while this theorem discharges all remaining SQL join
semantics. -/
theorem Query.evalPrimaryKeyCandidates_eq_eval (query : Query)
    (leftSchema rightSchema : Core.Schema) (left right candidates : List Core.Row)
    (bound : Core.Integer)
    (candidatesEq : candidates = left.filter (rowidAtMost bound))
    (onShape : query.on = some
      (rowidOn leftSchema.primaryKey rightSchema.primaryKey))
    (whereShape : query.where_ = none) (kindShape : query.kind = .inner)
    (leftWellFormed : Core.RowsWellFormed leftSchema left)
    (rightWellFormed : Core.RowsWellFormed rightSchema right)
    (rightBounded : ∀ row ∈ right, row.rowid.value ≤ bound.value) :
    query.evalPrimaryKeyCandidates candidates right = query.eval left right := by
  subst candidates
  exact query.evalPrimaryKeyBounded_eq_eval leftSchema rightSchema left right
    bound onShape whereShape kindShape leftWellFormed rightWellFormed rightBounded

/-- Empty right input is the other branch of the cold join reader; it is a
complete inner-join result without touching the left tree. -/
theorem Query.evalPrimaryKeyCandidates_empty_right_eq_eval (query : Query)
    (leftSchema rightSchema : Core.Schema) (left : List Core.Row)
    (onShape : query.on = some
      (rowidOn leftSchema.primaryKey rightSchema.primaryKey))
    (whereShape : query.where_ = none) (kindShape : query.kind = .inner) :
    query.evalPrimaryKeyCandidates [] [] = query.eval left [] := by
  have crossEmpty : crossRows left [] = [] := by
    induction left with
    | nil => rfl
    | cons _ rows induction => simp [crossRows, induction]
  simp [Query.evalPrimaryKeyCandidates, Query.eval, Query.selectedRows,
    onShape, whereShape, kindShape, mergeRowids, crossEmpty, matchingRows]

/-- Live join planner: a pure primary-key equijoin with no additional WHERE
filter uses the linear merge; every other shape retains the general 3VL nested
loop. A WHERE predicate whose operands all reference the left side is pushed
below either an inner or left outer join, avoiding construction of pairs for
discarded left rows. ORDER BY and LIMIT are applied after every access path. -/
def Query.selectedRowsPlanned (query : Query)
    (left right : Core.Table) : List JoinedRow :=
  if _merge : query.on =
        some (rowidOn left.schema.primaryKey right.schema.primaryKey) ∧
      query.where_ = none ∧ query.kind = .inner then
    query.finishRows (mergeRowids left.rows right.rows)
  else match query.where_ with
    | some where_ =>
        if _leftOnly : where_.leftOnly = true then
          let pushedLeft := left.rows.filter (selectsLeft where_)
          let selected := match query.kind with
            | .inner => matchingRows query.on none (crossRows pushedLeft right.rows)
            | .left => leftOuterRows query.on query.rightWidth pushedLeft right.rows
          query.finishRows selected
        else query.selectedRows left.rows right.rows
    | none => query.selectedRows left.rows right.rows

def Query.evalPlanned (query : Query) (left right : Core.Table) :
    List (List Core.Value) :=
  (query.selectedRowsPlanned left right).map (projectRow query.columns)

theorem Query.evalPlanned_eq_eval (query : Query)
    (left right : Core.Table) :
    query.evalPlanned left right = query.eval left.rows right.rows := by
  unfold Query.evalPlanned Query.eval
  apply congrArg (List.map (projectRow query.columns))
  unfold Query.selectedRowsPlanned
  split
  next mergeShape =>
    rcases mergeShape with ⟨onShape, whereShape, kindShape⟩
    rw [mergeRowids_eq_spec left.rows right.rows
      left.rowsWellFormed.2 right.rowsWellFormed.2]
    rw [rowidJoinSpec_eq_matchingRows left.schema right.schema
      left.rows right.rows left.rowsWellFormed.1 right.rowsWellFormed.1]
    simp [Query.selectedRows, onShape, whereShape, kindShape]
  next notMerge =>
    cases whereShape : query.where_ with
    | none => rfl
    | some where_ =>
        simp only [whereShape]
        split
        next leftOnly =>
          unfold Query.selectedRows
          simp only [whereShape]
          cases kindShape : query.kind with
          | inner =>
              simp only [kindShape]
              rw [matchingRows_pushLeft query.on leftOnly left.rows right.rows]
          | left =>
              simp only [kindShape]
              rw [leftOuterRows_pushLeft query.on query.rightWidth leftOnly
                left.rows right.rows]
        next => rfl

theorem Query.eval_width (query : Query) (left right : List Core.Row) :
    ∀ values ∈ query.eval left right, values.length = query.columns.length := by
  intro values membership
  simp only [Query.eval, List.mem_map] at membership
  obtain ⟨row, _, rfl⟩ := membership
  exact projectRow_length query.columns row

end CoreJoin

end SQLeanite
