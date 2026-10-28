import SQLeanite.Core.TableUpsertDifferencesSchema
import SQLeanite.CoreDistinct

namespace SQLeanite
namespace Core

def Row.value (row : Row) (column : Nat) : Value :=
  row.values[column]?.getD .null

theorem Row.value_primaryKey {schema : Schema} {row : Row}
    (valid : row.WellFormed schema) :
    row.value schema.primaryKey = .integer row.rowid := by
  unfold Row.value
  rw [valid.2.1]
  rfl

inductive Predicate where
  | equal (column : Nat) (value : Value)
  | notEqual (column : Nat) (value : Value)
  | compare (operation : PhysicalQuery.Comparison) (column : Nat) (value : Value)
  | isNull (column : Nat)
  | not (predicate : Predicate)
  | and (left right : Predicate)
  | or (left right : Predicate)
  deriving DecidableEq

def Predicate.eval : Predicate → Row → Truth
  | .equal column value, row => PhysicalQuery.sqlEquals (row.value column) value
  | .notEqual column value, row =>
      Truth.not (PhysicalQuery.sqlEquals (row.value column) value)
  | .compare operation column value, row =>
      PhysicalQuery.sqlCompare operation (row.value column) value
  | .isNull column, row => if row.value column = .null then .true else .false
  | .not predicate, row => Truth.not (predicate.eval row)
  | .and left right, row => Truth.and (left.eval row) (right.eval row)
  | .or left right, row => Truth.or (left.eval row) (right.eval row)

/-- Live three-valued predicate optimizer. Every rewrite below is valid for
UNKNOWN as well as TRUE/FALSE: double negation, equality-negation conversion,
and De Morgan. -/
def Predicate.optimize : Predicate → Predicate
  | .equal column value => .equal column value
  | .notEqual column value => .notEqual column value
  | .compare operation column value => .compare operation column value
  | .isNull column => .isNull column
  | .not predicate =>
      match predicate.optimize with
      | .not inner => inner
      | .equal column value => .notEqual column value
      | .notEqual column value => .equal column value
      | .and left right => .or (.not left) (.not right)
      | .or left right => .and (.not left) (.not right)
      | optimized => .not optimized
  | .and left right => .and left.optimize right.optimize
  | .or left right => .or left.optimize right.optimize

theorem Predicate.optimize_eval (predicate : Predicate) (row : Row) :
    predicate.optimize.eval row = predicate.eval row := by
  induction predicate with
  | equal | notEqual | compare | isNull => rfl
  | and left right leftInduction rightInduction =>
      simp [Predicate.optimize, Predicate.eval, leftInduction, rightInduction]
  | or left right leftInduction rightInduction =>
      simp [Predicate.optimize, Predicate.eval, leftInduction, rightInduction]
  | not predicate induction =>
      simp only [Predicate.optimize]
      cases optimized : predicate.optimize
      all_goals simp only [optimized, Predicate.eval] at induction ⊢
      all_goals rw [← induction]
      all_goals simp [Truth.not_not, Truth.deMorgan_and, Truth.deMorgan_or]

def selects : Option Predicate → Row → Bool
  | none, _ => true
  | some predicate, row => predicate.eval row = .true

theorem selects_primaryKey_integer_iff {schema : Schema} {row : Row}
    (valid : row.WellFormed schema) (target : Integer) :
    selects (some (.equal schema.primaryKey (.integer target))) row = true ↔
      row.rowid = target := by
  simp only [selects, Predicate.eval]
  simp [row.value_primaryKey valid, PhysicalQuery.sqlEquals]

def Table.primaryKeyRows (table : Table) (rowid : Integer) : List Row :=
  (table.findRowid? rowid).toList

/-- Exact primary-key pruning: routed lookup returns precisely the full-scan
filter, including the empty case. No post-lookup scan or runtime comparison is
needed. -/
theorem Table.primaryKeyRows_eq_filter (table : Table) (rowid : Integer) :
    table.primaryKeyRows rowid =
      table.rows.filter
        (selects (some (.equal table.schema.primaryKey (.integer rowid)))) := by
  unfold Table.primaryKeyRows
  cases found : table.findRowid? rowid with
  | none =>
      simp only [Option.toList_none]
      symm
      apply List.filter_eq_nil_iff.mpr
      intro row member
      cases selected : selects
          (some (.equal table.schema.primaryKey (.integer rowid))) row with
      | false => simp
      | true =>
          have same := (selects_primaryKey_integer_iff
            (table.rowsWellFormed.1 row member) rowid).mp selected
          have complete := table.findRowid?_eq_some_of_mem member same
          rw [found] at complete
          contradiction
  | some stored =>
      simp only [Option.toList_some]
      let predicate :=
        selects (some (.equal table.schema.primaryKey (.integer rowid)))
      have storedMember := table.findRowid?_some_mem found
      have storedSame := table.findRowid?_some_eq found
      have storedSelected : predicate stored = true :=
        (selects_primaryKey_integer_iff
          (table.rowsWellFormed.1 stored storedMember) rowid).mpr storedSame
      have selectedMember : stored ∈ table.rows.filter predicate :=
        List.mem_filter.mpr ⟨storedMember, storedSelected⟩
      have selectedUnique : ∀ row ∈ table.rows.filter predicate,
          row = stored := by
        intro row member
        have filtered := List.mem_filter.mp member
        have same := (selects_primaryKey_integer_iff
          (table.rowsWellFormed.1 row filtered.1) rowid).mp filtered.2
        have complete := table.findRowid?_eq_some_of_mem filtered.1 same
        rw [found] at complete
        exact (Option.some.inj complete).symm
      have rowsNodup : table.rows.Nodup := by
        exact table.rowsWellFormed.2.imp fun less equal => by
          cases equal
          exact Int.lt_irrefl _ less
      have selectedNodup := rowsNodup.filter predicate
      change [stored] = table.rows.filter predicate
      cases selectedEq : table.rows.filter predicate with
      | nil =>
          rw [selectedEq] at selectedMember
          contradiction
      | cons first rest =>
          rw [selectedEq] at selectedUnique selectedNodup
          have firstEqual := selectedUnique first (by simp)
          subst first
          cases rest with
          | nil => rfl
          | cons second rest =>
              have secondEqual := selectedUnique second (by simp)
              subst second
              simp at selectedNodup

theorem Table.primaryKeyRows_filter (table : Table) (rowid : Integer) :
    (table.primaryKeyRows rowid).filter
        (selects (some (.equal table.schema.primaryKey (.integer rowid)))) =
      table.rows.filter
        (selects (some (.equal table.schema.primaryKey (.integer rowid)))) := by
  rw [table.primaryKeyRows_eq_filter rowid, List.filter_filter]
  apply List.filter_congr
  intro row _
  cases selected : selects
      (some (.equal table.schema.primaryKey (.integer rowid))) row <;>
    simp [selected]

structure Query where
  columns : List Nat
  predicate : Option Predicate := none
  orderBy : List (Nat × Bool) := []
  limit : Option Nat := none
  distinct : Bool := false

def Query.optimize (query : Query) : Query :=
  { query with predicate := query.predicate.map Predicate.optimize }

theorem selects_optimize (predicate : Option Predicate) (row : Row) :
    selects (predicate.map Predicate.optimize) row = selects predicate row := by
  cases predicate with
  | none => rfl
  | some predicate => simp [selects, Predicate.optimize_eval]

def rowLess : List (Nat × Bool) → Row → Row → Bool
  | [], _, _ => false
  | term :: terms, left, right =>
      let order := PhysicalQuery.compareValue (left.value term.1) (right.value term.1)
      if order == .eq then rowLess terms left right
      else if term.2 then order == .gt else order == .lt

def insertOrdered (terms : List (Nat × Bool)) (row : Row) : List Row → List Row
  | [] => [row]
  | candidate :: rows =>
      if rowLess terms row candidate then row :: candidate :: rows
      else candidate :: insertOrdered terms row rows

theorem insertOrdered_perm (terms : List (Nat × Bool)) (row : Row)
    (rows : List Row) : (insertOrdered terms row rows).Perm (row :: rows) := by
  induction rows with
  | nil => exact List.Perm.refl _
  | cons candidate rows induction =>
      unfold insertOrdered
      split
      · exact List.Perm.refl _
      · exact (induction.cons candidate).trans (List.Perm.swap row candidate rows)

/-- Stable merge sort by the same strict order `insertOrdered` used. The
insertion sort it replaces was O(n^2) and cost ~3.1 s of the 3.6 s an
`ORDER BY` over 10,000 rows took. `a ≤ b` is `¬ (b < a)`, which makes
`List.mergeSort` stable in the same sense: equal rows keep input order. -/
def rowLe (terms : List (Nat × Bool)) (left right : Row) : Bool :=
  !rowLess terms right left

def Query.selectedRows (query : Query) (rows : List Row) : List Row :=
  let rows := rows.filter (selects query.predicate)
  let rows := if query.orderBy.isEmpty then rows
    else rows.mergeSort (rowLe query.orderBy)
  if query.distinct then rows
  else match query.limit with
    | none => rows
    | some limit => rows.take limit

def deduplicate [DecidableEq α] : List α → List α
  | [] => []
  | value :: values =>
      if value ∈ values then deduplicate values
      else value :: deduplicate values

theorem mem_deduplicate [DecidableEq α] (value : α) (values : List α) :
    value ∈ deduplicate values ↔ value ∈ values := by
  induction values with
  | nil => rfl
  | cons head values induction =>
      unfold deduplicate
      split
      · simp_all
      · simp_all

theorem deduplicate_nodup [DecidableEq α] (values : List α) :
    (deduplicate values).Nodup := by
  induction values with
  | nil => simp [deduplicate]
  | cons head values induction =>
      unfold deduplicate
      split
      · exact induction
      · apply List.nodup_cons.mpr
        exact ⟨by simpa [mem_deduplicate], induction⟩

/-- Preserve the first representative, rather than the last one, before LIMIT.
The historical last-retaining helper remains for its other callers. -/
def stableDeduplicate [DecidableEq α] (rows : List α) : List α :=
  (deduplicate rows.reverse).reverse

theorem mem_stableDeduplicate [DecidableEq α] (value : α) (rows : List α) :
    value ∈ stableDeduplicate rows ↔ value ∈ rows := by
  simp [stableDeduplicate, mem_deduplicate]

theorem stableDeduplicate_nodup [DecidableEq α] (rows : List α) :
    (stableDeduplicate rows).Nodup := by
  apply List.pairwise_reverse.mpr
  exact (deduplicate_nodup rows.reverse).imp (fun h => Ne.symm h)

theorem deduplicate_map_injective [DecidableEq α] [DecidableEq β]
    (f : α → β) (injective : Function.Injective f) (rows : List α) :
    deduplicate (rows.map f) = (deduplicate rows).map f := by
  induction rows with
  | nil => rfl
  | cons x xs ih =>
      have member : f x ∈ xs.map f ↔ x ∈ xs := by
        simp only [List.mem_map]
        constructor
        · rintro ⟨y, hy, equal⟩
          exact injective equal ▸ hy
        · intro h; exact ⟨x, h, rfl⟩
      simp only [List.map_cons, deduplicate, member]
      split <;> simp_all

theorem stableDeduplicate_map_injective [DecidableEq α] [DecidableEq β]
    (f : α → β) (injective : Function.Injective f) (rows : List α) :
    stableDeduplicate (rows.map f) = (stableDeduplicate rows).map f := by
  unfold stableDeduplicate
  rw [← List.map_reverse, deduplicate_map_injective f injective, List.map_reverse]

def limitRows (limit : Option Nat) (rows : List α) : List α :=
  match limit with | none => rows | some n => rows.take n

theorem mem_limitRows {limit : Option Nat} {rows : List α} {row : α}
    (h : row ∈ limitRows limit rows) : row ∈ rows := by
  cases limit with
  | none => exact h
  | some n => exact List.mem_of_mem_take h

theorem limitRows_nodup (limit : Option Nat) {rows : List α} (h : rows.Nodup) :
    (limitRows limit rows).Nodup := by
  cases limit with
  | none => exact h
  | some n => exact h.take

theorem limitRows_map (limit : Option Nat) (f : α → β) (rows : List α) :
    limitRows limit (rows.map f) = (limitRows limit rows).map f := by
  cases limit <;> simp [limitRows, List.map_take]

def Query.projectedRows (query : Query) (rows : List Row) : List (List Value) :=
  (query.selectedRows rows).map fun row => query.columns.map row.value

def Query.eval (query : Query) (rows : List Row) : List (List Value) :=
  let projected := query.projectedRows rows
  if query.distinct then limitRows query.limit (stableDistinctBy distinctRowKey projected) else projected

theorem Query.eval_distinct_limit (query : Query) (rows : List Row) (n : Nat)
    (enabled : query.distinct = true) (limited : query.limit = some n) :
    (query.eval rows).length ≤ n := by
  simp [Query.eval, enabled, limited, limitRows, Nat.min_le_left]

theorem Query.eval_primaryKey (table : Table) (query : Query) (rowid : Integer)
    (predicate : query.predicate =
      some (.equal table.schema.primaryKey (.integer rowid))) :
    query.eval (table.primaryKeyRows rowid) = query.eval table.rows := by
  unfold Query.eval Query.projectedRows Query.selectedRows
  rw [predicate, table.primaryKeyRows_filter rowid]

theorem Query.selectedRows_optimize (query : Query) (rows : List Row) :
    query.optimize.selectedRows rows = query.selectedRows rows := by
  unfold Query.optimize Query.selectedRows
  rw [List.filter_congr]
  intro row _
  exact selects_optimize query.predicate row

theorem Query.projectedRows_optimize (query : Query) (rows : List Row) :
    query.optimize.projectedRows rows = query.projectedRows rows := by
  unfold Query.projectedRows
  rw [Query.selectedRows_optimize]
  rfl

theorem Query.eval_optimize (query : Query) (rows : List Row) :
    query.optimize.eval rows = query.eval rows := by
  unfold Query.eval
  rw [Query.projectedRows_optimize]
  rfl

theorem Query.projectedRows_width (query : Query) (rows : List Row)
    {output : List Value} (member : output ∈ query.projectedRows rows) :
    output.length = query.columns.length := by
  unfold Query.projectedRows at member
  simp only [List.mem_map] at member
  rcases member with ⟨row, _, equal⟩
  subst output
  simp

theorem Query.eval_width (query : Query) (rows : List Row)
    {output : List Value} (member : output ∈ query.eval rows) :
    output.length = query.columns.length := by
  unfold Query.eval at member
  split at member
  next enabled =>
    have original : output ∈ query.projectedRows rows :=
      stableDistinctBy_subset distinctRowKey (query.projectedRows rows) (mem_limitRows member)
    exact Query.projectedRows_width query rows original
  next disabled => exact Query.projectedRows_width query rows member

theorem Query.eval_nodup_of_distinct (query : Query) (rows : List Row)
    (enabled : query.distinct = true) : (query.eval rows).Nodup := by
  simpa [Query.eval, enabled] using
    limitRows_nodup query.limit (stableDistinctBy_nodup distinctRowKey (query.projectedRows rows))

/-- DISTINCT output has unique SQL comparison keys, while preserving the
stored representation of each chosen row. -/
theorem Query.eval_distinct_key_nodup (query : Query) (rows : List Row)
    (enabled : query.distinct = true) :
    ((query.eval rows).map distinctRowKey).Nodup := by
  simp only [Query.eval, enabled, if_true]
  rw [← limitRows_map]
  exact limitRows_nodup _ (stableDistinctBy_key_nodup _ _)

/-- Does this row agree with the sought value on the indexed column, under the
same equality the predicate applies? -/
def indexColumnMatches (column : Nat) (value : Value) (row : Row) : Bool :=
  PhysicalQuery.sqlEquals (row.value column) value = .true

/-- Rows an equality or half-bounded range lookup would visit. The executable
in-memory Core uses the same predicate to model the physical index interval;
the physical page layer supplies the ordered traversal after persistence. -/
def indexedCandidates (index : Index) : Option Predicate → List Row → Option (List Row)
  | some predicate@(.equal column _), rows =>
      if column = index.column then
        some (rows.filter (selects (some predicate)))
      else none
  | some predicate@(.compare _ column _), rows =>
      if column = index.column then
        some (rows.filter (selects (some predicate)))
      else none
  | _, _ => none

/-- A row kept by an equality predicate always matches on the indexed column. -/
theorem selects_imp_indexColumnMatches {column : Nat} {value : Value} {row : Row}
    (kept : selects (some (.equal column value)) row = true) :
    indexColumnMatches column value row = true := by
  exact kept

/-- **P2 on the Core path.** Filtering the index candidates yields exactly the
same rows, in the same order, as filtering the entire table. -/
theorem indexedCandidates_filter_eq_scan (index : Index)
    (predicate : Option Predicate) (rows candidates : List Row)
    (narrowed : indexedCandidates index predicate rows = some candidates) :
    candidates.filter (selects predicate) = rows.filter (selects predicate) := by
  cases predicate with
  | none => simp [indexedCandidates] at narrowed
  | some p =>
    cases p with
    | equal column value =>
        simp only [indexedCandidates] at narrowed
        split at narrowed
        · simp only [Option.some.injEq] at narrowed
          subst candidates
          rw [List.filter_filter]
          apply List.filter_congr
          intro row _
          by_cases kept : selects (some (Predicate.equal column value)) row = true
          · simp [kept]
          · simp only [Bool.not_eq_true] at kept
            simp [kept]
        · simp at narrowed
    | notEqual _ _ => simp [indexedCandidates] at narrowed
    | compare operation column value =>
        simp only [indexedCandidates] at narrowed
        split at narrowed
        · simp only [Option.some.injEq] at narrowed
          subst candidates
          rw [List.filter_filter]
          apply List.filter_congr
          intro row _
          by_cases kept :
              selects (some (Predicate.compare operation column value)) row = true
          · simp [kept]
          · simp only [Bool.not_eq_true] at kept
            simp [kept]
        · simp at narrowed
    | isNull _ => simp [indexedCandidates] at narrowed
    | not _ => simp [indexedCandidates] at narrowed
    | and _ _ => simp [indexedCandidates] at narrowed
    | or _ _ => simp [indexedCandidates] at narrowed

/-- Query results are unchanged when the index is used, since `selectedRows`
consumes the filtered list and nothing else. -/
theorem Query.eval_indexed (index : Index) (query : Query)
    (rows candidates : List Row)
    (narrowed : indexedCandidates index query.predicate rows = some candidates) :
    query.eval candidates = query.eval rows := by
  unfold Query.eval Query.projectedRows Query.selectedRows
  rw [indexedCandidates_filter_eq_scan index query.predicate rows candidates narrowed]

/-- Pick an index that serves this predicate, if any. -/
def Table.chooseIndex? (table : Table) (predicate : Option Predicate) : Option Index :=
  match predicate with
  | some (.equal column _) => table.indexes.find? (fun index => index.column = column)
  | some (.compare _ column _) =>
      table.indexes.find? (fun index => index.column = column)
  | _ => none

inductive AccessPath where
  | fullScan
  | primaryKey (rowid : Integer)
  | equalityIndex (index : Index)
  | rangeIndex (index : Index)
  deriving DecidableEq

def AccessPath.estimatedRows (tableRows : Nat) : AccessPath → Nat
  | .fullScan => tableRows
  | .primaryKey _ => 1
  | .equalityIndex _ => max 1 (tableRows / 16)
  | .rangeIndex _ => max 1 (tableRows / 4)

end Core

end SQLeanite
