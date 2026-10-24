import SQLeanite.CoreJoin
import SQLeanite.CoreDistinct
import SQLeanite.PhysicalQuery
import SQLeanite.SQLite.AggregateSum

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

private theorem max_div_le_max (rows divisor : Nat) :
    max 1 (rows / divisor) ≤ max 1 rows := by
  exact Nat.max_le.2 ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.div_le_self rows divisor) (Nat.le_max_right _ _)⟩

/-- Cost-aware access-path choice. Applicable indexes have a lower selectivity
estimate than a scan; unsupported predicate shapes retain the scan. -/
def Table.chooseAccessPath (table : Table) (predicate : Option Predicate) :
    AccessPath :=
  match predicate with
  | some (.equal column value) =>
      match value with
      | .integer rowid =>
          if column = table.schema.primaryKey then .primaryKey rowid
          else match table.indexes.find? (fun index => index.column = column) with
            | some index => .equalityIndex index
            | none => .fullScan
      | _ =>
          match table.indexes.find? (fun index => index.column = column) with
          | some index => .equalityIndex index
          | none => .fullScan
  | some (.compare _ column _) =>
      match table.indexes.find? (fun index => index.column = column) with
      | some index => .rangeIndex index
      | none => .fullScan
  | _ => .fullScan

private theorem chooseAccessPath_primaryKey {table : Table}
    {predicate : Option Predicate} {rowid : Integer}
    (chosen : table.chooseAccessPath predicate = .primaryKey rowid) :
    predicate = some
      (.equal table.schema.primaryKey (.integer rowid)) := by
  cases predicate with
  | none => simp [Table.chooseAccessPath] at chosen
  | some predicate =>
      cases predicate with
      | equal column value =>
          cases value with
          | integer target =>
              simp only [Table.chooseAccessPath] at chosen
              split at chosen
              next sameColumn =>
                have targetEqual : target = rowid :=
                  AccessPath.primaryKey.inj chosen
                subst target
                rw [sameColumn]
              next different =>
                split at chosen <;> contradiction
          | null | realBits | text | blob =>
              simp only [Table.chooseAccessPath] at chosen
              split at chosen <;> contradiction
      | compare operation column value =>
          simp only [Table.chooseAccessPath] at chosen
          split at chosen <;> contradiction
      | notEqual | isNull | not | and | or =>
          simp [Table.chooseAccessPath] at chosen

theorem Table.chooseAccessPath_estimatedRows_le (table : Table)
    (predicate : Option Predicate) :
    (table.chooseAccessPath predicate).estimatedRows table.rows.length ≤
      max 1 table.rows.length := by
  cases predicate with
  | none =>
      simp only [Table.chooseAccessPath, AccessPath.estimatedRows]
      exact Nat.le_max_right _ _
  | some predicate =>
    cases predicate with
    | equal column value =>
        cases value with
        | integer rowid =>
            simp only [Table.chooseAccessPath]
            split
            · simp only [AccessPath.estimatedRows]
              exact Nat.le_max_left _ _
            · split
              · exact max_div_le_max _ _
              · exact Nat.le_max_right _ _
        | null | realBits | text | blob =>
            simp only [Table.chooseAccessPath]
            split
            · exact max_div_le_max _ _
            · exact Nat.le_max_right _ _
    | compare operation column value =>
        simp only [Table.chooseAccessPath]
        split
        · exact max_div_le_max _ _
        · exact Nat.le_max_right _ _
    | notEqual | isNull | not | and | or =>
        simp only [Table.chooseAccessPath, AccessPath.estimatedRows]
        exact Nat.le_max_right _ _

/-- Rows the planner feeds to a query: index candidates when an index applies,
otherwise the whole table. -/
def Table.plannedRows (table : Table) (query : Query) : List Row :=
  match table.chooseAccessPath query.predicate with
  | .primaryKey rowid => table.primaryKeyRows rowid
  | .equalityIndex index | .rangeIndex index =>
      (indexedCandidates index query.predicate table.rows).getD table.rows
  | .fullScan => table.rows

/-- **Planning is semantics-preserving.** Using an index changes nothing a query
can observe, so the executor may substitute `plannedRows` for the full table. -/
theorem Query.eval_plannedRows (table : Table) (query : Query) :
    query.eval (table.plannedRows query) = query.eval table.rows := by
  unfold Table.plannedRows
  cases chosen : table.chooseAccessPath query.predicate with
  | fullScan => simp [chosen]
  | primaryKey rowid =>
      simp only [chosen]
      exact Query.eval_primaryKey table query rowid
        (chooseAccessPath_primaryKey chosen)
  | equalityIndex index =>
      cases narrowed : indexedCandidates index query.predicate table.rows with
      | none => simp [chosen, narrowed]
      | some candidates =>
          simp only [chosen, narrowed, Option.getD_some]
          exact Query.eval_indexed index query table.rows candidates narrowed
  | rangeIndex index =>
      cases narrowed : indexedCandidates index query.predicate table.rows with
      | none => simp [chosen, narrowed]
      | some candidates =>
          simp only [chosen, narrowed, Option.getD_some]
          exact Query.eval_indexed index query table.rows candidates narrowed

def Database.modifyTable (database : Database) (name : String)
    (operation : Table → Except String Table) : Except String Database := do
  let table ← match database.findTable? name with
    | some table => .ok table
    | none => .error s!"no such table: {name}"
  let replacement ← operation table
  database.updateTable replacement

theorem Database.modifyTable_exact {database next : Database} {name : String}
    {operation : Table → Except String Table}
    (success : database.modifyTable name operation = .ok next) :
    ∃ table replacement,
      database.findTable? name = some table ∧
      operation table = .ok replacement ∧
      database.updateTable replacement = .ok next := by
  unfold Database.modifyTable at success
  cases found : database.findTable? name with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases operated : operation table with
      | error message =>
          simp [found, operated, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok replacement =>
          cases updated : database.updateTable replacement with
          | error message =>
              simp [found, operated, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok output =>
              simp [found, operated, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              subst next
              exact ⟨table, replacement, rfl, operated, updated⟩

/-- Resolve a declared TEXT primary key through its proof-carrying balanced
map.  Keeping this operation separate makes the trust argument explicit: the
map is not an opportunistic cache, but an exact abstraction of the logical row
list established by `declaredKeyMapRepresents`. -/
def Table.findDeclaredTextRowid? (table : Table) (text : PhysicalCodec.Text) :
    Option Integer :=
  if table.schema.hasHiddenRowid then
    (table.declaredKeyMap.get? (.text text)).map (·.rowid)
  else none

/-- A successful declared-key route names a real logical row with precisely
that key.  Thus the point updater cannot be sent to an unrelated row by stale
or merely advisory index data. -/
theorem Table.findDeclaredTextRowid?_some_mem {table : Table}
    {text : PhysicalCodec.Text} {rowid : Integer}
    (found : table.findDeclaredTextRowid? text = some rowid) :
    ∃ row, row ∈ table.rows ∧ row.rowid = rowid ∧
      row.declaredKey table.schema = .text text := by
  unfold Table.findDeclaredTextRowid? at found
  split at found
  next hidden =>
    rcases Option.map_eq_some_iff.mp found with ⟨row, owner, rowidEqual⟩
    have represented := table.declaredKeyMapRepresents hidden (.text text)
    rw [owner] at represented
    have logical : table.rows.find? (fun candidate =>
        candidate.declaredKey table.schema == .text text) = some row :=
      represented.symm
    refine ⟨row, List.mem_of_find?_eq_some logical, ?_, ?_⟩
    · exact rowidEqual
    · simpa only [beq_iff_eq] using List.find?_some logical
  next => contradiction

/-- Recognize the UPDATE shapes that can safely use one primary-tree lookup.
Besides the INTEGER PRIMARY KEY alias, a declared TEXT PRIMARY KEY first
routes through its exact key map and then uses the returned hidden rowid. -/
def Table.pointUpdateRowid? (table : Table)
    (assignments : List (Nat × Value)) : Option Predicate → Option Integer
  | some (.equal column value) =>
      if assignments.all (fun assignment => assignment.1 != column) then
        if column == table.schema.primaryKey then
          match value with
          | .integer rowid => some rowid
          | _ => none
        else if table.schema.hasHiddenRowid &&
            column == table.schema.declaredPrimaryKey then
          match value with
          | .text text => table.findDeclaredTextRowid? text
          | _ => none
        else none
      else none
  | _ => none

/-- The logical UPDATE operation named independently of the statement
executor, so execute-level correspondence can expose exactly which table
transformation succeeded. -/
def Table.updateWhere (table : Table) (assignments : List (Nat × Value))
    (predicate : Option Predicate) : Except String (Table × Nat) :=
  match table.pointUpdateRowid? assignments predicate with
  | some rowid => table.patchRowid assignments rowid
  | none => do
      let replacement ← table.patchRows assignments (selects predicate)
      return (replacement, (table.rows.filter (selects predicate)).length)

theorem Table.updateWhere_schema {table next : Table}
    {assignments : List (Nat × Value)} {predicate : Option Predicate}
    {changes : Nat}
    (success : table.updateWhere assignments predicate = .ok (next, changes)) :
    next.schema = table.schema := by
  unfold Table.updateWhere at success
  cases pointResult : table.pointUpdateRowid? assignments predicate with
  | some rowid =>
    rw [pointResult] at success
    exact Table.patchRowid_schema success
  | none =>
    rw [pointResult] at success
    cases patched : table.patchRows assignments (selects predicate) with
    | error message =>
        rw [patched] at success
        contradiction
    | ok replacement =>
        rw [patched] at success
        have pairEqual := Except.ok.inj success
        have tableEqual : replacement = next := by
          simpa using congrArg Prod.fst pairEqual
        subst next
        exact Table.patchRows_schema patched

theorem Table.updateWhere_exact {table next : Table}
    {assignments : List (Nat × Value)} {predicate : Option Predicate}
    {changes : Nat}
    (success : table.updateWhere assignments predicate = .ok (next, changes)) :
    (∃ rowid,
      table.pointUpdateRowid? assignments predicate = some rowid ∧
      table.patchRowid assignments rowid = .ok (next, changes)) ∨
    (table.pointUpdateRowid? assignments predicate = none ∧
      ∃ rows,
        Core.patchRows table.schema assignments (selects predicate)
          table.rows = .ok rows ∧
        next.rows = rows ∧
        changes = (table.rows.filter (selects predicate)).length) := by
  unfold Table.updateWhere at success
  cases pointResult : table.pointUpdateRowid? assignments predicate with
  | some rowid =>
      rw [pointResult] at success
      exact Or.inl ⟨rowid, rfl, success⟩
  | none =>
      rw [pointResult] at success
      cases patchedRows : Core.patchRows table.schema assignments
          (selects predicate) table.rows with
      | error message =>
          have patchFailed : table.patchRows assignments (selects predicate) =
              .error message := by
            unfold Table.patchRows
            rw [patchedRows]
            rfl
          rw [patchFailed] at success
          contradiction
      | ok rows =>
          cases patched : table.patchRows assignments (selects predicate) with
          | error message =>
              rw [patched] at success
              contradiction
          | ok replacement =>
              rw [patched] at success
              have pairEqual := Except.ok.inj success
              have tableEqual : replacement = next := by
                simpa using congrArg Prod.fst pairEqual
              have changesEqual :
                  (table.rows.filter (selects predicate)).length = changes := by
                simpa using congrArg Prod.snd pairEqual
              subst next
              exact Or.inr ⟨rfl, rows, rfl,
                Table.patchRows_exact patchedRows patched, changesEqual.symm⟩

structure Result where
  rows : List (List Value) := []
  changes : Nat := 0

/-- Check an arbitrary mathematical integer against SQLite's signed 64-bit
INTEGER domain. -/
def checkedInteger (value : Int) : Except String Integer :=
  if lower : -(Int.ofNat FileFormat.IntegerWidth.eight.midpoint) ≤ value then
    if upper : value < Int.ofNat FileFormat.IntegerWidth.eight.midpoint then
      .ok ⟨value, lower, upper⟩
    else .error "integer is above the signed 64-bit range"
  else .error "integer is below the signed 64-bit range"

theorem checkedInteger_exact {value : Int} {integer : Integer}
    (success : checkedInteger value = .ok integer) : integer.value = value := by
  unfold checkedInteger at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  injection success with equal
  subst integer
  rfl

/-- Embed a finite row count in SQLite's signed 64-bit INTEGER domain.  The
guard is executable and the returned bounds are kernel-checked; an impossible
in-memory table larger than `2^63-1` rows is reported rather than wrapped. -/
def countInteger (count : Nat) : Except String Integer :=
  if upper : count < FileFormat.IntegerWidth.eight.midpoint then
    .ok {
      value := Int.ofNat count
      lowerBound := by simp
      upperBound := Int.ofNat_lt.mpr upper }
  else .error "COUNT(*) exceeds the signed 64-bit INTEGER range"

theorem countInteger_exact {count : Nat} {integer : Integer}
    (success : countInteger count = .ok integer) :
    integer.value = Int.ofNat count := by
  unfold countInteger at success
  split at success
  next upper =>
    injection success with equal
    subst integer
    rfl
  next tooLarge => contradiction

inductive CountTarget where
  | star
  | column (index : Nat)
  deriving DecidableEq, Repr

def CountTarget.includes : CountTarget → Row → Bool
  | .star, _ => true
  | .column index, row => row.value index != .null

def countRows (target : CountTarget) (predicate : Option Predicate)
    (rows : List Row) : Nat :=
  (rows.filter (selects predicate)).countP target.includes

theorem countRows_star (predicate : Option Predicate) (rows : List Row) :
    countRows .star predicate rows = (rows.filter (selects predicate)).length := by
  unfold countRows
  induction rows.filter (selects predicate) with
  | nil => rfl
  | cons row rows induction => simp [CountTarget.includes, List.countP_cons, induction]

def addInteger (left right : Integer) : Except String Integer :=
  checkedInteger (left.value + right.value)

theorem addInteger_exact {left right result : Integer}
    (success : addInteger left right = .ok result) :
    result.value = left.value + right.value := by
  exact checkedInteger_exact success

def sumIntegerFrom (accumulator : Integer) :
    List Integer → Except String Integer
  | [] => .ok accumulator
  | value :: values =>
      match addInteger accumulator value with
      | .error message => .error message
      | .ok next => sumIntegerFrom next values

theorem sumIntegerFrom_exact {accumulator result : Integer}
    {values : List Integer}
    (success : sumIntegerFrom accumulator values = .ok result) :
    result.value = accumulator.value + (values.map (·.value)).sum := by
  induction values generalizing accumulator result with
  | nil =>
      simp [sumIntegerFrom] at success
      subst result
      simp
  | cons value values induction =>
      simp only [sumIntegerFrom] at success
      cases added : addInteger accumulator value with
      | error message => simp [added] at success
      | ok next =>
          simp [added] at success
          have tailExact := induction success
          have addExact := addInteger_exact added
          simp only [List.map_cons, List.sum_cons]
          omega

def sumIntegers : List Integer → Except String (Option Integer)
  | [] => .ok none
  | value :: values =>
      match sumIntegerFrom value values with
      | .error message => .error message
      | .ok total => .ok (some total)

theorem sumIntegers_exact {values : List Integer} {result : Integer}
    (success : sumIntegers values = .ok (some result)) :
    result.value = (values.map (·.value)).sum := by
  cases values with
  | nil => simp [sumIntegers] at success
  | cons value values =>
      simp only [sumIntegers] at success
      cases folded : sumIntegerFrom value values with
      | error message => simp [folded] at success
      | ok total =>
          simp [folded] at success
          subst result
          simpa using sumIntegerFrom_exact folded

def columnIntegers (column : Nat) : List Row → Except String (List Integer)
  | [] => .ok []
  | row :: rows =>
      match row.value column with
      | .null => columnIntegers column rows
      | .integer value => (value :: ·) <$> columnIntegers column rows
      | .realBits _ | .text _ | .blob _ =>
          .error "SUM requires INTEGER or NULL values in the verified Core"

/-- The all-integer fast path retains its exact-sum theorem. Mixed storage
classes use the ordered SQLite accumulator, including delayed overflow errors. -/
def sumColumn (column : Nat) (rows : List Row) : Except String Value :=
  match columnIntegers column rows with
  | .error _ => SQLite.AggregateSum.sum (rows.map (·.value column))
  | .ok integers => do
      match ← sumIntegers integers with
      | none => .ok .null
      | some total => .ok (.integer total)

def averageColumn (column : Nat) (rows : List Row) : Value :=
  SQLite.AggregateSum.average (rows.map (·.value column))

def totalColumn (column : Nat) (rows : List Row) : Value :=
  SQLite.AggregateSum.total (rows.map (·.value column))

/-- Select one non-NULL value using SQLite's total storage-class ordering.
`minimum = true` chooses MIN; false chooses MAX. -/
def chooseExtreme (minimum : Bool) (left right : Value) : Value :=
  match left, right with
  | .null, value => value
  | value, .null => value
  | left, right =>
      let order := PhysicalQuery.compareValue left right
      if (minimum && order != .gt) || (!minimum && order != .lt) then left
      else right

theorem chooseExtreme_tie (minimum : Bool) (left right : Value)
    (leftNotNull : left ≠ .null) (rightNotNull : right ≠ .null)
    (equal : PhysicalQuery.compareValue left right = .eq) :
    chooseExtreme minimum left right = left := by
  cases left <;> cases right <;> simp_all [chooseExtreme]
  all_goals cases minimum <;> simp_all

def extremeValues (minimum : Bool) : List Value → Value
  | [] => .null
  | value :: values => chooseExtreme minimum value (extremeValues minimum values)

def extremeColumn (minimum : Bool) (column : Nat) (rows : List Row) : Value :=
  extremeValues minimum (rows.map (fun row => row.value column))

theorem chooseExtreme_eq_left_or_right (minimum : Bool) (left right : Value) :
    chooseExtreme minimum left right = left ∨
      chooseExtreme minimum left right = right := by
  cases left <;> cases right
  all_goals
    rw [chooseExtreme]
    first | (split <;> simp) | simp
  all_goals simp_all

theorem extremeValues_mem_or_null (minimum : Bool) (values : List Value) :
    extremeValues minimum values = .null ∨
      extremeValues minimum values ∈ values := by
  induction values with
  | nil => simp [extremeValues]
  | cons value values induction =>
      simp only [extremeValues]
      rcases chooseExtreme_eq_left_or_right minimum value
          (extremeValues minimum values) with chosen | chosen
      · exact .inr (by simp [chosen])
      · rcases induction with empty | member
        · exact .inl (by simpa [chosen] using empty)
        · exact .inr (by simp [chosen, member])

inductive GroupOutput where
  /-- Project a position in the query's group-key tuple. -/
  | key (position : Nat)
  | countStar
  | countColumn (column : Nat)
  | sumColumn (column : Nat)
  | averageColumn (column : Nat)
  | totalColumn (column : Nat)
  | minColumn (column : Nat)
  | maxColumn (column : Nat)
  deriving DecidableEq, Repr

structure GroupQuery where
  groupBy : List Nat
  outputs : List GroupOutput
  predicate : Option Predicate := none

def GroupQuery.originalKey (query : GroupQuery) (row : Row) : List Value :=
  query.groupBy.map row.value

/-- GROUP BY uses the same exact BINARY numeric equivalence as DISTINCT. -/
def GroupQuery.rowKey (query : GroupQuery) (row : Row) : List Value :=
  distinctRowKey (query.originalKey row)

def GroupQuery.selectedRows (query : GroupQuery) (rows : List Row) : List Row :=
  rows.filter (selects query.predicate)

/-- Canonical comparison keys, presented in SQLite's ascending group order.
Original group output values are read from a representative source row. -/
def GroupQuery.groupKeys (query : GroupQuery) (rows : List Row) : List (List Value) :=
  (deduplicate ((query.selectedRows rows).map query.rowKey)).mergeSort
    (fun a b => PhysicalQuery.compareValues a b != .gt)

theorem GroupQuery.groupKeys_nodup (query : GroupQuery) (rows : List Row) :
    (query.groupKeys rows).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (deduplicate_nodup _)

theorem GroupQuery.mem_groupKeys_iff (query : GroupQuery) (rows : List Row)
    (key : List Value) :
    key ∈ query.groupKeys rows ↔
      ∃ row ∈ rows, selects query.predicate row = true ∧ query.rowKey row = key := by
  rw [GroupQuery.groupKeys, (List.mergeSort_perm _ _).mem_iff, mem_deduplicate]
  simp only [GroupQuery.selectedRows, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨row, ⟨member, selected⟩, equal⟩
    exact ⟨row, member, selected, equal⟩
  · rintro ⟨row, member, selected, equal⟩
    exact ⟨row, ⟨member, selected⟩, equal⟩

def GroupQuery.keyCount (query : GroupQuery) (rows : List Row)
    (key : List Value) : Nat :=
  (query.selectedRows rows).countP fun row => query.rowKey row == key

def GroupQuery.keyRows (query : GroupQuery) (rows : List Row)
    (key : List Value) : List Row :=
  (query.selectedRows rows).filter fun row => query.rowKey row == key

/-- A MIN/MAX step updates bare columns only on improvement. If every input
is NULL, SQLite keeps loading the current row because no best value exists. -/
def extremeRepresentativeStep (minimum : Bool) (column : Nat) (best row : Row) : Row :=
  if best.value column == .null then row
  else if row.value column == .null then best
  else
    let order := PhysicalQuery.compareValue (row.value column) (best.value column)
    if (minimum && order == .lt) || (!minimum && order == .gt) then row else best

theorem extremeRepresentativeStep_member (minimum : Bool) (column : Nat) (best row : Row) :
    extremeRepresentativeStep minimum column best row = best ∨
      extremeRepresentativeStep minimum column best row = row := by
  unfold extremeRepresentativeStep
  split
  · exact Or.inr rfl
  · split
    · exact Or.inl rfl
    · dsimp only
      split
      · exact Or.inr rfl
      · exact Or.inl rfl

def extremeRepresentative (minimum : Bool) (column : Nat) (first : Row) : List Row → Row
  | [] => first
  | row :: rows => extremeRepresentative minimum column
      (extremeRepresentativeStep minimum column first row) rows

theorem extremeRepresentative_mem (minimum : Bool) (column : Nat) (first : Row) (rows : List Row) :
    extremeRepresentative minimum column first rows ∈ first :: rows := by
  induction rows generalizing first with
  | nil => simp [extremeRepresentative]
  | cons row rows ih =>
      change extremeRepresentative minimum column (extremeRepresentativeStep minimum column first row) rows ∈ first :: row :: rows
      have member := ih (extremeRepresentativeStep minimum column first row)
      rcases List.mem_cons.mp member with same | tail
      · rw [same]
        rcases extremeRepresentativeStep_member minimum column first row with best | current
        · simp [best]
        · simp [current]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ tail)

/-- Repeated aggregate expressions share one SQLite accumulator. The last
unique MIN/MAX accumulator controls bare-column row selection. -/
def GroupQuery.controllingExtreme (query : GroupQuery) : Option (Bool × Nat) :=
  (stableDistinctBy id query.outputs).foldl (fun current output =>
    match output with
    | .minColumn column => some (true, column)
    | .maxColumn column => some (false, column)
    | _ => current) none

def GroupQuery.representative (query : GroupQuery) (rows : List Row) (key : List Value) : Option Row :=
  match query.keyRows rows key with
  | [] => none
  | first :: rest => some <| match query.controllingExtreme with
      | none => first
      | some (minimum, column) => extremeRepresentative minimum column first rest

theorem GroupQuery.representative_mem (query : GroupQuery) (rows : List Row) (key : List Value)
    (chosen : Row) (success : query.representative rows key = some chosen) :
    chosen ∈ query.keyRows rows key := by
  unfold GroupQuery.representative at success
  cases found : query.keyRows rows key with
  | nil => simp [found] at success
  | cons first rest =>
      cases controls : query.controllingExtreme with
      | none => simp [found, controls] at success; subst chosen; simp
      | some control =>
          rcases control with ⟨minimum, column⟩
          simp [found, controls] at success
          subst chosen
          exact extremeRepresentative_mem minimum column first rest

theorem GroupQuery.representative_key (query : GroupQuery) (rows : List Row) (key : List Value)
    (chosen : Row) (success : query.representative rows key = some chosen) :
    query.rowKey chosen = key := by
  have member := query.representative_mem rows key chosen success
  simpa only [beq_iff_eq] using (List.mem_filter.mp member).2

def GroupQuery.outputKey (query : GroupQuery) (rows : List Row) (key : List Value) : List Value :=
  ((query.representative rows key).map query.originalKey).getD key

def GroupQuery.outputValue (query : GroupQuery) (rows : List Row)
    (key : List Value) : GroupOutput → Except String Value
  | .key position => .ok ((query.outputKey rows key)[position]?.getD .null)
  | .countStar =>
      .integer <$> countInteger (query.keyRows rows key).length
  | .countColumn column =>
      .integer <$> countInteger ((query.keyRows rows key).countP
        fun row => row.value column != .null)
  | .sumColumn column => sumColumn column (query.keyRows rows key)
  | .averageColumn column => .ok (averageColumn column (query.keyRows rows key))
  | .totalColumn column => .ok (totalColumn column (query.keyRows rows key))
  | .minColumn column => .ok (extremeColumn true column (query.keyRows rows key))
  | .maxColumn column => .ok (extremeColumn false column (query.keyRows rows key))

def GroupQuery.evalOutputs (query : GroupQuery) (rows : List Row)
    (key : List Value) : List GroupOutput → Except String (List Value)
  | [] => .ok []
  | output :: outputs =>
      match query.outputValue rows key output with
      | .error message => .error message
      | .ok value =>
          match query.evalOutputs rows key outputs with
          | .error message => .error message
          | .ok values => .ok (value :: values)

theorem GroupQuery.evalOutputs_length (query : GroupQuery) (rows : List Row)
    (key : List Value) (outputs : List GroupOutput) (result : List Value)
    (success : query.evalOutputs rows key outputs = .ok result) :
    result.length = outputs.length := by
  induction outputs generalizing result with
  | nil =>
      simp [GroupQuery.evalOutputs] at success
      subst result
      rfl
  | cons output outputs induction =>
      simp only [GroupQuery.evalOutputs] at success
      cases head : query.outputValue rows key output with
      | error message => simp [head] at success
      | ok value =>
          simp only [head] at success
          cases tail : query.evalOutputs rows key outputs with
          | error message => simp [tail] at success
          | ok values =>
              simp [tail] at success
              subst result
              simp [induction values tail]

def GroupQuery.evalKeys (query : GroupQuery) (rows : List Row) :
    List (List Value) → Except String (List (List Value))
  | [] => .ok []
  | key :: keys =>
      match query.evalOutputs rows key query.outputs with
      | .error message => .error message
      | .ok result =>
          match query.evalKeys rows keys with
          | .error message => .error message
          | .ok results =>
              .ok (result :: results)

def GroupQuery.eval (query : GroupQuery) (rows : List Row) :
    Except String (List (List Value)) :=
  query.evalKeys rows (query.groupKeys rows)

theorem GroupQuery.evalKeys_width (query : GroupQuery) (rows : List Row)
    (keys : List (List Value)) (output : List (List Value))
    (success : query.evalKeys rows keys = .ok output) :
    ∀ result ∈ output, result.length = query.outputs.length := by
  induction keys generalizing output with
  | nil =>
      simp [GroupQuery.evalKeys] at success
      subst output
      simp
  | cons key keys induction =>
      simp only [GroupQuery.evalKeys] at success
      cases evaluated : query.evalOutputs rows key query.outputs with
      | error message => simp [evaluated] at success
      | ok head =>
          simp only [evaluated] at success
          cases tailResult : query.evalKeys rows keys with
          | error message => simp [tailResult] at success
          | ok tail =>
              simp [tailResult] at success
              subst output
              have headWidth :=
                query.evalOutputs_length rows key query.outputs head evaluated
              intro result member
              simp only [List.mem_cons] at member
              rcases member with equal | member
              · subst result
                exact headWidth
              · exact induction _ tailResult result member

theorem GroupQuery.eval_width (query : GroupQuery) (rows : List Row)
    (output : List (List Value))
    (success : query.eval rows = .ok output) :
    ∀ result ∈ output, result.length = query.outputs.length := by
  exact query.evalKeys_width rows (query.groupKeys rows) output success

inductive Command where
  | createTable (schema : Schema)
  | createIndex (table : String) (index : Index)
  | insert (table : String) (values : List Value)
  | replace (table : String) (values : List Value)
  | deleteWhere (table : String) (predicate : Option Predicate)
  | updateWhere (table : String) (assignments : List (Nat × Value))
      (predicate : Option Predicate)
  | query (table : String) (query : Query)
  | count (table : String) (target : CountTarget) (predicate : Option Predicate)
  | sum (table : String) (column : Nat) (predicate : Option Predicate)
  | extreme (table : String) (minimum : Bool) (column : Nat)
      (predicate : Option Predicate)
  | group (table : String) (query : GroupQuery)
  | join (left right : String) (query : CoreJoin.Query)
  | begin
  | commit
  | rollback

def Command.writes : Command → Bool
  | .createTable _ | .createIndex .. | .insert .. | .replace .. | .deleteWhere .. |
      .updateWhere .. => true
  | _ => false

structure State where
  database : Database
  transactionSnapshot : Option Database := none

def State.empty : State := { database := Database.empty }

def execute (state : State) : Command → Except String (State × Result)
  | .createTable schema => do
      let database ← state.database.createTable schema
      return ({ state with database }, {})
  | .createIndex tableName index => do
      let database ← state.database.modifyTable tableName fun table =>
        table.addIndex index
      return ({ state with database }, {})
  | .insert tableName values => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let replacement ← table.insertValues values
      let database ← state.database.updateTable replacement
      return ({ state with database }, { changes := 1 })
  | .replace tableName values => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let replacement ← table.replaceValues values
      let database ← state.database.updateTable replacement
      return ({ state with database }, { changes := 1 })
  | .deleteWhere tableName predicate => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let replacement ← table.retainRows fun row => !selects predicate row
      let database ← state.database.updateTable replacement
      return ({ state with database }, {
        changes := table.rows.length - replacement.rows.length })
  | .updateWhere tableName assignments predicate => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let (replacement, changes) ← table.updateWhere assignments predicate
      let database ← state.database.updateTable replacement
      return ({ state with database }, { changes })
  | .query tableName query => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let optimized := query.optimize
      return (state, { rows := optimized.eval (table.plannedRows optimized) })
  | .count tableName target predicate =>
      match state.database.findTable? tableName with
      | none => .error s!"no such table: {tableName}"
      | some table =>
          match countInteger (countRows target predicate table.rows) with
          | .error message => .error message
          | .ok count => .ok (state, { rows := [[.integer count]] })
  | .sum tableName column predicate =>
      match state.database.findTable? tableName with
      | none => .error s!"no such table: {tableName}"
      | some table =>
          match sumColumn column (table.rows.filter (selects predicate)) with
          | .error message => .error message
          | .ok value => .ok (state, { rows := [[value]] })
  | .extreme tableName minimum column predicate =>
      match state.database.findTable? tableName with
      | none => .error s!"no such table: {tableName}"
      | some table =>
          let value := extremeColumn minimum column
            (table.rows.filter (selects predicate))
          .ok (state, { rows := [[value]] })
  | .group tableName query =>
      match state.database.findTable? tableName with
      | none => .error s!"no such table: {tableName}"
      | some table =>
          match query.eval table.rows with
          | .error message => .error message
          | .ok rows => .ok (state, { rows })
  | .join leftName rightName query => do
      let left ← match state.database.findTable? leftName with
        | some table => .ok table
        | none => .error s!"no such table: {leftName}"
      let right ← match state.database.findTable? rightName with
        | some table => .ok table
        | none => .error s!"no such table: {rightName}"
      return (state, { rows := query.evalPlanned left right })
  | .begin =>
      if state.transactionSnapshot.isSome then .error "cannot start a transaction within a transaction"
      else .ok ({ state with transactionSnapshot := some state.database }, {})
  | .commit =>
      if state.transactionSnapshot.isSome then
        .ok ({ state with transactionSnapshot := none }, {})
      else .error "cannot commit - no transaction is active"
  | .rollback =>
      match state.transactionSnapshot with
      | some snapshot => .ok ({ database := snapshot }, {})
      | none => .error "cannot rollback - no transaction is active"

/-- Explicit containment boundary for an *uncertified* effectful traversal.
Certified candidates never call this function.  General or externally-mutated
files may still offer physical candidates without a kernel witness; those are
compared with the verified executor and rejected to the ordinary path on any
disagreement. -/
def executeUncertifiedQueryWithCandidates (state : State) (tableName : String)
    (query : Query) (candidates : List Row) : Except String (State × Result) :=
  match state.database.findTable? tableName with
  | none => .error s!"no such table: {tableName}"
  | some table =>
      let optimized := query.optimize
      let physicalResult := optimized.eval candidates
      let verifiedResult := optimized.eval (table.plannedRows optimized)
      if _same : physicalResult = verifiedResult then
        .ok (state, { rows := physicalResult })
      else execute state (.query tableName query)

theorem executeUncertifiedQueryWithCandidates_eq_execute (state : State)
    (tableName : String) (query : Query) (candidates : List Row) :
    executeUncertifiedQueryWithCandidates state tableName query candidates =
      execute state (.query tableName query) := by
  unfold executeUncertifiedQueryWithCandidates
  cases found : state.database.findTable? tableName with
  | none =>
      simp only [execute, found]
      rfl
  | some table =>
      simp only [found]
      split
      next same =>
        rw [same]
        simp only [execute, found]
        rfl
      next different => rfl

theorem execute_createTable_exact {state next : State} {schema : Schema}
    {result : Result}
    (success : execute state (.createTable schema) = .ok (next, result)) :
    ∃ table,
      emptyTable schema = .ok table ∧
      next.database.tables = table :: state.database.tables ∧
      next.database.findTable? schema.name = some table ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = {} ∧
      ∀ other, other ≠ schema.name →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases created : state.database.createTable schema with
  | error message =>
      simp [created, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | ok database =>
      simp [created, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
      rcases success with ⟨stateEqual, resultEqual⟩
      subst next
      subst result
      rcases Database.createTable_exact created with
        ⟨table, empty, tables⟩
      have tableSchema : table.schema = schema := by
        apply (Table.rebuild_exact (by simpa [emptyTable] using empty)).1
      refine ⟨table, empty, tables, ?_, rfl, rfl, ?_⟩
      · unfold Database.findTable?
        rw [tables]
        simp [tableSchema]
      · intro other different
        unfold Database.findTable?
        rw [tables]
        simp [tableSchema, Ne.symm different]

theorem execute_createIndex_exact {state next : State}
    {tableName : String} {index : Index} {result : Result}
    (success : execute state (.createIndex tableName index) =
      .ok (next, result)) :
    ∃ table replacement,
      state.database.findTable? tableName = some table ∧
      replacement.schema = table.schema ∧
      replacement.indexes = index :: table.indexes ∧
      replacement.rows = table.rows ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = {} ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases modified : state.database.modifyTable tableName
      (fun table => table.addIndex index) with
  | error message =>
      simp [modified, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | ok database =>
      simp [modified, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
      rcases success with ⟨stateEqual, resultEqual⟩
      subst next
      subst result
      rcases Database.modifyTable_exact modified with
        ⟨table, replacement, found, added, updated⟩
      rcases Table.addIndex_exact added with
        ⟨replacementSchema, replacementIndexes, replacementRows⟩
      have replacementName : replacement.schema.name = tableName :=
        (congrArg Schema.name replacementSchema).trans
          (findTable?_some_schemaName found)
      refine ⟨table, replacement, found, replacementSchema,
        replacementIndexes, replacementRows, ?_, rfl, rfl, ?_⟩
      · exact Database.updateTable_target found replacementName updated
      · intro other different
        exact Database.updateTable_frame updated other fun equal =>
          different (equal.trans replacementName)

/-- The exact effect of a successful live `INSERT`.

`freshRowid` and the declared-key freshness are checked by `insertValues` and are
now carried up: an `INSERT` is an insert, not an upsert, and downstream theorems
can say so. `execute_replace_exact` deliberately does *not* carry them, which is
where the two statements differ. -/
theorem execute_insert_exact {state next : State} {tableName : String}
    {values : List Value} {result : Result}
    (success : execute state (.insert tableName values) = .ok (next, result)) :
    ∃ table replacement row,
      state.database.findTable? tableName = some table ∧
      table.createRow values = .ok row ∧
      row.WellFormed table.schema ∧
      (∀ existing ∈ table.rows, existing.rowid.value ≠ row.rowid.value) ∧
      table.findDeclaredPrimary? row = none ∧
      replacement.rows = orderedUpsert row table.rows ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes := 1 } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases inserted : table.insertValues values with
      | error message =>
          simp [found, inserted, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok replacement =>
          cases updated : state.database.updateTable replacement with
          | error message =>
              simp [found, inserted, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok database =>
              simp [found, inserted, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              rcases success with ⟨stateEqual, resultEqual⟩
              subst next
              subst result
              rcases Table.insertValues_exact inserted with
                ⟨row, created, valid, freshRowid, declaredFresh, replacementRows⟩
              have replacementName : replacement.schema.name = tableName :=
                (congrArg Schema.name (Table.insertValues_schema inserted)).trans
                  (findTable?_some_schemaName found)
              refine ⟨table, replacement, row, rfl, created, valid, freshRowid,
                declaredFresh, replacementRows, ?_, rfl, rfl, ?_⟩
              · exact Database.updateTable_target found replacementName updated
              · intro other different
                exact Database.updateTable_frame updated other fun equal =>
                  different (equal.trans replacementName)

theorem execute_replace_exact {state next : State} {tableName : String}
    {values : List Value} {result : Result}
    (success : execute state (.replace tableName values) = .ok (next, result)) :
    ∃ table replacement row,
      state.database.findTable? tableName = some table ∧
      table.createReplacementRow values = .ok row ∧
      replacement.rows = orderedUpsert row table.rows ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes := 1 } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases replaced : table.replaceValues values with
      | error message =>
          simp [found, replaced, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok replacement =>
          cases updated : state.database.updateTable replacement with
          | error message =>
              simp [found, replaced, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok database =>
              simp [found, replaced, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              rcases success with ⟨stateEqual, resultEqual⟩
              subst next
              subst result
              rcases Table.replaceValues_rows replaced with
                ⟨row, created, replacementRows⟩
              have replacementName : replacement.schema.name = tableName :=
                (congrArg Schema.name
                  (Table.replaceValues_schema replaced)).trans
                  (findTable?_some_schemaName found)
              refine ⟨table, replacement, row, rfl, created,
                replacementRows, ?_, rfl, rfl, ?_⟩
              · exact Database.updateTable_target found replacementName updated
              · intro other different
                exact Database.updateTable_frame updated other fun equal =>
                  different (equal.trans replacementName)

theorem execute_deleteWhere_exact {state next : State} {tableName : String}
    {predicate : Option Predicate} {result : Result}
    (success : execute state (.deleteWhere tableName predicate) =
      .ok (next, result)) :
    ∃ table replacement,
      state.database.findTable? tableName = some table ∧
      replacement.rows = table.rows.filter
        (fun row => !selects predicate row) ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes := table.rows.length - replacement.rows.length } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases retained : table.retainRows (fun row => !selects predicate row) with
      | error message =>
          simp [found, retained, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok replacement =>
          cases updated : state.database.updateTable replacement with
          | error message =>
              simp [found, retained, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok database =>
              simp [found, retained, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              rcases success with ⟨stateEqual, resultEqual⟩
              subst next
              subst result
              have replacementName : replacement.schema.name = tableName :=
                (congrArg Schema.name
                  (Table.retainRows_schema retained)).trans
                  (findTable?_some_schemaName found)
              refine ⟨table, replacement, rfl,
                Table.retainRows_exact retained, ?_, rfl, rfl, ?_⟩
              · exact Database.updateTable_target found replacementName updated
              · intro other different
                exact Database.updateTable_frame updated other fun equal =>
                  different (equal.trans replacementName)

theorem execute_updateWhere_exact {state next : State} {tableName : String}
    {assignments : List (Nat × Value)} {predicate : Option Predicate}
    {result : Result}
    (success : execute state (.updateWhere tableName assignments predicate) =
      .ok (next, result)) :
    ∃ table replacement changes,
      state.database.findTable? tableName = some table ∧
      table.updateWhere assignments predicate = .ok (replacement, changes) ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases changed : table.updateWhere assignments predicate with
      | error message =>
          simp [found, changed, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok outcome =>
          rcases outcome with ⟨replacement, changes⟩
          cases updated : state.database.updateTable replacement with
          | error message =>
              simp [found, changed, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok database =>
              simp [found, changed, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              rcases success with ⟨stateEqual, resultEqual⟩
              subst next
              subst result
              have replacementName : replacement.schema.name = tableName :=
                (congrArg Schema.name
                  (Table.updateWhere_schema changed)).trans
                  (findTable?_some_schemaName found)
              refine ⟨table, replacement, changes, rfl, changed, ?_, rfl,
                rfl, ?_⟩
              · exact Database.updateTable_target found replacementName updated
              · intro other different
                exact Database.updateTable_frame updated other fun equal =>
                  different (equal.trans replacementName)

theorem execute_query_exact {state next : State} {tableName : String}
    {query : Query} {result : Result}
    (success : execute state (.query tableName query) = .ok (next, result)) :
    ∃ table, state.database.findTable? tableName = some table ∧
      next = state ∧ result.rows = query.eval table.rows := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      change Except.error _ = Except.ok _ at success
      contradiction
  | some table =>
      simp only [found] at success
      have pairEqual := Except.ok.inj success
      injection pairEqual with stateEqual resultEqual
      subst next
      subst result
      -- The executor now runs the index plan; the observable spec is still the
      -- full scan, and stays true because planning is semantics-preserving.
      have planned := Query.eval_plannedRows table query.optimize
      have resultExact : query.optimize.eval (table.plannedRows query.optimize) =
          query.eval table.rows := by
        calc
          _ = query.optimize.eval table.rows := planned
          _ = query.eval table.rows := Query.eval_optimize query table.rows
      exact ⟨table, rfl, rfl, resultExact⟩

theorem execute_count_exact {state next : State} {tableName : String}
    {target : CountTarget} {predicate : Option Predicate} {result : Result}
    (success : execute state (.count tableName target predicate) = .ok (next, result)) :
    ∃ table count,
      state.database.findTable? tableName = some table ∧
      countInteger (countRows target predicate table.rows) = .ok count ∧
      next = state ∧ result.rows = [[.integer count]] ∧
      count.value = Int.ofNat (countRows target predicate table.rows) := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      change Except.error _ = Except.ok _ at success
      contradiction
  | some table =>
      simp only [found] at success
      cases counted : countInteger (countRows target predicate table.rows) with
      | error message =>
          simp [counted] at success
      | ok count =>
          simp [counted] at success
          rcases success with ⟨stateEqual, resultEqual⟩
          subst next
          subst result
          exact ⟨table, count, rfl, counted, rfl, rfl,
            countInteger_exact counted⟩

theorem execute_group_exact {state next : State} {tableName : String}
    {query : GroupQuery} {result : Result}
    (success : execute state (.group tableName query) = .ok (next, result)) :
    ∃ table, state.database.findTable? tableName = some table ∧
      query.eval table.rows = .ok result.rows ∧ next = state := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      contradiction
  | some table =>
      simp only [found] at success
      cases evaluated : query.eval table.rows with
      | error message => simp [evaluated] at success
      | ok rows =>
          simp [evaluated] at success
          rcases success with ⟨stateEqual, resultEqual⟩
          subst next
          subst result
          exact ⟨table, rfl, evaluated, rfl⟩

theorem execute_sum_exact {state next : State} {tableName : String}
    {column : Nat} {predicate : Option Predicate} {result : Result}
    (success : execute state (.sum tableName column predicate) = .ok (next, result)) :
    ∃ table value, state.database.findTable? tableName = some table ∧
      sumColumn column (table.rows.filter (selects predicate)) = .ok value ∧
      next = state ∧ result.rows = [[value]] := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      contradiction
  | some table =>
      simp only [found] at success
      cases summed : sumColumn column (table.rows.filter (selects predicate)) with
      | error message => simp [summed] at success
      | ok value =>
          simp [summed] at success
          rcases success with ⟨stateEqual, resultEqual⟩
          subst next
          subst result
          exact ⟨table, value, rfl, summed, rfl, rfl⟩

theorem execute_extreme_exact {state next : State} {tableName : String}
    {minimum : Bool} {column : Nat} {predicate : Option Predicate}
    {result : Result}
    (success : execute state (.extreme tableName minimum column predicate) =
      .ok (next, result)) :
    ∃ table, state.database.findTable? tableName = some table ∧
      next = state ∧ result.rows = [[extremeColumn minimum column
        (table.rows.filter (selects predicate))]] := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      contradiction
  | some table =>
      simp [found] at success
      rcases success with ⟨stateEqual, resultEqual⟩
      subst next
      subst result
      exact ⟨table, rfl, rfl, rfl⟩

theorem execute_join_exact {state next : State} {leftName rightName : String}
    {query : CoreJoin.Query} {result : Result}
    (success : execute state (.join leftName rightName query) = .ok (next, result)) :
    ∃ left right, state.database.findTable? leftName = some left ∧
      state.database.findTable? rightName = some right ∧ next = state ∧
      result.rows = query.eval left.rows right.rows := by
  simp only [execute] at success
  cases leftFound : state.database.findTable? leftName with
  | none =>
      rw [leftFound] at success
      change Except.error _ = Except.ok _ at success
      contradiction
  | some left =>
      simp only [leftFound, Option.bind_eq_bind, Option.bind] at success
      cases rightFound : state.database.findTable? rightName with
      | none =>
          rw [rightFound] at success
          change Except.error _ = Except.ok _ at success
          contradiction
      | some right =>
        simp only [rightFound] at success
        have pairEqual := Except.ok.inj success
        injection pairEqual with stateEqual resultEqual
        subst next
        subst result
        exact ⟨left, right, rfl, rfl, rfl, query.evalPlanned_eq_eval left right⟩

theorem execute_commit_exact {state next : State} {result : Result}
    (success : execute state .commit = .ok (next, result)) :
    state.transactionSnapshot.isSome = true ∧
      next.database = state.database ∧
      next.transactionSnapshot = none ∧ result = {} ∧
      ∀ tableName,
        next.database.findTable? tableName =
          state.database.findTable? tableName := by
  unfold execute at success
  cases snapshot : state.transactionSnapshot with
  | none => simp [snapshot] at success
  | some database =>
      simp [snapshot] at success
      rcases success with ⟨stateEqual, resultEqual⟩
      subst next
      subst result
      exact ⟨by simp [snapshot], rfl, rfl, rfl, fun _ => rfl⟩

theorem execute_rollback_restores {state next : State} {result : Result}
    (success : execute state .rollback = .ok (next, result)) :
    next.database = state.transactionSnapshot.getD state.database := by
  unfold execute at success
  cases snapshot : state.transactionSnapshot with
  | none => simp [snapshot] at success
  | some database =>
      simp only [snapshot] at success
      have pairEqual := Except.ok.inj success
      have databaseEqual := congrArg (fun pair => pair.1.database) pairEqual
      simp only at databaseEqual
      rw [← databaseEqual]
      simp [snapshot]

end Core
end SQLeanite
