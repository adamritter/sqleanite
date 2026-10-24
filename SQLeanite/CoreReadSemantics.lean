import SQLeanite.CoreOptimizerBridge
import SQLeanite.RelationalAlgebra

namespace SQLeanite
namespace CoreReadSemantics

open QuerySemantics

/-!
# Live Core reads and multiplicity semantics

This module is deliberately compositional.  It does not define another query
evaluator.  It connects the live `Core.execute` results to the independently
defined `KRelation` bag algebra, while retaining list equality for SQLite's
observable `ORDER BY`/`LIMIT` suffix.
-/

def coreRow (row : Core.Row) : QuerySemantics.Row := .values row.values

def tableFilterPlan (tableName : String)
    (predicate : Option Core.Predicate) : QuerySemantics.Plan :=
  match predicate with
  | none => .table tableName
  | some predicate =>
      .filter (CoreOptimizerBridge.toSemantics predicate) (.table tableName)

private theorem whereRows_coreRows (predicate : Core.Predicate)
    (rows : List Core.Row) :
    QuerySemantics.whereRows (CoreOptimizerBridge.toSemantics predicate)
        (rows.map coreRow) =
      (rows.filter (Core.selects (some predicate))).map coreRow := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      have tail :
          (rows.map coreRow).filter (fun candidate =>
              (CoreOptimizerBridge.toSemantics predicate).eval candidate ==
                .true) =
            (rows.filter (Core.selects (some predicate))).map coreRow := by
        simpa [QuerySemantics.whereRows] using induction
      have headEval :
          (CoreOptimizerBridge.toSemantics predicate).eval (coreRow row) =
            predicate.eval row := by
        simpa [coreRow] using
          CoreOptimizerBridge.toSemantics_eval predicate row
      simp only [List.map_cons, QuerySemantics.whereRows, List.filter_cons]
      rw [headEval]
      cases evaluated : predicate.eval row <;>
        simp [Core.selects, evaluated, coreRow, tail]

theorem tableFilterPlan_eval {database : Core.Database} {tableName : String}
    {table : Core.Table} (found : database.findTable? tableName = some table)
    (predicate : Option Core.Predicate) :
    QuerySemantics.evalPlan database (tableFilterPlan tableName predicate) =
      (table.rows.filter (Core.selects predicate)).map coreRow := by
  cases predicate with
  | none =>
      simp only [tableFilterPlan, QuerySemantics.evalPlan,
        QuerySemantics.tableRows, found]
      rw [show table.rows.filter (Core.selects none) = table.rows by
        simp [Core.selects]]
      rfl
  | some predicate =>
      simp only [tableFilterPlan, QuerySemantics.evalPlan,
        QuerySemantics.tableRows, found]
      exact whereRows_coreRows predicate table.rows

/-- The unordered relational prefix of every live single-table query. -/
theorem optimize_tableFilterPlan_eval {database : Core.Database}
    {tableName : String} {table : Core.Table}
    (found : database.findTable? tableName = some table)
    (predicate : Option Core.Predicate) :
    QuerySemantics.evalPlan database
        (QuerySemantics.optimizePlan (tableFilterPlan tableName predicate)) =
      (table.rows.filter (Core.selects predicate)).map coreRow := by
  rw [QuerySemantics.optimizePlan_eval]
  exact tableFilterPlan_eval found predicate

/-- LIMIT restricts a duplicate-free bag to a prefix of its explicit ordered
presentation. Ordering remains an input to this bag-level operation. -/
def orderedLimit {α : Type} [DecidableEq α] (order : List α) (limit : Option Nat)
    (relation : KRelation.Relation α) : KRelation.Relation α :=
  match limit with
  | none => relation
  | some n => KRelation.select
      (fun row => if row ∈ order.take n then .true else .false) relation

theorem ofList_limitRows {α : Type} [DecidableEq α] (rows : List α) (limit : Option Nat)
    (nodup : rows.Nodup) :
    RelationalAlgebra.ofList (Core.limitRows limit rows) =
      orderedLimit rows limit (RelationalAlgebra.ofList rows) := by
  cases limit with
  | none => rfl
  | some n =>
      funext row
      simp only [Core.limitRows, orderedLimit, KRelation.select, RelationalAlgebra.ofList,
        RelationalAlgebra.listMultiplicity_eq_count]
      rw [List.Nodup.count (nodup.take), List.Nodup.count nodup]
      by_cases member : row ∈ rows.take n
      · have original : row ∈ rows := List.mem_of_mem_take member
        simp [member, original]
      · simp [member]

theorem ofList_stableDeduplicate {α : Type} [DecidableEq α] (rows : List α) :
    RelationalAlgebra.ofList (Core.stableDeduplicate rows) =
      KRelation.distinct (RelationalAlgebra.ofList rows) := by
  calc
    RelationalAlgebra.ofList (Core.stableDeduplicate rows) =
        RelationalAlgebra.ofList (Core.deduplicate rows.reverse) :=
      RelationalAlgebra.ofList_perm (List.reverse_perm _)
    _ = KRelation.distinct (RelationalAlgebra.ofList rows.reverse) :=
      RelationalAlgebra.ofList_deduplicate _
    _ = KRelation.distinct (RelationalAlgebra.ofList rows) :=
      congrArg KRelation.distinct (RelationalAlgebra.ofList_perm (List.reverse_perm _))

/-- Bag denotation of the live query after its order/limit presentation step.
The finite support is deduplicated, so projection sums each source value once
and preserves its original multiplicity. -/
def queryDenotation (query : Core.Query) (rows : List Core.Row) :
    KRelation.Relation (List Core.Value) :=
  let selected := query.selectedRows rows
  let projected := KRelation.project
    (RelationalAlgebra.supportDomain selected).values
    (fun row => query.columns.map row.value)
    (RelationalAlgebra.ofList selected)
  if query.distinct then
    orderedLimit (Core.stableDeduplicate (query.projectedRows rows)) query.limit
      (KRelation.distinct projected)
  else projected

theorem query_eval_denotes (query : Core.Query) (rows : List Core.Row) :
    RelationalAlgebra.ofList (query.eval rows) =
      queryDenotation query rows := by
  unfold Core.Query.eval Core.Query.projectedRows queryDenotation
  split
  next enabled =>
    rw [ofList_limitRows _ _ (Core.stableDeduplicate_nodup _), ofList_stableDeduplicate]
    rw [← RelationalAlgebra.project_ofList]
    rfl
  next disabled =>
    rw [← RelationalAlgebra.project_ofList]

theorem execute_query_denotes {state next : Core.State} {tableName : String}
    {query : Core.Query} {result : Core.Result}
    (success : Core.execute state (.query tableName query) = .ok (next, result)) :
    ∃ table, state.database.findTable? tableName = some table ∧
      next = state ∧
      RelationalAlgebra.ofList result.rows =
        queryDenotation query table.rows := by
  rcases Core.execute_query_exact success with ⟨table, found, unchanged, rows⟩
  refine ⟨table, found, unchanged, ?_⟩
  rw [rows, query_eval_denotes]

def joinPlan (query : CoreJoin.Query) (left right : List Core.Row) :
    QuerySemantics.Plan :=
  match query.kind with
  | .inner => CoreOptimizerBridge.innerJoinPlan query.on query.where_ left right
  | .left => CoreOptimizerBridge.leftOuterJoinPlan query.on query.where_
      query.rightWidth left right

def joinSelectedPrefix (query : CoreJoin.Query) (left right : List Core.Row) :
    List CoreJoin.JoinedRow :=
  match query.kind with
  | .inner => CoreJoin.matchingRows query.on query.where_
      (CoreJoin.crossRows left right)
  | .left =>
      (CoreJoin.leftOuterRows query.on query.rightWidth left right).filter
        (CoreJoin.selects query.where_)

/-- Inner and left-outer joins both refine the typed relational algebra before
the explicitly order-sensitive `ORDER BY`/`LIMIT` suffix is applied. -/
theorem optimize_joinPlan_eval (database : Core.Database)
    (query : CoreJoin.Query) (left right : List Core.Row) :
    QuerySemantics.evalPlan database
        (QuerySemantics.optimizePlan (joinPlan query left right)) =
      (joinSelectedPrefix query left right).map
        CoreOptimizerBridge.joinedRow := by
  cases query with
  | mk columns on kind rightWidth where_ orderBy limit =>
      cases kind with
      | inner =>
          simpa [joinPlan, joinSelectedPrefix] using
            CoreOptimizerBridge.optimize_innerJoinPlan_eval database on
              where_ left right
      | left =>
          simpa [joinPlan, joinSelectedPrefix] using
            CoreOptimizerBridge.optimize_leftOuterJoinPlan_eval database on
              where_ rightWidth left right

def joinDenotation (query : CoreJoin.Query)
    (left right : List Core.Row) : KRelation.Relation (List Core.Value) :=
  let selected := query.selectedRows left right
  KRelation.project (RelationalAlgebra.supportDomain selected).values
    (CoreJoin.projectRow query.columns) (RelationalAlgebra.ofList selected)

theorem join_eval_denotes (query : CoreJoin.Query)
    (left right : List Core.Row) :
    RelationalAlgebra.ofList (query.eval left right) =
      joinDenotation query left right := by
  unfold CoreJoin.Query.eval joinDenotation
  rw [← RelationalAlgebra.project_ofList]

theorem execute_join_denotes {state next : Core.State}
    {leftName rightName : String} {query : CoreJoin.Query}
    {result : Core.Result}
    (success : Core.execute state (.join leftName rightName query) =
      .ok (next, result)) :
    ∃ left right,
      state.database.findTable? leftName = some left ∧
      state.database.findTable? rightName = some right ∧
      next = state ∧
      RelationalAlgebra.ofList result.rows =
        joinDenotation query left.rows right.rows := by
  rcases Core.execute_join_exact success with
    ⟨left, right, leftFound, rightFound, unchanged, rows⟩
  refine ⟨left, right, leftFound, rightFound, unchanged, ?_⟩
  rw [rows, join_eval_denotes]

/-- Successful grouped execution carries the existing output-by-output
refinement to COUNT, SUM, MIN and MAX denotations. -/
theorem execute_group_denotes {state next : Core.State} {tableName : String}
    {query : Core.GroupQuery} {result : Core.Result}
    (success : Core.execute state (.group tableName query) = .ok (next, result)) :
    ∃ table,
      state.database.findTable? tableName = some table ∧
      next = state ∧
      RelationalAlgebra.Aligned (fun group output =>
        RelationalAlgebra.Aligned
          (RelationalAlgebra.coreGroupOutputRefines query table.rows group)
          query.outputs output)
        (query.groupKeys table.rows) result.rows := by
  rcases Core.execute_group_exact success with
    ⟨table, found, evaluated, unchanged⟩
  exact ⟨table, found, unchanged,
    RelationalAlgebra.coreGroup_eval_refines query table.rows result.rows
      evaluated⟩

theorem execute_count_denotes {state next : Core.State} {tableName : String}
    {target : Core.CountTarget} {predicate : Option Core.Predicate}
    {result : Core.Result}
    (success : Core.execute state (.count tableName target predicate) =
      .ok (next, result)) :
    ∃ table count,
      state.database.findTable? tableName = some table ∧
      next = state ∧ result.rows = [[.integer count]] ∧
      count.value = Int.ofNat (Core.countRows target predicate table.rows) := by
  rcases Core.execute_count_exact success with
    ⟨table, count, found, _, unchanged, rows, exactCount⟩
  exact ⟨table, count, found, unchanged, rows, exactCount⟩

theorem execute_sum_denotes {state next : Core.State} {tableName : String}
    {column : Nat} {predicate : Option Core.Predicate} {result : Core.Result}
    (success : Core.execute state (.sum tableName column predicate) =
      .ok (next, result)) :
    ∃ table value,
      state.database.findTable? tableName = some table ∧
      Core.sumColumn column (table.rows.filter (Core.selects predicate)) =
        .ok value ∧ next = state ∧ result.rows = [[value]] := by
  exact Core.execute_sum_exact success

theorem execute_extreme_denotes {state next : Core.State} {tableName : String}
    {minimum : Bool} {column : Nat} {predicate : Option Core.Predicate}
    {result : Core.Result}
    (success : Core.execute state (.extreme tableName minimum column predicate) =
      .ok (next, result)) :
    ∃ table, state.database.findTable? tableName = some table ∧
      next = state ∧
      result.rows = [[Core.extremeColumn minimum column
        (table.rows.filter (Core.selects predicate))]] := by
  exact Core.execute_extreme_exact success

/-- Every compound operator used by `CoreSQL` has the independent optimized
bag-plan denotation already proved by the bridge. -/
theorem compound_denotes (database : Core.Database) (operation : CompoundOp)
    (left right : List (List Core.Value)) :
    QuerySemantics.evalPlan database
        (QuerySemantics.optimizePlan
          (CoreOptimizerBridge.compoundPlan operation left right)) =
      (CoreOptimizerBridge.compoundRows operation left right).map
        CoreOptimizerBridge.compoundRow :=
  CoreOptimizerBridge.optimize_compoundPlan_eval database operation left right

/-! ## POPL'10 permutation parity, on the live read path

`RelationalAlgebra.permute_eval` and `permute_symm_eval` establish that the
algebra has POPL'10's permutation operator. On their own they say nothing about
the shipped executor: they are theorems about a standalone module that the live
read path never mentions.

What follows closes that. A live `Core.Query` projects by a list of column
indices; reordering that list is a column permutation. These lemmas prove the
reordered live projection *is* `RelationalAlgebra.permute` applied to the
unreordered one, on the denotation both are observed through -- so the parity
claim becomes a claim about `Core.execute`.
-/

/-- Total positional read. `Value.null` for an out-of-range index keeps the
reindexing functions total without a bounds proof at every use. -/
def valueAt (values : List Core.Value) (index : Nat) : Core.Value :=
  (values[index]?).getD .null

/-- Reorder a projected tuple by `positions`. Tuples of the wrong width are
returned unchanged, which is what makes this a total bijection rather than a
partial one: the identity branch is its own inverse. -/
def reorderValues (positions : List Nat) (values : List Core.Value) :
    List Core.Value :=
  if values.length = positions.length then positions.map (valueAt values)
  else values

/-- The inverse reindexing: position `k` of the result reads whichever slot of
the input `positions` sent to `k`. -/
def invertPositions (positions : List Nat) : List Nat :=
  (List.range positions.length).map (fun target => positions.idxOf target)

theorem invertPositions_length (positions : List Nat) :
    (invertPositions positions).length = positions.length := by
  simp [invertPositions]

private theorem getElem?_idxOf_of_mem :
    ∀ {values : List Nat} {target : Nat}, target ∈ values →
      values[values.idxOf target]? = some target
  | [], _, member => absurd member (by simp)
  | head :: tail, target, member => by
      rw [List.idxOf, List.findIdx_cons]
      by_cases hit : (head == target) = true
      · have equal : head = target := by simpa using hit
        simp [hit, equal]
      · have different : head ≠ target := by
          intro equal
          exact hit (by simp [equal])
        have inTail : target ∈ tail := by
          rcases List.mem_cons.mp member with equal | tail?
          · exact absurd equal.symm different
          · exact tail?
        have recursive := getElem?_idxOf_of_mem inTail
        simpa [hit, List.idxOf] using recursive

private theorem idxOf_eq_of_getElem? {values : List Nat} (nodup : values.Nodup) :
    ∀ {index target : Nat}, values[index]? = some target →
      values.idxOf target = index := by
  induction values with
  | nil => intro index target found; simp at found
  | cons head tail induction =>
      intro index target found
      cases index with
      | zero =>
          have equal : head = target := by simpa using found
          simp [List.idxOf, List.findIdx_cons, equal]
      | succ index =>
          have inTail : tail[index]? = some target := by simpa using found
          have member : target ∈ tail := List.mem_of_getElem? inTail
          have different : (head == target) = false := by
            have notMember := (List.nodup_cons.mp nodup).1
            have : head ≠ target := fun equal => notMember (equal ▸ member)
            simpa using this
          have recursive := induction (List.nodup_cons.mp nodup).2 inTail
          rw [List.idxOf, List.findIdx_cons, different]
          simpa [List.idxOf] using recursive

private theorem reorderValues_getElem? {positions : List Nat}
    {values : List Core.Value} (width : values.length = positions.length)
    {index slot : Nat} (found : positions[index]? = some slot) :
    (reorderValues positions values)[index]? = some (valueAt values slot) := by
  rw [reorderValues, if_pos width, List.getElem?_map, found]
  rfl

private theorem reorderValues_length_of_width {positions : List Nat}
    {values : List Core.Value} (width : values.length = positions.length) :
    (reorderValues positions values).length = positions.length := by
  rw [reorderValues, if_pos width, List.length_map]

/-- Every slot named by a permutation of `range positions.length` is in range. -/
private theorem lt_of_mem_positions {positions : List Nat}
    (perm : positions.Perm (List.range positions.length)) {slot : Nat}
    (member : slot ∈ positions) : slot < positions.length := by
  have inRange : slot ∈ List.range positions.length := perm.mem_iff.mp member
  simpa using inRange

private theorem invertPositions_getElem? {positions : List Nat}
    {slot : Nat} (bounded : slot < positions.length) :
    (invertPositions positions)[slot]? = some (positions.idxOf slot) := by
  rw [invertPositions, List.getElem?_map, List.getElem?_range bounded]
  rfl

/-- Reordering by a permutation and by its inverse is the identity on every
tuple, including the wrong-width tuples the identity branch returns. -/
theorem reorderValues_invert {positions : List Nat}
    (perm : positions.Perm (List.range positions.length))
    (values : List Core.Value) :
    reorderValues (invertPositions positions) (reorderValues positions values) =
      values := by
  by_cases width : values.length = positions.length
  · have nodup : positions.Nodup :=
      perm.nodup_iff.mpr (List.nodup_range)
    have innerLength := reorderValues_length_of_width (positions := positions)
      (values := values) width
    have outerWidth :
        (reorderValues positions values).length =
          (invertPositions positions).length := by
      rw [innerLength, invertPositions_length]
    apply List.ext_getElem?
    intro index
    by_cases bounded : index < positions.length
    · have slotFound : (invertPositions positions)[index]? =
          some (positions.idxOf index) := invertPositions_getElem? bounded
      have member : index ∈ positions := by
        have : index ∈ List.range positions.length := by simpa using bounded
        exact perm.mem_iff.mpr this
      have inner := reorderValues_getElem? (positions := positions)
        (values := values) width (getElem?_idxOf_of_mem member)
      rw [reorderValues_getElem? (positions := invertPositions positions)
        (values := reorderValues positions values) outerWidth slotFound]
      rw [valueAt, inner]
      have bound : index < values.length := by rw [width]; exact bounded
      simp only [Option.getD_some, valueAt, List.getElem?_eq_getElem bound]
    · have beyondLeft :
          (reorderValues (invertPositions positions)
            (reorderValues positions values))[index]? = none := by
        apply List.getElem?_eq_none
        rw [reorderValues_length_of_width (positions := invertPositions positions)
          (values := reorderValues positions values) outerWidth,
          invertPositions_length]
        omega
      have beyondRight : values[index]? = none := by
        apply List.getElem?_eq_none
        rw [width]
        omega
      rw [beyondLeft, beyondRight]
  · have identity : reorderValues positions values = values := by
      rw [reorderValues, if_neg width]
    rw [identity, reorderValues, if_neg (by rw [invertPositions_length]; exact width)]

theorem reorderValues_invert_symm {positions : List Nat}
    (perm : positions.Perm (List.range positions.length))
    (values : List Core.Value) :
    reorderValues positions (reorderValues (invertPositions positions) values) =
      values := by
  by_cases width : values.length = positions.length
  · have nodup : positions.Nodup := perm.nodup_iff.mpr (List.nodup_range)
    have innerWidth : values.length = (invertPositions positions).length := by
      rw [invertPositions_length]; exact width
    have innerLength :=
      reorderValues_length_of_width (positions := invertPositions positions)
        (values := values) innerWidth
    have outerWidth :
        (reorderValues (invertPositions positions) values).length =
          positions.length := by
      rw [innerLength, invertPositions_length]
    apply List.ext_getElem?
    intro index
    by_cases bounded : index < positions.length
    · have slotFound : positions[index]? = some positions[index] :=
        List.getElem?_eq_getElem bounded
      have slotBounded : positions[index] < positions.length :=
        lt_of_mem_positions perm (List.getElem_mem bounded)
      have inner := reorderValues_getElem?
        (positions := invertPositions positions) (values := values) innerWidth
        (invertPositions_getElem? slotBounded)
      rw [reorderValues_getElem? (positions := positions)
        (values := reorderValues (invertPositions positions) values)
        outerWidth slotFound]
      rw [valueAt, inner]
      have recovered : positions.idxOf positions[index] = index :=
        idxOf_eq_of_getElem? nodup slotFound
      rw [recovered, valueAt]
      have : index < values.length := by rw [width]; exact bounded
      rw [List.getElem?_eq_getElem this]
      rfl
    · have beyondLeft :
          (reorderValues positions
            (reorderValues (invertPositions positions) values))[index]? = none := by
        apply List.getElem?_eq_none
        rw [reorderValues_length_of_width (positions := positions)
          (values := reorderValues (invertPositions positions) values) outerWidth]
        omega
      have beyondRight : values[index]? = none := by
        apply List.getElem?_eq_none
        rw [width]
        omega
      rw [beyondLeft, beyondRight]
  · have identity : reorderValues (invertPositions positions) values = values := by
      rw [reorderValues, if_neg (by rw [invertPositions_length]; exact width)]
    rw [identity, reorderValues, if_neg width]

/-- A permutation of `range columns.length` is a permutation of
`range positions.length`, because permutations preserve length.  Stated
separately so the bijection below can be built from the permutation a caller
naturally has: one against the *source* column list. -/
private theorem perm_range_self {positions columns : List Nat}
    (perm : positions.Perm (List.range columns.length)) :
    positions.Perm (List.range positions.length) := by
  have lengths : positions.length = columns.length := by
    simpa using perm.length_eq
  rw [lengths]
  exact perm

/-- A column permutation of the live projection, as an algebra `Bijection` on
output tuples. -/
def columnBijection {positions columns : List Nat}
    (perm : positions.Perm (List.range columns.length)) :
    RelationalAlgebra.Bijection (List Core.Value) (List Core.Value) where
  forward := reorderValues positions
  backward := reorderValues (invertPositions positions)
  leftInverse := reorderValues_invert (perm_range_self perm)
  rightInverse := reorderValues_invert_symm (perm_range_self perm)

theorem columnBijection_forward {positions columns : List Nat}
    (perm : positions.Perm (List.range columns.length)) :
    (columnBijection perm).forward = reorderValues positions := rfl

/-- The permuted column list projects to the reordered tuple. This is the step
that ties a *syntactic* column reordering to the tuple-level permutation. -/
theorem permutedColumns_map_value {columns positions : List Nat}
    (perm : positions.Perm (List.range columns.length))
    (row : Core.Row) :
    (positions.map (fun index => columns.getD index 0)).map row.value =
      reorderValues positions (columns.map row.value) := by
  have lengths : positions.length = columns.length := by
    have := perm.length_eq
    simpa using this
  have width : (columns.map row.value).length = positions.length := by
    rw [List.length_map, lengths]
  rw [reorderValues, if_pos width, List.map_map]
  apply List.map_congr_left
  intro index member
  have bounded : index < columns.length := by
    have inRange : index ∈ List.range columns.length := perm.mem_iff.mp member
    simpa using inRange
  have found : columns[index]? = some columns[index] :=
    List.getElem?_eq_getElem bounded
  have projected : (columns.map row.value)[index]? =
      some (row.value columns[index]) := by
    rw [List.getElem?_map, found]
    rfl
  show row.value (columns.getD index 0) = valueAt (columns.map row.value) index
  rw [valueAt, projected, List.getD_eq_getElem?_getD, found]
  rfl

/-- **POPL'10 permutation parity, reached from the live executor.**

Permuting a live query's column list denotes exactly `RelationalAlgebra.permute`
of the unpermuted query's denotation. Both `DISTINCT` and non-`DISTINCT` queries
are covered: duplicate elimination commutes with a bijective relabelling.

This is the theorem that upgrades "the algebra module has a permutation
operator" to "the projection the shipped read path performs *is* that operator".
-/
theorem permuted_projection_denotes (query : Core.Query) {positions : List Nat}
    (perm : positions.Perm (List.range query.columns.length))
    (rows : List Core.Row) :
    queryDenotation
        { query with
          columns := positions.map (fun index => query.columns.getD index 0) }
        rows =
      RelationalAlgebra.eval
        (RelationalAlgebra.permute (columnBijection perm)
          (.relation (queryDenotation query rows))) := by
  rw [← query_eval_denotes, ← query_eval_denotes]
  have projected :
      Core.Query.projectedRows
          { query with
            columns := positions.map (fun index => query.columns.getD index 0) }
          rows =
        (query.projectedRows rows).map (reorderValues positions) := by
    unfold Core.Query.projectedRows Core.Query.selectedRows
    rw [List.map_map]
    apply List.map_congr_left
    intro row _
    simpa [Function.comp_def] using permutedColumns_map_value perm row
  -- The permuted query differs from the original in `columns` only, so the two
  -- `distinct` flags and the two selected-row lists are literally the same.
  have samePermuted :
      Core.Query.eval
          { query with
            columns := positions.map (fun index => query.columns.getD index 0) }
          rows =
        if query.distinct then
          Core.limitRows query.limit (Core.stableDeduplicate ((query.projectedRows rows).map
            (reorderValues positions)))
        else (query.projectedRows rows).map (reorderValues positions) := by
    unfold Core.Query.eval
    rw [projected]
  rw [samePermuted, Core.Query.eval]
  cases flag : query.distinct with
  | true =>
      simp only [flag, if_true]
      have injective : Function.Injective (columnBijection perm).forward := by
        intro a b equal
        have recovered := congrArg (columnBijection perm).backward equal
        simpa only [(columnBijection perm).leftInverse] using recovered
      rw [← columnBijection_forward perm,
        Core.stableDeduplicate_map_injective _ injective, Core.limitRows_map]
      exact RelationalAlgebra.ofList_map_permute (columnBijection perm)
        (Core.limitRows query.limit (Core.stableDeduplicate (query.projectedRows rows)))
  | false =>
      simp only [flag, if_false, Bool.false_eq_true]
      rw [← columnBijection_forward perm]
      exact RelationalAlgebra.ofList_map_permute (columnBijection perm)
        (query.projectedRows rows)

end CoreReadSemantics
end SQLeanite
