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
  if query.distinct then KRelation.distinct projected else projected

theorem query_eval_denotes (query : Core.Query) (rows : List Core.Row) :
    RelationalAlgebra.ofList (query.eval rows) =
      queryDenotation query rows := by
  unfold Core.Query.eval Core.Query.projectedRows queryDenotation
  split
  next enabled =>
    rw [RelationalAlgebra.ofList_deduplicate]
    rw [← RelationalAlgebra.project_ofList]
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

end CoreReadSemantics
end SQLeanite
