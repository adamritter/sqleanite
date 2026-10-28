import SQLeanite.CoreJoin.FilterMappedRightLeftOnly
import SQLeanite.Optimizer

namespace SQLeanite
namespace CoreOptimizerBridge
open QuerySemantics

/-- Exact embedding of every live Core predicate into the denotational SQL
semantics. No value conversion occurs: both sides use the same bounded physical
value type and the same three-valued comparison functions. -/
def toSemantics : Core.Predicate → QuerySemantics.Predicate
  | .equal column value => .equals (.cell column) value
  | .notEqual column value => .notEquals (.cell column) value
  | .compare operation column value => .compare operation (.cell column) value
  | .isNull column => .isNull (.cell column)
  | .not predicate => .not (toSemantics predicate)
  | .and left right => .and (toSemantics left) (toSemantics right)
  | .or left right => .or (toSemantics left) (toSemantics right)

/-- Partial projection is intentional: join-scoped and constant predicates do
not exist in `Core.Predicate`. Plans originating in the Core are proved to
remain in this image. -/
def fromSemantics? : QuerySemantics.Predicate → Option Core.Predicate
  | .equals (.cell column) value => some (.equal column value)
  | .notEquals (.cell column) value => some (.notEqual column value)
  | .compare operation (.cell column) value => some (.compare operation column value)
  | .isNull (.cell column) => some (.isNull column)
  | .not predicate => return .not (← fromSemantics? predicate)
  | .and left right => return .and (← fromSemantics? left) (← fromSemantics? right)
  | .or left right => return .or (← fromSemantics? left) (← fromSemantics? right)
  | _ => none

theorem fromSemantics_toSemantics (predicate : Core.Predicate) :
    fromSemantics? (toSemantics predicate) = some predicate := by
  induction predicate <;> simp_all [toSemantics, fromSemantics?]

theorem toSemantics_eval (predicate : Core.Predicate) (row : Core.Row) :
    (toSemantics predicate).eval (.values row.values) = predicate.eval row := by
  induction predicate <;>
    simp_all [toSemantics, QuerySemantics.Predicate.eval,
      QuerySemantics.Row.lookup, Core.Predicate.eval, Core.Row.value,
      QuerySemantics.sqlEquals] <;> rfl

private theorem foldNot_toSemantics (predicate : Core.Predicate) :
    QuerySemantics.foldNot (toSemantics predicate) =
      .not (toSemantics predicate) := by
  cases predicate <;> rfl

private theorem foldAnd_toSemantics (left right : Core.Predicate) :
    QuerySemantics.foldAnd (toSemantics left) (toSemantics right) =
      .and (toSemantics left) (toSemantics right) := by
  cases left <;> cases right <;> rfl

private theorem foldOr_toSemantics (left right : Core.Predicate) :
    QuerySemantics.foldOr (toSemantics left) (toSemantics right) =
      .or (toSemantics left) (toSemantics right) := by
  cases left <;> cases right <;> rfl

/-- A single-table Core query represented as a denotational plan. The identity
projection is deliberate: it makes projection elimination part of the actual
pipeline while preserving the Core's separate column projection. -/
def predicatePlan (tableName : String) (predicate : Core.Predicate) : Plan :=
  .project .identity (.filter (toSemantics predicate) (.table tableName))

def extractPredicate? : Plan → Option Core.Predicate
  | .filter predicate (.table _) => fromSemantics? predicate
  | _ => none

/-- Run the bottom-up, proved plan optimizer and project its resulting filter
back into the executable Core predicate language. The fallback is reachable
only for plans outside the image of `predicatePlan`; the theorem below closes
that case for every live Core predicate. -/
def optimizePredicate (tableName : String) (predicate : Core.Predicate) :
    Core.Predicate :=
  (extractPredicate? (QuerySemantics.optimizePlan
    (predicatePlan tableName predicate))).getD predicate

theorem foldConstants_toSemantics (predicate : Core.Predicate) :
    QuerySemantics.foldConstants (toSemantics predicate) =
      toSemantics predicate := by
  induction predicate <;>
    simp_all [toSemantics, QuerySemantics.foldConstants,
      foldNot_toSemantics, foldAnd_toSemantics, foldOr_toSemantics]

theorem optimizePredicate_eq (tableName : String) (predicate : Core.Predicate) :
    optimizePredicate tableName predicate = predicate := by
  simp [optimizePredicate, predicatePlan, QuerySemantics.optimizePlan,
    QuerySemantics.rewriteRoot, QuerySemantics.predicatePushdown,
    QuerySemantics.constantFolding, QuerySemantics.projectionElimination,
    QuerySemantics.filterFusion, QuerySemantics.unionDistribution,
    foldConstants_toSemantics,
    extractPredicate?, fromSemantics_toSemantics]

theorem optimizePredicate_eval (tableName : String)
    (predicate : Core.Predicate) (row : Core.Row) :
    (optimizePredicate tableName predicate).eval row = predicate.eval row := by
  rw [optimizePredicate_eq]

/-- Live query optimizer. Core's recursive 3VL normalization runs first; the
result then traverses the proved denotational plan pipeline. -/
def optimize (tableName : String) (query : Core.Query) : Core.Query :=
  let normalized := query.optimize
  { normalized with
    predicate := (normalized.predicate.map (optimizePredicate tableName)) }

theorem optimize_eq (tableName : String) (query : Core.Query) :
    optimize tableName query = query.optimize := by
  unfold optimize
  generalize query.optimize = optimized
  cases optimized with
  | mk columns predicate orderBy limit distinct =>
      cases predicate <;> simp [optimizePredicate_eq]

theorem optimize_eval (tableName : String) (query : Core.Query)
    (rows : List Core.Row) :
    (optimize tableName query).eval rows = query.eval rows := by
  rw [optimize_eq]
  exact Core.Query.eval_optimize query rows

def joinRow (row : Core.Row) : QuerySemantics.Row :=
  .values row.values

def joinedRow (row : CoreJoin.JoinedRow) : QuerySemantics.Row :=
  .joined (joinRow row.1) (joinRow row.2)

def joinColumnPath (reference : CoreJoin.ColumnRef) : ColumnPath :=
  match reference.side with
  | .left => .left (.cell reference.column)
  | .right => .right (.cell reference.column)

def joinOperand : CoreJoin.Operand → QuerySemantics.Operand
  | .column reference => .column (joinColumnPath reference)
  | .coercedColumn affinity reference => .coercedColumn affinity (joinColumnPath reference)
  | .literal value => .literal value
  | .mergedColumn affinity left right =>
      .mergedColumn affinity (.left (.cell left)) (.right (.cell right))

theorem joinOperand_value (operand : CoreJoin.Operand)
    (row : CoreJoin.JoinedRow) :
    (joinOperand operand).value (joinedRow row) = operand.value row := by
  cases operand with
  | mergedColumn affinity left right =>
      cases row
      cases affinity <;> rfl
  | literal => rfl
  | column reference =>
      cases reference with
      | mk side column =>
          cases side <;> simp [joinOperand, joinColumnPath,
            QuerySemantics.Operand.value, joinedRow, joinRow,
            QuerySemantics.Row.lookup, CoreJoin.Operand.value,
            CoreJoin.ColumnRef.value]
  | coercedColumn affinity reference =>
      cases reference with
      | mk side column =>
          cases side <;> simp [joinOperand, joinColumnPath,
            QuerySemantics.Operand.value, joinedRow, joinRow,
            QuerySemantics.Row.lookup, CoreJoin.Operand.value,
            CoreJoin.ColumnRef.value]

def joinPredicate : CoreJoin.Predicate → QuerySemantics.Predicate
  | .equalCollated kind left right => .operandsEqualCollated kind (joinOperand left) (joinOperand right)
  | .compareCollated kind operation left right =>
      .operandsCompareCollated kind operation (joinOperand left) (joinOperand right)
  | .truthy operand => .operandTruthy (joinOperand operand)
  | .equal left right => .operandsEqual (joinOperand left) (joinOperand right)
  | .notEqual left right =>
      .operandsNotEqual (joinOperand left) (joinOperand right)
  | .compare operation left right =>
      .operandsCompare operation (joinOperand left) (joinOperand right)
  | .isNull operand => .operandIsNull (joinOperand operand)
  | .not predicate => .not (joinPredicate predicate)
  | .and left right => .and (joinPredicate left) (joinPredicate right)
  | .or left right => .or (joinPredicate left) (joinPredicate right)

def fromJoinOperand? : QuerySemantics.Operand → Option CoreJoin.Operand
  | .column (.left (.cell column)) =>
      some (.column ⟨.left, column⟩)
  | .column (.right (.cell column)) =>
      some (.column ⟨.right, column⟩)
  | .coercedColumn affinity (.left (.cell column)) =>
      some (.coercedColumn affinity ⟨.left, column⟩)
  | .coercedColumn affinity (.right (.cell column)) =>
      some (.coercedColumn affinity ⟨.right, column⟩)
  | .literal value => some (.literal value)
  | .mergedColumn affinity (.left (.cell left)) (.right (.cell right)) =>
      some (.mergedColumn affinity left right)
  | _ => none

def fromJoinPredicate? : QuerySemantics.Predicate → Option CoreJoin.Predicate
  | .operandsEqualCollated kind left right =>
      return .equalCollated kind (← fromJoinOperand? left) (← fromJoinOperand? right)
  | .operandsCompareCollated kind operation left right =>
      return .compareCollated kind operation (← fromJoinOperand? left) (← fromJoinOperand? right)
  | .operandTruthy operand => return .truthy (← fromJoinOperand? operand)
  | .operandsEqual left right =>
      return .equal (← fromJoinOperand? left) (← fromJoinOperand? right)
  | .operandsNotEqual left right =>
      return .notEqual (← fromJoinOperand? left) (← fromJoinOperand? right)
  | .operandsCompare operation left right =>
      return .compare operation (← fromJoinOperand? left) (← fromJoinOperand? right)
  | .operandIsNull operand => return .isNull (← fromJoinOperand? operand)
  | .not predicate => return .not (← fromJoinPredicate? predicate)
  | .and left right =>
      return .and (← fromJoinPredicate? left) (← fromJoinPredicate? right)
  | .or left right =>
      return .or (← fromJoinPredicate? left) (← fromJoinPredicate? right)
  | _ => none

theorem fromJoinOperand_joinOperand (operand : CoreJoin.Operand) :
    fromJoinOperand? (joinOperand operand) = some operand := by
  cases operand with
  | mergedColumn => rfl
  | literal => rfl
  | column reference =>
      cases reference with
      | mk side column => cases side <;> rfl
  | coercedColumn affinity reference =>
      cases reference with
      | mk side column => cases side <;> rfl

theorem fromJoinPredicate_joinPredicate (predicate : CoreJoin.Predicate) :
    fromJoinPredicate? (joinPredicate predicate) = some predicate := by
  induction predicate <;>
    simp_all [joinPredicate, fromJoinPredicate?, fromJoinOperand_joinOperand]

theorem joinPredicate_eval (predicate : CoreJoin.Predicate)
    (row : CoreJoin.JoinedRow) :
    (joinPredicate predicate).eval (joinedRow row) = predicate.eval row := by
  induction predicate <;>
    simp_all [joinPredicate, QuerySemantics.Predicate.eval,
      QuerySemantics.sqlEquals, QuerySemantics.valueTruth, CoreJoin.Predicate.eval, joinOperand_value]

/-- SQL `ON` and post-join `WHERE` are both selection conditions for an inner
join. `TRUE` is the identity when either optional clause is absent. -/
def combinedJoinPredicate (on where_ : Option CoreJoin.Predicate) :
    QuerySemantics.Predicate :=
  match on, where_ with
  | none, none => .constant .true
  | some predicate, none | none, some predicate => joinPredicate predicate
  | some on, some where_ => .and (joinPredicate on) (joinPredicate where_)

private theorem truth_beq_true (truth : Truth) :
    (truth == .true) = decide (truth = .true) := by
  cases truth <;> rfl

private theorem and_beq_true (left right : Truth) :
    (Truth.and left right == .true) =
      ((left == .true) && (right == .true)) := by
  cases left <;> cases right <;> rfl

private theorem and_decide_true (left right : Truth) :
    decide (Truth.and left right = .true) =
      (decide (left = .true) && decide (right = .true)) := by
  cases left <;> cases right <;> rfl

theorem combinedJoinPredicate_selects (on where_ : Option CoreJoin.Predicate)
    (row : CoreJoin.JoinedRow) :
    ((combinedJoinPredicate on where_).eval (joinedRow row) == .true) =
      (CoreJoin.selects on row && CoreJoin.selects where_ row) := by
  cases on <;> cases where_ <;>
    simp [combinedJoinPredicate, CoreJoin.selects,
      QuerySemantics.Predicate.eval, joinPredicate_eval,
      truth_beq_true, and_beq_true, and_decide_true]

theorem joinRows_embedded (left right : List Core.Row) :
    QuerySemantics.joinRows (left.map joinRow) (right.map joinRow) =
      (CoreJoin.crossRows left right).map joinedRow := by
  simp [QuerySemantics.joinRows, CoreJoin.crossRows, List.map_flatMap,
    List.flatMap_map, Function.comp_def, joinedRow, joinRow]

theorem whereRows_joined (on where_ : Option CoreJoin.Predicate)
    (rows : List CoreJoin.JoinedRow) :
    QuerySemantics.whereRows (combinedJoinPredicate on where_)
        (rows.map joinedRow) =
      (CoreJoin.matchingRows on where_ rows).map joinedRow := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.map_cons, QuerySemantics.whereRows,
        CoreJoin.matchingRows, List.filter_cons]
      rw [combinedJoinPredicate_selects]
      split <;>
        simpa [QuerySemantics.whereRows, CoreJoin.matchingRows] using induction

def innerJoinPlan (on where_ : Option CoreJoin.Predicate)
    (left right : List Core.Row) : QuerySemantics.Plan :=
  .filter (combinedJoinPredicate on where_)
    (.innerJoin (.rows (left.map joinRow)) (.rows (right.map joinRow)))

theorem innerJoinPlan_eval (database : Core.Database)
    (on where_ : Option CoreJoin.Predicate) (left right : List Core.Row) :
    QuerySemantics.evalPlan database (innerJoinPlan on where_ left right) =
      (CoreJoin.matchingRows on where_ (CoreJoin.crossRows left right)).map
        joinedRow := by
  simp only [innerJoinPlan, QuerySemantics.evalPlan]
  rw [joinRows_embedded, whereRows_joined]

theorem optimize_innerJoinPlan_eval (database : Core.Database)
    (on where_ : Option CoreJoin.Predicate) (left right : List Core.Row) :
    QuerySemantics.evalPlan database
        (QuerySemantics.optimizePlan (innerJoinPlan on where_ left right)) =
      (CoreJoin.matchingRows on where_ (CoreJoin.crossRows left right)).map
        joinedRow := by
  rw [QuerySemantics.optimizePlan_eval]
  exact innerJoinPlan_eval database on where_ left right

def optionalJoinPredicate : Option CoreJoin.Predicate → QuerySemantics.Predicate
  | none => .constant .true
  | some predicate => joinPredicate predicate

theorem optionalJoinPredicate_selects (predicate : Option CoreJoin.Predicate)
    (row : CoreJoin.JoinedRow) :
    ((optionalJoinPredicate predicate).eval (joinedRow row) == .true) =
      CoreJoin.selects predicate row := by
  cases predicate <;>
    simp [optionalJoinPredicate, CoreJoin.selects,
      QuerySemantics.Predicate.eval, joinPredicate_eval, truth_beq_true]

private theorem outerCandidates_embedded (on : Option CoreJoin.Predicate)
    (left : Core.Row) (right : List Core.Row) :
    ((right.map joinRow).map fun row => .joined (joinRow left) row).filter
        (fun row => (optionalJoinPredicate on).eval row == .true) =
      ((right.map fun row => (left, row)).filter (CoreJoin.selects on)).map
        joinedRow := by
  induction right with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.map_cons, List.filter_cons]
      rw [show QuerySemantics.Row.joined (joinRow left) (joinRow row) =
        joinedRow (left, row) by rfl]
      rw [optionalJoinPredicate_selects]
      split <;> simp_all

theorem leftOuterForRows_embedded (on : Option CoreJoin.Predicate)
    (rightWidth : Nat) (left : Core.Row) (right : List Core.Row) :
    QuerySemantics.leftOuterForRowsWith (optionalJoinPredicate on)
        (joinRow (CoreJoin.nullRow rightWidth)) (joinRow left)
        (right.map joinRow) =
      (CoreJoin.leftOuterFor on rightWidth left right).map joinedRow := by
  unfold QuerySemantics.leftOuterForRowsWith CoreJoin.leftOuterFor
  rw [outerCandidates_embedded]
  generalize (right.map fun row => (left, row)).filter
    (CoreJoin.selects on) = candidates
  have mappedEmpty : (candidates.map joinedRow).isEmpty =
      candidates.isEmpty := by cases candidates <;> rfl
  change (if (candidates.map joinedRow).isEmpty = true then
      [joinedRow (left, CoreJoin.nullRow rightWidth)]
    else candidates.map joinedRow) =
      (if candidates.isEmpty = true then
        [(left, CoreJoin.nullRow rightWidth)] else candidates).map joinedRow
  rw [mappedEmpty]
  cases empty : candidates.isEmpty <;> simp [empty]

theorem leftOuterRows_embedded (on : Option CoreJoin.Predicate)
    (rightWidth : Nat) (left right : List Core.Row) :
    QuerySemantics.leftOuterOnRowsWith (optionalJoinPredicate on)
        (joinRow (CoreJoin.nullRow rightWidth))
        (left.map joinRow) (right.map joinRow) =
      (CoreJoin.leftOuterRows on rightWidth left right).map joinedRow := by
  induction left with
  | nil => rfl
  | cons row rows induction =>
      unfold QuerySemantics.leftOuterOnRowsWith CoreJoin.leftOuterRows
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [leftOuterForRows_embedded]
      change (CoreJoin.leftOuterFor on rightWidth row right).map joinedRow ++
          QuerySemantics.leftOuterOnRowsWith (optionalJoinPredicate on)
            (joinRow (CoreJoin.nullRow rightWidth))
            (rows.map joinRow) (right.map joinRow) =
        (CoreJoin.leftOuterFor on rightWidth row right).map joinedRow ++
          (CoreJoin.leftOuterRows on rightWidth rows right).map joinedRow
      rw [induction]

theorem whereRows_outer_embedded (where_ : Option CoreJoin.Predicate)
    (rows : List CoreJoin.JoinedRow) :
    QuerySemantics.whereRows (optionalJoinPredicate where_)
        (rows.map joinedRow) =
      (rows.filter (CoreJoin.selects where_)).map joinedRow := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.map_cons, QuerySemantics.whereRows, List.filter_cons]
      rw [optionalJoinPredicate_selects]
      split <;>
        simpa [QuerySemantics.whereRows] using induction

def leftOuterJoinPlan (on where_ : Option CoreJoin.Predicate)
    (rightWidth : Nat) (left right : List Core.Row) : QuerySemantics.Plan :=
  .filter (optionalJoinPredicate where_)
    (.leftOuterOnWith (optionalJoinPredicate on)
      (joinRow (CoreJoin.nullRow rightWidth))
      (.rows (left.map joinRow)) (.rows (right.map joinRow)))

theorem leftOuterJoinPlan_eval (database : Core.Database)
    (on where_ : Option CoreJoin.Predicate) (rightWidth : Nat)
    (left right : List Core.Row) :
    QuerySemantics.evalPlan database
        (leftOuterJoinPlan on where_ rightWidth left right) =
      ((CoreJoin.leftOuterRows on rightWidth left right).filter
        (CoreJoin.selects where_)).map joinedRow := by
  simp only [leftOuterJoinPlan, QuerySemantics.evalPlan]
  rw [leftOuterRows_embedded, whereRows_outer_embedded]

theorem optimize_leftOuterJoinPlan_eval (database : Core.Database)
    (on where_ : Option CoreJoin.Predicate) (rightWidth : Nat)
    (left right : List Core.Row) :
    QuerySemantics.evalPlan database
        (QuerySemantics.optimizePlan
          (leftOuterJoinPlan on where_ rightWidth left right)) =
      ((CoreJoin.leftOuterRows on rightWidth left right).filter
        (CoreJoin.selects where_)).map joinedRow := by
  rw [QuerySemantics.optimizePlan_eval]
  exact leftOuterJoinPlan_eval database on where_ rightWidth left right

/-- A symbolic live join plan. Table names, rather than row literals, ensure
running the optimizer adds no scan or allocation to query execution. -/
def symbolicJoinPredicatePlan (leftName rightName : String)
    (predicate : CoreJoin.Predicate) : QuerySemantics.Plan :=
  .project .identity
    (.filter (joinPredicate predicate)
      (.innerJoin (.table leftName) (.table rightName)))

def extractJoinPredicate? : QuerySemantics.Plan → Option CoreJoin.Predicate
  | .filter predicate (.innerJoin _ _) => fromJoinPredicate? predicate
  | _ => none

def optimizeJoinPredicate (leftName rightName : String)
    (predicate : CoreJoin.Predicate) : CoreJoin.Predicate :=
  (extractJoinPredicate? (QuerySemantics.optimizePlan
    (symbolicJoinPredicatePlan leftName rightName predicate))).getD predicate

theorem foldNot_joinPredicate (predicate : CoreJoin.Predicate) :
    QuerySemantics.foldNot (joinPredicate predicate) =
      .not (joinPredicate predicate) := by
  cases predicate <;> rfl

theorem foldAnd_joinPredicate (left right : CoreJoin.Predicate) :
    QuerySemantics.foldAnd (joinPredicate left) (joinPredicate right) =
      .and (joinPredicate left) (joinPredicate right) := by
  cases left <;> cases right <;> rfl

theorem foldOr_joinPredicate (left right : CoreJoin.Predicate) :
    QuerySemantics.foldOr (joinPredicate left) (joinPredicate right) =
      .or (joinPredicate left) (joinPredicate right) := by
  cases left <;> cases right <;> rfl

theorem foldConstants_joinPredicate (predicate : CoreJoin.Predicate) :
    QuerySemantics.foldConstants (joinPredicate predicate) =
      joinPredicate predicate := by
  induction predicate <;>
    simp_all [joinPredicate, QuerySemantics.foldConstants,
      foldNot_joinPredicate, foldAnd_joinPredicate, foldOr_joinPredicate]

theorem optimizeJoinPredicate_eq (leftName rightName : String)
    (predicate : CoreJoin.Predicate) :
    optimizeJoinPredicate leftName rightName predicate = predicate := by
  cases predicate <;>
    simp [optimizeJoinPredicate, symbolicJoinPredicatePlan,
      QuerySemantics.optimizePlan, QuerySemantics.rewriteRoot,
      QuerySemantics.predicatePushdown, QuerySemantics.constantFolding,
      QuerySemantics.projectionElimination, QuerySemantics.filterFusion,
      QuerySemantics.unionDistribution, QuerySemantics.foldConstants,
      foldConstants_joinPredicate, foldNot_joinPredicate,
      foldAnd_joinPredicate, foldOr_joinPredicate, joinPredicate,
      extractJoinPredicate?, fromJoinPredicate?,
      fromJoinPredicate_joinPredicate,
      fromJoinOperand_joinOperand]

end CoreOptimizerBridge

end SQLeanite
