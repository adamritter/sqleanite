import SQLeanite.CoreOptimizerBridge.ToSemantics

namespace SQLeanite
namespace CoreOptimizerBridge
open QuerySemantics

def symbolicLeftOnPlan (leftName rightName : String) (rightWidth : Nat)
    (predicate : CoreJoin.Predicate) : QuerySemantics.Plan :=
  .leftOuterOnWith (joinPredicate predicate)
    (joinRow (CoreJoin.nullRow rightWidth))
    (.table leftName) (.table rightName)

def extractLeftOnPredicate? : QuerySemantics.Plan → Option CoreJoin.Predicate
  | .leftOuterOnWith predicate _ _ _ => fromJoinPredicate? predicate
  | _ => none

def optimizeLeftOnPredicate (leftName rightName : String) (rightWidth : Nat)
    (predicate : CoreJoin.Predicate) : CoreJoin.Predicate :=
  (extractLeftOnPredicate? (QuerySemantics.optimizePlan
    (symbolicLeftOnPlan leftName rightName rightWidth predicate))).getD predicate

theorem optimizeLeftOnPredicate_eq (leftName rightName : String)
    (rightWidth : Nat) (predicate : CoreJoin.Predicate) :
    optimizeLeftOnPredicate leftName rightName rightWidth predicate = predicate := by
  simp [optimizeLeftOnPredicate, symbolicLeftOnPlan,
    QuerySemantics.optimizePlan, QuerySemantics.rewriteRoot,
    QuerySemantics.predicatePushdown, QuerySemantics.constantFolding,
    QuerySemantics.projectionElimination, QuerySemantics.filterFusion,
    QuerySemantics.unionDistribution, extractLeftOnPredicate?,
    fromJoinPredicate_joinPredicate]

def symbolicLeftWherePlan (leftName rightName : String) (rightWidth : Nat)
    (predicate : CoreJoin.Predicate) : QuerySemantics.Plan :=
  .filter (joinPredicate predicate)
    (.leftOuterOnWith (.constant .true)
      (joinRow (CoreJoin.nullRow rightWidth))
      (.table leftName) (.table rightName))

def extractLeftWherePredicate? : QuerySemantics.Plan → Option CoreJoin.Predicate
  | .filter predicate (.leftOuterOnWith _ _ _ _) => fromJoinPredicate? predicate
  | _ => none

def optimizeLeftWherePredicate (leftName rightName : String) (rightWidth : Nat)
    (predicate : CoreJoin.Predicate) : CoreJoin.Predicate :=
  (extractLeftWherePredicate? (QuerySemantics.optimizePlan
    (symbolicLeftWherePlan leftName rightName rightWidth predicate))).getD predicate

theorem optimizeLeftWherePredicate_eq (leftName rightName : String)
    (rightWidth : Nat) (predicate : CoreJoin.Predicate) :
    optimizeLeftWherePredicate leftName rightName rightWidth predicate = predicate := by
  cases predicate <;>
    simp [optimizeLeftWherePredicate, symbolicLeftWherePlan,
      QuerySemantics.optimizePlan, QuerySemantics.rewriteRoot,
      QuerySemantics.predicatePushdown, QuerySemantics.constantFolding,
      QuerySemantics.projectionElimination, QuerySemantics.filterFusion,
      QuerySemantics.unionDistribution, QuerySemantics.foldConstants,
      foldConstants_joinPredicate, foldNot_joinPredicate,
      foldAnd_joinPredicate, foldOr_joinPredicate, joinPredicate,
      extractLeftWherePredicate?, fromJoinPredicate?,
      fromJoinPredicate_joinPredicate, fromJoinOperand_joinOperand]

/-- Run both live join clauses through the proved optimizer pipeline before
the existing merge/nested-loop planner. The equality theorem makes this a
zero-risk integration point while later join rewrites can become executable
by changing only the extraction layer and its refinement proof. -/
def optimizeJoin (leftName rightName : String)
    (query : CoreJoin.Query) : CoreJoin.Query :=
  match query.kind with
  | .inner =>
      { query with
        on := query.on.map (optimizeJoinPredicate leftName rightName)
        where_ := query.where_.map (optimizeJoinPredicate leftName rightName) }
  | .left =>
      { query with
        on := query.on.map
          (optimizeLeftOnPredicate leftName rightName query.rightWidth)
        where_ := query.where_.map
          (optimizeLeftWherePredicate leftName rightName query.rightWidth) }

theorem optimizeJoin_eq (leftName rightName : String)
    (query : CoreJoin.Query) :
    optimizeJoin leftName rightName query = query := by
  cases query with
  | mk columns on kind rightWidth where_ orderBy limit offset distinct distinctScanOrder =>
      cases kind <;> cases on <;> cases where_ <;>
        simp [optimizeJoin, optimizeJoinPredicate_eq,
          optimizeLeftOnPredicate_eq, optimizeLeftWherePredicate_eq]

theorem optimizeJoin_eval (leftName rightName : String)
    (query : CoreJoin.Query) (left right : List Core.Row) :
    (optimizeJoin leftName rightName query).eval left right =
      query.eval left right := by
  rw [optimizeJoin_eq]

def compoundRows (operation : CompoundOp)
    (left right : List (List Core.Value)) : List (List Core.Value) :=
  match operation with
  | .unionAll => left ++ right
  | .unionDistinct => Core.deduplicate (left ++ right)
  | .intersect => (Core.deduplicate left).filter (· ∈ right)
  | .except => (Core.deduplicate left).filter (· ∉ right)

def compoundRow (values : List Core.Value) : QuerySemantics.Row :=
  .values values

private theorem compoundRow_beq (left right : List Core.Value) :
    (compoundRow left == compoundRow right) = (left == right) := by
  rfl

private theorem deduplicate_compoundRows (rows : List (List Core.Value)) :
    Core.deduplicate (rows.map compoundRow) =
      (Core.deduplicate rows).map compoundRow := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.map_cons, Core.deduplicate]
      by_cases member : row ∈ rows
      · rw [if_pos member]
        rw [if_pos]
        · exact induction
        · simpa [compoundRow] using member
      · rw [if_neg member]
        rw [if_neg]
        · simp [induction]
        · simpa [compoundRow] using member

private theorem mem_erase_of_ne [DecidableEq α] {removed value : α}
    (unequal : value ≠ removed) (values : List α) :
    value ∈ values.erase removed ↔ value ∈ values :=
  List.mem_erase_of_ne unequal

private theorem filter_mem_erase [DecidableEq α] (removed : α)
    (values right : List α) (absent : removed ∉ values) :
    values.filter (· ∈ right.erase removed) =
      values.filter (· ∈ right) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      have unequal : value ≠ removed := by
        intro equal
        apply absent
        simp [equal]
      have tailAbsent : removed ∉ values := by
        intro member
        exact absent (by simp [member])
      simp only [List.filter_cons]
      have membership := mem_erase_of_ne unequal right
      rw [show decide (value ∈ right.erase removed) =
          decide (value ∈ right) by
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using membership]
      rw [induction tailAbsent]

private theorem bagIntersect_eq_filter [DecidableEq α]
    (left right : List α) (unique : left.Nodup) :
    QuerySemantics.bagIntersect left right = left.filter (· ∈ right) := by
  induction left generalizing right with
  | nil => rfl
  | cons value values induction =>
      simp only [List.nodup_cons] at unique
      unfold QuerySemantics.bagIntersect
      by_cases member : value ∈ right
      · rw [if_pos member]
        simp only [List.filter_cons, decide_eq_true member, if_true,
          List.cons.injEq, true_and]
        rw [induction (right.erase value) unique.2]
        exact filter_mem_erase value values right unique.1
      · rw [if_neg member]
        simp [member, induction right unique.2]

private theorem bagExcept_eq_filter [DecidableEq α]
    (left right : List α) (unique : left.Nodup) :
    QuerySemantics.bagExcept left right = left.filter (· ∉ right) := by
  induction left generalizing right with
  | nil => rfl
  | cons value values induction =>
      simp only [List.nodup_cons] at unique
      unfold QuerySemantics.bagExcept
      by_cases member : value ∈ right
      · rw [if_pos member]
        simp only [List.filter_cons, decide_eq_false (not_not_intro member),
          if_false]
        rw [induction (right.erase value) unique.2]
        apply List.filter_congr
        intro candidate candidateMember
        have unequal : candidate ≠ value := by
          intro equal
          subst candidate
          exact unique.1 candidateMember
        have sameMembership := mem_erase_of_ne unequal right
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using not_congr sameMembership
      · rw [if_neg member]
        simp [member, induction right unique.2]

def compoundPlanOf (operation : CompoundOp)
    (left right : QuerySemantics.Plan) : QuerySemantics.Plan :=
  match operation with
  | .unionAll => .unionAll left right
  | .unionDistinct => .distinct (.unionAll left right)
  | .intersect => .intersectAll (.distinct left) (.distinct right)
  | .except => .exceptAll (.distinct left) (.distinct right)

def compoundPlan (operation : CompoundOp)
    (left right : List (List Core.Value)) : QuerySemantics.Plan :=
  compoundPlanOf operation
    (.rows (left.map compoundRow)) (.rows (right.map compoundRow))

private theorem nodup_map_compoundRow {rows : List (List Core.Value)}
    (unique : rows.Nodup) : (rows.map compoundRow).Nodup := by
  induction rows with
  | nil => simp
  | cons row rows induction =>
      simp only [List.nodup_cons] at unique ⊢
      constructor
      · intro member membership
        simp only [List.mem_map] at membership
        rcases membership with ⟨values, valuesMember, rfl⟩
        intro equal
        apply unique.1
        have same : row = values := by
          simpa [compoundRow] using equal
        simpa [same] using valuesMember
      · exact induction unique.2

private theorem filter_map_compoundRow_exists
    (rows right : List (List Core.Value)) :
    (rows.map compoundRow).filter (fun candidate => decide
        (∃ value, value ∈ right ∧ compoundRow value = candidate)) =
      (rows.filter (fun row => decide (row ∈ right))).map compoundRow := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.map_cons, List.filter_cons]
      have sameDecision :
          decide (∃ value, value ∈ right ∧
            compoundRow value = compoundRow row) =
            decide (row ∈ right) := by
        apply Bool.eq_iff_iff.mpr
        simp [compoundRow]
      rw [sameDecision, induction]
      by_cases keep : decide (row ∈ right) = true <;> simp [keep]

private theorem filter_map_compoundRow_forall
    (rows right : List (List Core.Value)) :
    (rows.map compoundRow).filter (fun candidate => decide
        (∀ value, value ∈ right → compoundRow value ≠ candidate)) =
      (rows.filter (fun row => decide (row ∉ right))).map compoundRow := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.map_cons, List.filter_cons]
      have sameDecision :
          decide (∀ value, value ∈ right →
            compoundRow value ≠ compoundRow row) =
            decide (row ∉ right) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · intro all member
          exact (all row member) rfl
        · intro absent value member equal
          apply absent
          have same : value = row := by
            simpa [compoundRow] using equal
          simpa [same] using member
      rw [sameDecision, induction]
      by_cases keep : decide (row ∉ right) = true <;> simp [keep]

theorem compoundPlan_eval (database : Core.Database) (operation : CompoundOp)
    (left right : List (List Core.Value)) :
    QuerySemantics.evalPlan database (compoundPlan operation left right) =
      (compoundRows operation left right).map compoundRow := by
  cases operation with
  | unionAll =>
      simp [compoundPlan, compoundPlanOf, compoundRows,
        QuerySemantics.evalPlan]
  | unionDistinct =>
      simp only [compoundPlan, compoundPlanOf, QuerySemantics.evalPlan,
        compoundRows, List.map_append]
      rw [← List.map_append]
      rw [deduplicate_compoundRows]
  | intersect =>
      simp only [compoundPlan, compoundPlanOf, QuerySemantics.evalPlan,
        deduplicate_compoundRows]
      rw [bagIntersect_eq_filter _ _
        (nodup_map_compoundRow (Core.deduplicate_nodup _))]
      simp only [List.mem_map]
      rw [filter_map_compoundRow_exists]
      simp [compoundRows, Core.mem_deduplicate]
  | except =>
      simp only [compoundPlan, compoundPlanOf, QuerySemantics.evalPlan,
        deduplicate_compoundRows]
      rw [bagExcept_eq_filter _ _
        (nodup_map_compoundRow (Core.deduplicate_nodup _))]
      simp only [List.mem_map, not_exists, not_and]
      rw [filter_map_compoundRow_forall]
      simp [compoundRows, Core.mem_deduplicate]

theorem optimize_compoundPlan_eval (database : Core.Database)
    (operation : CompoundOp) (left right : List (List Core.Value)) :
    QuerySemantics.evalPlan database
        (QuerySemantics.optimizePlan (compoundPlan operation left right)) =
      (compoundRows operation left right).map compoundRow := by
  rw [QuerySemantics.optimizePlan_eval]
  exact compoundPlan_eval database operation left right

def symbolicCompoundPlan (operation : CompoundOp) : QuerySemantics.Plan :=
  compoundPlanOf operation (.table "__left") (.table "__right")

def extractCompoundOp? : QuerySemantics.Plan → Option CompoundOp
  | .unionAll (.table "__left") (.table "__right") => some .unionAll
  | .distinct (.unionAll (.table "__left") (.table "__right")) =>
      some .unionDistinct
  | .intersectAll (.distinct (.table "__left"))
      (.distinct (.table "__right")) => some .intersect
  | .exceptAll (.distinct (.table "__left"))
      (.distinct (.table "__right")) => some .except
  | _ => none

def optimizeCompoundOp (operation : CompoundOp) : CompoundOp :=
  (extractCompoundOp?
    (QuerySemantics.optimizePlan (symbolicCompoundPlan operation))).getD operation

theorem optimizeCompoundOp_eq (operation : CompoundOp) :
    optimizeCompoundOp operation = operation := by
  cases operation <;>
    simp [optimizeCompoundOp, symbolicCompoundPlan, compoundPlanOf,
      QuerySemantics.optimizePlan, QuerySemantics.rewriteRoot,
      QuerySemantics.predicatePushdown, QuerySemantics.constantFolding,
      QuerySemantics.projectionElimination, QuerySemantics.filterFusion,
      QuerySemantics.unionDistribution, extractCompoundOp?]

end CoreOptimizerBridge

end SQLeanite
