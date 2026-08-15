import SQLeanite.Optimizer

namespace SQLeanite
namespace QuerySemantics

/-!
# Executable logical cost semantics

This is deliberately not a wall-clock model.  It counts the three operations
whose asymptotic shape matters to the live engine: rows traversed, SQL value
comparisons, and output rows materialized.  It is proof-only and is never run
by query execution.
-/

structure Cost where
  rowVisits : Nat := 0
  comparisons : Nat := 0
  materializations : Nat := 0
  deriving Repr, DecidableEq

def Cost.add (left right : Cost) : Cost :=
  ⟨left.rowVisits + right.rowVisits,
    left.comparisons + right.comparisons,
    left.materializations + right.materializations⟩

instance : Add Cost := ⟨Cost.add⟩

def Cost.LE (left right : Cost) : Prop :=
  left.rowVisits ≤ right.rowVisits ∧
    left.comparisons ≤ right.comparisons ∧
    left.materializations ≤ right.materializations

def Cost.total (cost : Cost) : Nat :=
  cost.rowVisits + cost.comparisons + cost.materializations

theorem Cost.LE.refl (cost : Cost) : cost.LE cost := by
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem Cost.LE.trans {first second third : Cost}
    (left : first.LE second) (right : second.LE third) : first.LE third := by
  exact ⟨Nat.le_trans left.1 right.1,
    Nat.le_trans left.2.1 right.2.1,
    Nat.le_trans left.2.2 right.2.2⟩

theorem Cost.total_le {left right : Cost} (bounded : left.LE right) :
    left.total ≤ right.total := by
  unfold Cost.total
  rcases bounded with ⟨visits, comparisons, materializations⟩
  omega

/-- Number of physical comparison/null/truth tests performed for one row.
Boolean connective bookkeeping is not counted as a value comparison. -/
def Predicate.comparisonCount : Predicate → Nat
  | .constant _ => 0
  | .truthy _ | .equals _ _ | .notEquals _ _ | .compare _ _ _ |
      .operandsEqual _ _ | .operandsNotEqual _ _ | .operandsCompare _ _ _ |
      .operandIsNull _ | .isNull _ => 1
  | .not predicate | .onLeft predicate | .onRight predicate =>
      predicate.comparisonCount
  | .and left right | .or left right =>
      left.comparisonCount + right.comparisonCount

private theorem foldNot_comparisonCount_le (predicate : Predicate) :
    (foldNot predicate).comparisonCount ≤ predicate.comparisonCount := by
  cases predicate <;> simp [foldNot, Predicate.comparisonCount]

private theorem foldAnd_comparisonCount_le (left right : Predicate) :
    (foldAnd left right).comparisonCount ≤
      left.comparisonCount + right.comparisonCount := by
  cases left <;> cases right <;>
    simp [foldAnd, Predicate.comparisonCount]

private theorem foldOr_comparisonCount_le (left right : Predicate) :
    (foldOr left right).comparisonCount ≤
      left.comparisonCount + right.comparisonCount := by
  cases left <;> cases right <;>
    simp [foldOr, Predicate.comparisonCount]

theorem foldConstants_comparisonCount_le (predicate : Predicate) :
    (foldConstants predicate).comparisonCount ≤ predicate.comparisonCount := by
  induction predicate with
  | constant | truthy | equals | notEquals | compare | operandsEqual |
      operandsNotEqual | operandsCompare | operandIsNull | isNull =>
      exact Nat.le_refl _
  | not predicate induction =>
      exact Nat.le_trans (foldNot_comparisonCount_le (foldConstants predicate))
        induction
  | and left right leftInduction rightInduction =>
      exact Nat.le_trans
        (foldAnd_comparisonCount_le (foldConstants left) (foldConstants right))
        (Nat.add_le_add leftInduction rightInduction)
  | or left right leftInduction rightInduction =>
      exact Nat.le_trans
        (foldOr_comparisonCount_le (foldConstants left) (foldConstants right))
        (Nat.add_le_add leftInduction rightInduction)
  | onLeft predicate induction | onRight predicate induction =>
      simpa [foldConstants, Predicate.comparisonCount] using induction

structure Profile where
  rows : List Row
  cost : Cost

private def filterCost (predicate : Predicate) (input : Profile) : Cost :=
  input.cost + {
    rowVisits := input.rows.length
    comparisons := input.rows.length * predicate.comparisonCount }

/-- Execute the denotation while accumulating logical work.  This function is
used in theorems and experiments, never by the live executor. -/
def profile (database : Core.Database) : Plan → Profile
  | .table name =>
      let rows := tableRows database name
      ⟨rows, { rowVisits := rows.length }⟩
  | .rows rows => ⟨rows, { rowVisits := rows.length }⟩
  | .unionAll left right =>
      let left := profile database left
      let right := profile database right
      ⟨left.rows ++ right.rows,
        left.cost + right.cost + { materializations := left.rows.length }⟩
  | .intersectAll left right =>
      let left := profile database left
      let right := profile database right
      let rows := bagIntersect left.rows right.rows
      ⟨rows, left.cost + right.cost + {
        rowVisits := left.rows.length
        comparisons := left.rows.length * right.rows.length
        materializations := rows.length }⟩
  | .exceptAll left right =>
      let left := profile database left
      let right := profile database right
      let rows := bagExcept left.rows right.rows
      ⟨rows, left.cost + right.cost + {
        rowVisits := left.rows.length
        comparisons := left.rows.length * right.rows.length
        materializations := rows.length }⟩
  | .distinct input =>
      let input := profile database input
      let rows := Core.deduplicate input.rows
      ⟨rows, input.cost + {
        rowVisits := input.rows.length
        comparisons := input.rows.length * input.rows.length
        materializations := rows.length }⟩
  | .filter predicate input =>
      let input := profile database input
      ⟨whereRows predicate input.rows, filterCost predicate input⟩
  | .project projection input =>
      let input := profile database input
      ⟨input.rows.map projection.apply,
        input.cost + {
          rowVisits := input.rows.length
          materializations := input.rows.length }⟩
  | .innerJoin left right =>
      let left := profile database left
      let right := profile database right
      let rows := joinRows left.rows right.rows
      ⟨rows, left.cost + right.cost + {
        rowVisits := left.rows.length + left.rows.length * right.rows.length
        materializations := rows.length }⟩
  | .leftOuterJoin left right =>
      let left := profile database left
      let right := profile database right
      let rows := leftJoinRows left.rows right.rows
      ⟨rows, left.cost + right.cost + {
        rowVisits := left.rows.length + left.rows.length * right.rows.length
        materializations := rows.length }⟩
  | .leftOuterOn predicate left right =>
      let left := profile database left
      let right := profile database right
      let rows := leftOuterOnRows predicate left.rows right.rows
      ⟨rows, left.cost + right.cost + {
        rowVisits := left.rows.length + left.rows.length * right.rows.length
        comparisons := left.rows.length * right.rows.length *
          predicate.comparisonCount
        materializations := rows.length }⟩
  | .leftOuterOnWith predicate nullRight left right =>
      let left := profile database left
      let right := profile database right
      let rows := leftOuterOnRowsWith predicate nullRight left.rows right.rows
      ⟨rows, left.cost + right.cost + {
        rowVisits := left.rows.length + left.rows.length * right.rows.length
        comparisons := left.rows.length * right.rows.length *
          predicate.comparisonCount
        materializations := rows.length }⟩
  | .groupCount key input =>
      let input := profile database input
      let rows := groupCountRows key input.rows
      ⟨rows, input.cost + {
        rowVisits := input.rows.length
        materializations := rows.length }⟩
  | .groupSum key measure input =>
      let input := profile database input
      let rows := groupSumRows key measure input.rows
      ⟨rows, input.cost + {
        rowVisits := input.rows.length
        materializations := rows.length }⟩

def cost (database : Core.Database) (plan : Plan) : Cost :=
  (profile database plan).cost

theorem profile_rows (database : Core.Database) (plan : Plan) :
    (profile database plan).rows = evalPlan database plan := by
  induction plan with
  | table | rows => rfl
  | unionAll left right leftInduction rightInduction |
    intersectAll left right leftInduction rightInduction |
    exceptAll left right leftInduction rightInduction |
    innerJoin left right leftInduction rightInduction |
    leftOuterJoin left right leftInduction rightInduction =>
      simp [profile, evalPlan, leftInduction, rightInduction]
  | distinct input induction | filter _ input induction |
    project _ input induction | groupCount _ input induction |
    groupSum _ _ input induction =>
      simp [profile, evalPlan, induction]
  | leftOuterOn _ left right leftInduction rightInduction |
    leftOuterOnWith _ _ left right leftInduction rightInduction =>
      simp [profile, evalPlan, leftInduction, rightInduction]

theorem projectionElimination_cost_le (database : Core.Database) (plan : Plan) :
    (cost database (projectionElimination plan)).LE (cost database plan) := by
  cases plan <;> try exact Cost.LE.refl _
  case project projection input =>
    cases projection with
    | identity =>
        change (profile database input).cost.LE
          ((profile database input).cost + {
            rowVisits := (profile database input).rows.length
            materializations := (profile database input).rows.length })
        generalize costEqual : (profile database input).cost = inputCost
        rcases inputCost with ⟨visits, comparisons, materializations⟩
        change visits ≤ visits + (profile database input).rows.length ∧
          comparisons ≤ comparisons + 0 ∧
          materializations ≤ materializations +
            (profile database input).rows.length
        omega
    | left | right => exact Cost.LE.refl _

theorem projectionElimination_strict_on_nonempty_rows
    (database : Core.Database) (row : Row) (rows : List Row) :
    (cost database (projectionElimination
        (.project .identity (.rows (row :: rows))))).total <
      (cost database (.project .identity (.rows (row :: rows)))).total := by
  change rows.length + 1 <
    (rows.length + 1 + (rows.length + 1)) + (0 + 0) +
      (0 + (rows.length + 1))
  omega

/-- Constant folding never adds a physical value comparison.  Row traversal
and materialization counts are identical because the filtered bag is equal. -/
theorem constantFolding_cost_le (database : Core.Database) (plan : Plan) :
    (cost database (constantFolding plan)).LE (cost database plan) := by
  cases plan <;> try exact Cost.LE.refl _
  case filter predicate input =>
    have comparisons := foldConstants_comparisonCount_le predicate
    simp only [constantFolding, cost, profile, filterCost, Cost.LE, Cost.add]
    constructor
    · exact Nat.le_refl _
    constructor
    · exact Nat.add_le_add_left
        (Nat.mul_le_mul_left (profile database input).rows.length comparisons) _
    · exact Nat.le_refl _

/-- The exact root pipeline selected by the live optimizer is cost-safe in all
three dimensions.  The conditional rewrites remain outside `rewriteRoot`. -/
theorem rewriteRoot_cost_le (database : Core.Database) (plan : Plan) :
    (cost database (rewriteRoot plan)).LE (cost database plan) := by
  unfold rewriteRoot
  exact (projectionElimination_cost_le database (constantFolding plan)).trans
    (constantFolding_cost_le database plan)

/-- Exact condition for filter fusion under this strict predicate evaluator.
Fusion saves one list traversal over rows passing the inner filter, but it also
evaluates the outer predicate on rows rejected by the inner predicate. -/
def FilterFusionProfitable (database : Core.Database) (outer inner : Predicate)
    (input : Plan) : Prop :=
  let rows := (profile database input).rows
  let kept := (whereRows inner rows).length
  (rows.length - kept) * outer.comparisonCount ≤ kept

/-- The conditional classification is substantive: strict evaluation makes
unconditional filter fusion increase comparisons on a rejected row. -/
theorem filterFusion_not_unconditionally_cost_safe (database : Core.Database) :
    ¬ Cost.LE
      (cost database (filterFusion
        (.filter (.isNull (.cell 0))
          (.filter (.constant .false) (.rows [.values []])))))
      (cost database
        (.filter (.isNull (.cell 0))
          (.filter (.constant .false) (.rows [.values []])))) := by
  change ¬ (2 ≤ 2 ∧ 1 ≤ 0 ∧ 0 ≤ 0)
  omega

end QuerySemantics
end SQLeanite
