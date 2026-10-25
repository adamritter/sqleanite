import SQLeanite.QuerySemantics

namespace SQLeanite
namespace QuerySemantics

def foldNot : Predicate → Predicate
  | .constant truth => .constant truth.not
  | predicate => .not predicate

def foldAnd : Predicate → Predicate → Predicate
  | .constant left, .constant right => .constant (Truth.and left right)
  | left, right => .and left right

def foldOr : Predicate → Predicate → Predicate
  | .constant left, .constant right => .constant (Truth.or left right)
  | left, right => .or left right

def foldConstants : Predicate → Predicate
  | .constant truth => .constant truth
  | .truthy column => .truthy column
  | .equals column value => .equals column value
  | .notEquals column value => .notEquals column value
  | .compare operation column value => .compare operation column value
  | .operandsEqual left right => .operandsEqual left right
  | .operandsNotEqual left right => .operandsNotEqual left right
  | .operandsCompare operation left right => .operandsCompare operation left right
  | .operandTruthy operand => .operandTruthy operand
  | .operandIsNull operand => .operandIsNull operand
  | .isNull column => .isNull column
  | .not predicate => foldNot (foldConstants predicate)
  | .and left right => foldAnd (foldConstants left) (foldConstants right)
  | .or left right => foldOr (foldConstants left) (foldConstants right)
  | .onLeft predicate => .onLeft (foldConstants predicate)
  | .onRight predicate => .onRight (foldConstants predicate)

private theorem foldNot_eval (predicate : Predicate) (row : Row) :
    (foldNot predicate).eval row = Truth.not (predicate.eval row) := by
  cases predicate <;> rfl

private theorem foldAnd_eval (left right : Predicate) (row : Row) :
    (foldAnd left right).eval row = Truth.and (left.eval row) (right.eval row) := by
  cases left <;> cases right <;> rfl

private theorem foldOr_eval (left right : Predicate) (row : Row) :
    (foldOr left right).eval row = Truth.or (left.eval row) (right.eval row) := by
  cases left <;> cases right <;> rfl

theorem foldConstants_eval (predicate : Predicate) (row : Row) :
    (foldConstants predicate).eval row = predicate.eval row := by
  induction predicate generalizing row with
  | constant | truthy | equals | notEquals | compare | operandsEqual |
      operandsNotEqual | operandsCompare | operandTruthy | operandIsNull | isNull => rfl
  | not predicate induction =>
      simp only [foldConstants, foldNot_eval, Predicate.eval, induction]
  | and left right leftInduction rightInduction =>
      simp only [foldConstants, foldAnd_eval, Predicate.eval,
        leftInduction, rightInduction]
  | or left right leftInduction rightInduction =>
      simp only [foldConstants, foldOr_eval, Predicate.eval,
        leftInduction, rightInduction]
  | onLeft predicate induction =>
      cases row <;> simp [foldConstants, Predicate.eval, induction]
  | onRight predicate induction =>
      cases row <;> simp [foldConstants, Predicate.eval, induction]

theorem whereRows_foldConstants (predicate : Predicate) (rows : List Row) :
    whereRows (foldConstants predicate) rows = whereRows predicate rows := by
  simp [whereRows, foldConstants_eval]

private theorem whereRows_append (predicate : Predicate) (left right : List Row) :
    whereRows predicate (left ++ right) =
      whereRows predicate left ++ whereRows predicate right := by
  simp [whereRows]

private theorem whereRows_onLeft_map (predicate : Predicate) (leftRow : Row)
    (rightRows : List Row) :
    whereRows (.onLeft predicate)
        (rightRows.map fun rightRow => .joined leftRow rightRow) =
      if predicate.eval leftRow == .true then
        rightRows.map fun rightRow => .joined leftRow rightRow
      else [] := by
  cases evaluated : predicate.eval leftRow <;>
    induction rightRows with
    | nil => simp [whereRows, evaluated]
    | cons rightRow rightRows induction =>
        simp [whereRows, Predicate.eval, evaluated, induction]

theorem whereRows_onLeft_joinRows (predicate : Predicate)
    (leftRows rightRows : List Row) :
    whereRows (.onLeft predicate) (joinRows leftRows rightRows) =
      joinRows (whereRows predicate leftRows) rightRows := by
  induction leftRows with
  | nil => rfl
  | cons leftRow leftRows induction =>
      change whereRows (.onLeft predicate)
          ((rightRows.map fun rightRow => .joined leftRow rightRow) ++
            joinRows leftRows rightRows) = _
      rw [whereRows_append, whereRows_onLeft_map, induction]
      cases evaluated : predicate.eval leftRow <;>
        simp [whereRows, joinRows, evaluated]

theorem whereRows_fusion (outer inner : Predicate) (rows : List Row) :
    whereRows outer (whereRows inner rows) =
      whereRows (.and inner outer) rows := by
  simp only [whereRows, List.filter_filter]
  congr 1
  funext row
  simp only [Predicate.eval]
  cases inner.eval row <;> cases outer.eval row <;> rfl

theorem joinRows_append_left (first second right : List Row) :
    joinRows (first ++ second) right =
      joinRows first right ++ joinRows second right := by
  simp [joinRows]

theorem leftJoinRows_append_left (first second right : List Row) :
    leftJoinRows (first ++ second) right =
      leftJoinRows first right ++ leftJoinRows second right := by
  cases right <;> simp [leftJoinRows, joinRows]

theorem leftOuterOnRows_append_left (predicate : Predicate)
    (first second right : List Row) :
    leftOuterOnRows predicate (first ++ second) right =
      leftOuterOnRows predicate first right ++
        leftOuterOnRows predicate second right := by
  simp [leftOuterOnRows, leftOuterOnRowsWith]

theorem leftOuterOnRowsWith_append_left (predicate : Predicate) (nullRight : Row)
    (first second right : List Row) :
    leftOuterOnRowsWith predicate nullRight (first ++ second) right =
      leftOuterOnRowsWith predicate nullRight first right ++
        leftOuterOnRowsWith predicate nullRight second right := by
  simp [leftOuterOnRowsWith]

/-- Exact list-order-preserving distribution laws.  Right-side product
distribution is intentionally absent: it preserves the bag but interleaves
rows differently, while this executable semantics promises list equality. -/
def unionDistribution : Plan → Plan
  | .filter predicate (.unionAll left right) =>
      .unionAll (.filter predicate left) (.filter predicate right)
  | .project projection (.unionAll left right) =>
      .unionAll (.project projection left) (.project projection right)
  | .innerJoin (.unionAll first second) right =>
      .unionAll (.innerJoin first right) (.innerJoin second right)
  | .leftOuterJoin (.unionAll first second) right =>
      .unionAll (.leftOuterJoin first right) (.leftOuterJoin second right)
  | .leftOuterOn predicate (.unionAll first second) right =>
      .unionAll (.leftOuterOn predicate first right)
        (.leftOuterOn predicate second right)
  | .leftOuterOnWith predicate nullRight (.unionAll first second) right =>
      .unionAll (.leftOuterOnWith predicate nullRight first right)
        (.leftOuterOnWith predicate nullRight second right)
  | .groupCount key (.unionAll left right) =>
      .unionAll (.groupCount key left) (.groupCount key right)
  | .groupSum key measure (.unionAll left right) =>
      .unionAll (.groupSum key measure left) (.groupSum key measure right)
  | plan => plan

theorem unionDistribution_eval (database : Core.Database) (plan : Plan) :
    evalPlan database (unionDistribution plan) = evalPlan database plan := by
  cases plan with
  | filter predicate input =>
      cases input <;> try rfl
      case unionAll left right =>
        exact (whereRows_append predicate
          (evalPlan database left) (evalPlan database right)).symm
  | project projection input =>
      cases input <;> try rfl
      case unionAll left right => simp [unionDistribution, evalPlan]
  | innerJoin left right =>
      cases left <;> try rfl
      case unionAll first second =>
        exact (joinRows_append_left
          (evalPlan database first) (evalPlan database second)
          (evalPlan database right)).symm
  | leftOuterJoin left right =>
      cases left <;> try rfl
      case unionAll first second =>
        exact (leftJoinRows_append_left
          (evalPlan database first) (evalPlan database second)
          (evalPlan database right)).symm
  | leftOuterOn predicate left right =>
      cases left <;> try rfl
      case unionAll first second =>
        exact (leftOuterOnRows_append_left predicate
          (evalPlan database first) (evalPlan database second)
          (evalPlan database right)).symm
  | leftOuterOnWith predicate nullRight left right =>
      cases left <;> try rfl
      case unionAll first second =>
        exact (leftOuterOnRowsWith_append_left predicate nullRight
          (evalPlan database first) (evalPlan database second)
          (evalPlan database right)).symm
  | groupCount key input =>
      cases input <;> try rfl
      case unionAll left right =>
        simp [unionDistribution, evalPlan, groupCountRows]
  | groupSum key measure input =>
      cases input <;> try rfl
      case unionAll left right =>
        simp [unionDistribution, evalPlan, groupSumRows]
  | _ => rfl

def predicatePushdown : Plan → Plan
  | .filter (.onLeft predicate) (.innerJoin left right) =>
      .innerJoin (.filter predicate left) right
  | plan => plan

theorem predicatePushdown_eval (database : Core.Database) (plan : Plan) :
    evalPlan database (predicatePushdown plan) = evalPlan database plan := by
  cases plan with
  | filter predicate input =>
      cases predicate <;> try rfl
      case onLeft predicate =>
        cases input <;> try rfl
        case innerJoin left right =>
          exact (whereRows_onLeft_joinRows predicate
            (evalPlan database left) (evalPlan database right)).symm
  | _ => rfl

def constantFolding : Plan → Plan
  | .filter predicate input => .filter (foldConstants predicate) input
  | plan => plan

theorem constantFolding_eval (database : Core.Database) (plan : Plan) :
    evalPlan database (constantFolding plan) = evalPlan database plan := by
  cases plan <;> try rfl
  case filter predicate input =>
    exact whereRows_foldConstants predicate (evalPlan database input)

def projectionElimination : Plan → Plan
  | .project .identity input => input
  | plan => plan

theorem projectionElimination_eval (database : Core.Database) (plan : Plan) :
    evalPlan database (projectionElimination plan) = evalPlan database plan := by
  cases plan <;> try rfl
  case project projection input =>
    cases projection <;> simp [projectionElimination, evalPlan, Projection.apply]
    exact (List.map_id (evalPlan database input)).symm

def filterFusion : Plan → Plan
  | .filter outer (.filter inner input) => .filter (.and inner outer) input
  | plan => plan

theorem filterFusion_eval (database : Core.Database) (plan : Plan) :
    evalPlan database (filterFusion plan) = evalPlan database plan := by
  cases plan with
  | filter outer input =>
      cases input with
      | filter inner nested =>
          exact (whereRows_fusion outer inner (evalPlan database nested)).symm
      | _ => rfl
  | _ => rfl

inductive Rewrite where
  | predicatePushdown
  | constantFolding
  | projectionElimination
  | filterFusion
  | unionDistribution
  deriving Repr, DecidableEq

def Rewrite.applyPlan : Rewrite → Plan → Plan
  | .predicatePushdown, plan => QuerySemantics.predicatePushdown plan
  | .constantFolding, plan => QuerySemantics.constantFolding plan
  | .projectionElimination, plan => QuerySemantics.projectionElimination plan
  | .filterFusion, plan => QuerySemantics.filterFusion plan
  | .unionDistribution, plan => QuerySemantics.unionDistribution plan

def Rewrite.apply (rewrite : Rewrite) (query : Select) : Select :=
  { query with plan := rewrite.applyPlan query.plan }

theorem Rewrite.applyPlan_eval (rewrite : Rewrite) (database : Core.Database)
    (plan : Plan) :
    evalPlan database (rewrite.applyPlan plan) = evalPlan database plan := by
  cases rewrite with
  | predicatePushdown => exact predicatePushdown_eval database plan
  | constantFolding => exact constantFolding_eval database plan
  | projectionElimination => exact projectionElimination_eval database plan
  | filterFusion => exact filterFusion_eval database plan
  | unionDistribution => exact unionDistribution_eval database plan

/-- Apply the local rewrites that are both semantics-preserving and
unconditionally non-increasing in the executable logical cost model.

Predicate pushdown needs a nonempty-right precondition, filter fusion can add
strict predicate evaluations, and join distribution can duplicate its right
input.  They remain available through `Rewrite.applyPlan`, but the live
bottom-up optimizer does not select them without a cost certificate. -/
def rewriteRoot (plan : Plan) : Plan :=
  projectionElimination (constantFolding plan)

theorem rewriteRoot_eval (database : Core.Database) (plan : Plan) :
    evalPlan database (rewriteRoot plan) = evalPlan database plan := by
  unfold rewriteRoot
  rw [projectionElimination_eval, constantFolding_eval]

/-- Bottom-up optimizer used by the live Core bridge. It visits every node and
then runs the certified cost-safe root pipeline. -/
def optimizePlan : Plan → Plan
  | .table name => .table name
  | .rows rows => .rows rows
  | .unionAll left right =>
      rewriteRoot (.unionAll (optimizePlan left) (optimizePlan right))
  | .intersectAll left right =>
      rewriteRoot (.intersectAll (optimizePlan left) (optimizePlan right))
  | .exceptAll left right =>
      rewriteRoot (.exceptAll (optimizePlan left) (optimizePlan right))
  | .distinct input => rewriteRoot (.distinct (optimizePlan input))
  | .filter predicate input =>
      rewriteRoot (.filter predicate (optimizePlan input))
  | .project projection input =>
      rewriteRoot (.project projection (optimizePlan input))
  | .innerJoin left right =>
      rewriteRoot (.innerJoin (optimizePlan left) (optimizePlan right))
  | .leftOuterJoin left right =>
      rewriteRoot (.leftOuterJoin (optimizePlan left) (optimizePlan right))
  | .leftOuterOn predicate left right =>
      rewriteRoot (.leftOuterOn predicate (optimizePlan left) (optimizePlan right))
  | .leftOuterOnWith predicate nullRight left right =>
      rewriteRoot (.leftOuterOnWith predicate nullRight
        (optimizePlan left) (optimizePlan right))
  | .groupCount key input => rewriteRoot (.groupCount key (optimizePlan input))
  | .groupSum key measure input =>
      rewriteRoot (.groupSum key measure (optimizePlan input))

theorem optimizePlan_eval (database : Core.Database) (plan : Plan) :
    evalPlan database (optimizePlan plan) = evalPlan database plan := by
  induction plan with
  | table | rows => rfl
  | unionAll left right leftInduction rightInduction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, leftInduction, rightInduction]
  | intersectAll left right leftInduction rightInduction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, leftInduction, rightInduction]
  | exceptAll left right leftInduction rightInduction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, leftInduction, rightInduction]
  | distinct input induction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, induction]
  | filter predicate input induction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, induction]
  | project projection input induction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, induction]
  | innerJoin left right leftInduction rightInduction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, leftInduction, rightInduction]
  | leftOuterJoin left right leftInduction rightInduction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, leftInduction, rightInduction]
  | leftOuterOn predicate left right leftInduction rightInduction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, leftInduction, rightInduction]
  | leftOuterOnWith predicate nullRight left right leftInduction rightInduction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, leftInduction, rightInduction]
  | groupCount key input induction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, induction]
  | groupSum key measure input induction =>
      rw [optimizePlan, rewriteRoot_eval]
      simp only [evalPlan, induction]

theorem rewrite_eval_eq (rewrite : Rewrite) (database : Core.Database)
    (query : Select) :
    eval database (rewrite.apply query) = eval database query := by
  unfold eval Rewrite.apply
  rw [rewrite.applyPlan_eval]

theorem rewrite_sound (rewrite : Rewrite) (database : Core.Database)
    (query : Select) :
    BagEq (eval database (rewrite.apply query)) (eval database query) := by
  rw [rewrite_eval_eq]
  exact List.Perm.refl _

/-- Ordered queries require list equality, not merely bag equivalence. The
three current rewrites preserve the pre-sort row sequence, so they satisfy the
stronger ordered obligation. -/
theorem rewrite_sound_ordered (rewrite : Rewrite) (database : Core.Database)
    (query : Select) (_ordered : query.orderBy ≠ []) :
    eval database (rewrite.apply query) = eval database query :=
  rewrite_eval_eq rewrite database query

def deMorgan : Predicate → Predicate
  | .not (.and left right) => .or (.not left) (.not right)
  | .not (.or left right) => .and (.not left) (.not right)
  | predicate => predicate

theorem deMorgan_eval (predicate : Predicate) (row : Row) :
    (deMorgan predicate).eval row = predicate.eval row := by
  cases predicate <;> try rfl
  case not predicate =>
    cases predicate <;> simp [deMorgan, Predicate.eval,
      Truth.deMorgan_and, Truth.deMorgan_or]

theorem not_equals_is_notEquals (column : ColumnPath) (value : Core.Value)
    (row : Row) :
    (Predicate.not (.equals column value)).eval row =
      (Predicate.notEquals column value).eval row := rfl

/-- Classical excluded middle is not a valid SQL rewrite: UNKNOWN survives
`p OR NOT p`, and WHERE consequently drops the row instead of retaining it. -/
theorem excludedMiddle_rewrite_unsound (row : Row) :
    whereRows
        (.or (.constant .unknown) (.not (.constant .unknown))) [row] ≠
      whereRows (.constant .true) [row] := by
  simp [whereRows, Predicate.eval, Truth.or, Truth.not]

/-- Pushing a right-side predicate through a left join is unsound. The
predicate sees NULL after the join and removes the row, while filtering the
right input first makes it empty and causes left-join NULL extension. -/
theorem outerJoin_pushdown_unsound (leftRow : Row) :
    whereRows
        (.onRight (.equals (.cell 0)
          (.integer ⟨5, by decide, by decide⟩)))
        (leftJoinRows [leftRow] [.values [.null]]) ≠
      leftJoinRows [leftRow]
        (whereRows (.equals (.cell 0)
          (.integer ⟨5, by decide, by decide⟩)) [.values [.null]]) := by
  simp [leftJoinRows, joinRows, whereRows, Predicate.eval, Row.lookup, sqlEquals,
    PhysicalQuery.sqlEquals]

end QuerySemantics
end SQLeanite
