import SQLeanite.RelationalAlgebra.CoreGroupOutputValueRefines

namespace SQLeanite
namespace RelationalAlgebra

/-- The executable cross left-outer join is exactly the typed outer relation:
an empty right bag contributes one NULL-shaped row per left occurrence, while
a nonempty right bag contributes the ordinary multiplicity product. -/
theorem joinedLeftOuterRows_eval (leftRows rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row)
    (leftExact : eval left = ofList leftRows)
    (rightExact : eval right = ofList rightRows) :
    eval (joinedLeftOuterRows rightRows left right) =
      ofList (QuerySemantics.leftJoinRows leftRows rightRows) := by
  cases rightRows with
  | nil =>
      apply KRelation.Relation.ext
      intro target
      cases target with
      | values cells =>
          simp [joinedLeftOuterRows, eval, leftOuterRelation, hasMatch,
            rightExact, QuerySemantics.leftJoinRows, ofList,
            listMultiplicity_leftNullRows]
      | joined leftTarget rightTarget =>
          have noMatch : hasMatch (supportDomain []) (fun _ _ => .true)
              (eval right) leftTarget = false := by
            rw [rightExact]
            rfl
          rw [show eval (joinedLeftOuterRows [] left right)
              (.joined leftTarget rightTarget) =
            if rightTarget = .values [] then eval left leftTarget else 0 by
              simp [joinedLeftOuterRows, eval, leftOuterRelation,
                noMatch]]
          rw [leftExact]
          simp [QuerySemantics.leftJoinRows, ofList,
            listMultiplicity_leftNullRows]
  | cons first rows =>
      apply KRelation.Relation.ext
      intro target
      cases target with
      | values cells =>
          simp [joinedLeftOuterRows, eval, QuerySemantics.leftJoinRows,
            ofList, listMultiplicity_joinRows]
      | joined leftTarget rightTarget =>
          have someMatch : hasMatch (supportDomain (first :: rows))
              (fun _ _ => .true) (eval right) leftTarget = true := by
            rw [rightExact]
            exact hasMatch_support_true first rows leftTarget
          rw [show eval (joinedLeftOuterRows (first :: rows) left right)
              (.joined leftTarget rightTarget) =
            eval left leftTarget * eval right rightTarget by
              simp [joinedLeftOuterRows, eval, leftOuterRelation,
                someMatch]]
          rw [leftExact, rightExact]
          simp [QuerySemantics.leftJoinRows, ofList,
            listMultiplicity_joinRows]

/-- The predicate-bearing executable left outer join agrees with the typed
bag semantics for every SQL truth value.  In particular, both `false` and
`unknown` produce the NULL-extended row when no right candidate is `true`,
and matching duplicates multiply their bag multiplicities. -/
theorem joinedLeftOuterOnWith_eval (predicate : QuerySemantics.Predicate)
    (nullRight : QuerySemantics.Row) (leftRows rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row)
    (leftExact : eval left = ofList leftRows)
    (rightExact : eval right = ofList rightRows) :
    eval (joinedLeftOuterOnWith predicate rightRows nullRight left right) =
      ofList (QuerySemantics.leftOuterOnRowsWith predicate nullRight
        leftRows rightRows) := by
  apply KRelation.Relation.ext
  intro target
  cases target with
  | values cells =>
      simp [joinedLeftOuterOnWith, eval, leftOuterRelation, ofList,
        listMultiplicity_leftOuterOnRowsWith]
  | joined leftTarget rightTarget =>
      rw [show eval (joinedLeftOuterOnWith predicate rightRows nullRight left right)
          (.joined leftTarget rightTarget) =
        if hasMatch (supportDomain rightRows)
            (fun leftRow rightRow =>
              predicate.eval (.joined leftRow rightRow))
            (eval right) leftTarget then
          if predicate.eval (.joined leftTarget rightTarget) = .true then
            eval left leftTarget * eval right rightTarget
          else 0
        else if rightTarget = nullRight then eval left leftTarget else 0 by
          rfl]
      rw [leftExact, rightExact, hasMatch_support]
      simp [ofList, listMultiplicity_leftOuterOnRowsWith]

theorem joinedLeftOuterOn_eval (predicate : QuerySemantics.Predicate)
    (leftRows rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row)
    (leftExact : eval left = ofList leftRows)
    (rightExact : eval right = ofList rightRows) :
    eval (joinedLeftOuterOn predicate rightRows left right) =
      ofList (QuerySemantics.leftOuterOnRows predicate leftRows rightRows) := by
  exact joinedLeftOuterOnWith_eval predicate (.values []) leftRows rightRows
    left right leftExact rightExact

/-- Translation of the existing optimizer plan into typed bag algebra. -/
def ofPlan? (database : Core.Database) : QuerySemantics.Plan → Option
    (Expr QuerySemantics.Row)
  | .table name => some (coreTable database name)
  | .rows rows => some (.relation (ofList rows))
  | .unionAll left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (.unionAll translatedLeft translatedRight)
  | .intersectAll left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (.intersect translatedLeft translatedRight)
  | .exceptAll left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (.except translatedLeft translatedRight)
  | .distinct input => do
      let translated ← ofPlan? database input
      some (.distinct translated)
  | .filter predicate input => do
      let translated ← ofPlan? database input
      some (.select predicate.eval translated)
  | .project projection input => do
      let translated ← ofPlan? database input
      some (.project inferInstance
        (supportDomain (QuerySemantics.evalPlan database input))
        projection.apply translated)
  | .innerJoin left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (joinedRows translatedLeft translatedRight)
  | .leftOuterJoin left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (joinedLeftOuterRows (QuerySemantics.evalPlan database right)
        translatedLeft translatedRight)
  | .leftOuterOn predicate left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (joinedLeftOuterOn predicate
        (QuerySemantics.evalPlan database right)
        translatedLeft translatedRight)
  | .leftOuterOnWith predicate nullRight left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (joinedLeftOuterOnWith predicate
        (QuerySemantics.evalPlan database right) nullRight
        translatedLeft translatedRight)
  | .groupCount key input => do
      let translated ← ofPlan? database input
      some (.groupCount inferInstance
        (supportDomain (QuerySemantics.evalPlan database input))
        key translated)
  | .groupSum key measure input => do
      let translated ← ofPlan? database input
      some (.groupSum inferInstance
        (supportDomain (QuerySemantics.evalPlan database input))
        key measure translated)

theorem ofPlan?_eval (database : Core.Database) :
    ∀ (plan : QuerySemantics.Plan) (translated : Expr QuerySemantics.Row),
      ofPlan? database plan = some translated →
      eval translated = ofList (QuerySemantics.evalPlan database plan)
  | .table name, translated, success => by
      simp only [ofPlan?, Option.some.injEq] at success
      subst translated
      rfl
  | .rows rows, translated, success => by
      simp only [ofPlan?, Option.some.injEq] at success
      subst translated
      rfl
  | .unionAll left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              rw [show eval (.unionAll translatedLeft translatedRight) =
                KRelation.unionAll (eval translatedLeft)
                  (eval translatedRight) by rfl]
              rw [ofPlan?_eval database left translatedLeft leftResult]
              rw [ofPlan?_eval database right translatedRight rightResult]
              rw [← ofList_append]
              rfl
  | .intersectAll left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              rw [show eval (.intersect translatedLeft translatedRight) =
                KRelation.intersect (eval translatedLeft)
                  (eval translatedRight) by rfl]
              rw [ofPlan?_eval database left translatedLeft leftResult]
              rw [ofPlan?_eval database right translatedRight rightResult]
              rw [← ofList_bagIntersect]
              rfl
  | .exceptAll left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              rw [show eval (.except translatedLeft translatedRight) =
                KRelation.except (eval translatedLeft)
                  (eval translatedRight) by rfl]
              rw [ofPlan?_eval database left translatedLeft leftResult]
              rw [ofPlan?_eval database right translatedRight rightResult]
              rw [← ofList_bagExcept]
              rfl
  | .distinct input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.distinct translatedInput) =
            KRelation.distinct (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [← ofList_deduplicate]
          rfl
  | .filter predicate input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.select predicate.eval translatedInput) =
            KRelation.select predicate.eval (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [← ofList_whereRows]
          rfl
  | .project projection input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.project inferInstance
              (supportDomain (QuerySemantics.evalPlan database input))
              projection.apply translatedInput) =
            KRelation.project
              (supportDomain (QuerySemantics.evalPlan database input)).values
              projection.apply (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [project_ofList]
          rfl
  | .innerJoin left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              rw [joinedRows_eval]
              rw [ofPlan?_eval database left translatedLeft leftResult]
              rw [ofPlan?_eval database right translatedRight rightResult]
              rw [← ofList_joinRows]
              rfl
  | .leftOuterJoin left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              exact joinedLeftOuterRows_eval
                (QuerySemantics.evalPlan database left)
                (QuerySemantics.evalPlan database right)
                translatedLeft translatedRight
                (ofPlan?_eval database left translatedLeft leftResult)
                (ofPlan?_eval database right translatedRight rightResult)
  | .leftOuterOn predicate left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              exact joinedLeftOuterOn_eval predicate
                (QuerySemantics.evalPlan database left)
                (QuerySemantics.evalPlan database right)
                translatedLeft translatedRight
                (ofPlan?_eval database left translatedLeft leftResult)
                (ofPlan?_eval database right translatedRight rightResult)
  | .leftOuterOnWith predicate nullRight left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              exact joinedLeftOuterOnWith_eval predicate nullRight
                (QuerySemantics.evalPlan database left)
                (QuerySemantics.evalPlan database right)
                translatedLeft translatedRight
                (ofPlan?_eval database left translatedLeft leftResult)
                (ofPlan?_eval database right translatedRight rightResult)
  | .groupCount key input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.groupCount inferInstance
              (supportDomain (QuerySemantics.evalPlan database input))
              key translatedInput) =
            KRelation.groupCount
              (supportDomain
                (QuerySemantics.evalPlan database input)).values
              key (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [← ofList_groupCountRows]
          rfl
  | .groupSum key measure input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.groupSum inferInstance
              (supportDomain (QuerySemantics.evalPlan database input))
              key measure translatedInput) =
            KRelation.groupSum
              (supportDomain
                (QuerySemantics.evalPlan database input)).values
              key measure (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [← ofList_groupSumRows]
          rfl

theorem select_product_left (predicate : Left → Truth)
    (left : Relation Left) (right : Relation Right) :
    KRelation.select (fun row : Left × Right => predicate row.1)
        (KRelation.join left right) =
      KRelation.join (KRelation.select predicate left) right := by
  apply KRelation.Relation.ext
  intro row
  by_cases passes : predicate row.1 = .true <;>
    simp [KRelation.select, KRelation.join, passes]

/-- Predicate pushdown through product, stated over the general algebra. -/
theorem selectProductLeft_eval (predicate : Left → Truth)
    (left : Expr Left) (right : Expr Right) :
    eval (.select (fun row : Left × Right => predicate row.1)
        (.product left right)) =
      eval (.product (.select predicate left) right) :=
  select_product_left predicate (eval left) (eval right)

theorem selectUnionAll_eval (predicate : Row → Truth)
    (left right : Expr Row) :
    eval (.select predicate (.unionAll left right)) =
      eval (.unionAll (.select predicate left) (.select predicate right)) :=
  KRelation.select_unionAll predicate (eval left) (eval right)

theorem productUnionAllLeft_eval (first second : Expr Left)
    (right : Expr Right) :
    eval (.product (.unionAll first second) right) =
      eval (.unionAll (.product first right) (.product second right)) :=
  KRelation.join_unionAll_left (eval first) (eval second) (eval right)

theorem productUnionAllRight_eval (left : Expr Left)
    (first second : Expr Right) :
    eval (.product left (.unionAll first second)) =
      eval (.unionAll (.product left first) (.product left second)) :=
  KRelation.join_unionAll_right (eval left) (eval first) (eval second)

theorem selectFusion_eval (first second : Row → Truth) (input : Expr Row) :
    eval (.select first (.select second input)) =
      eval (.select (fun row => Truth.and (first row) (second row)) input) := by
  apply KRelation.Relation.ext
  intro row
  cases firstResult : first row <;> cases secondResult : second row <;>
    simp [eval, KRelation.select, Truth.and, firstResult, secondResult]

theorem distinctIdempotent_eval (input : Expr Row) :
    eval (.distinct (.distinct input)) = eval (.distinct input) :=
  KRelation.distinct_idempotent (eval input)

def swapProduct (input : Expr (Left × Right)) : Expr (Right × Left) :=
  .rename (fun row => (row.2, row.1)) input

theorem swapProduct_eval (left : Expr Left) (right : Expr Right) :
    eval (swapProduct (.product left right)) = eval (.product right left) := by
  exact KRelation.swap_join (eval left) (eval right)

def reassociateProduct (input : Expr ((First × Second) × Third)) :
    Expr (First × (Second × Third)) :=
  .rename (fun row => ((row.1, row.2.1), row.2.2)) input

theorem reassociateProduct_eval (first : Expr First) (second : Expr Second)
    (third : Expr Third) :
    eval (reassociateProduct (.product (.product first second) third)) =
      eval (.product first (.product second third)) := by
  apply KRelation.Relation.ext
  intro row
  simp [reassociateProduct, eval, KRelation.join, Nat.mul_assoc]

theorem project_unionAll (decEq : DecidableEq Output) (domain : Domain Input)
    (projection : Input → Output) (left right : Expr Input) :
    eval (.project decEq domain projection (.unionAll left right)) =
      eval (.unionAll (.project decEq domain projection left)
        (.project decEq domain projection right)) := by
  let _ : DecidableEq Output := decEq
  exact KRelation.project_unionAll domain.values projection
    (eval left) (eval right)

theorem groupCountUnionAll_eval (decEq : DecidableEq Group)
    (domain : Domain Input) (key : Input → Group) (left right : Expr Input) :
    eval (.groupCount decEq domain key (.unionAll left right)) =
      eval (.unionAll (.groupCount decEq domain key left)
        (.groupCount decEq domain key right)) := by
  let _ : DecidableEq Group := decEq
  exact KRelation.groupCount_unionAll domain.values key (eval left) (eval right)

theorem groupSumUnionAll_eval (decEq : DecidableEq Group)
    (domain : Domain Input) (key : Input → Group) (measure : Input → Nat)
    (left right : Expr Input) :
    eval (.groupSum decEq domain key measure (.unionAll left right)) =
      eval (.unionAll (.groupSum decEq domain key measure left)
        (.groupSum decEq domain key measure right)) := by
  let _ : DecidableEq Group := decEq
  exact KRelation.groupSum_unionAll domain.values key measure
    (eval left) (eval right)

end RelationalAlgebra

end SQLeanite
