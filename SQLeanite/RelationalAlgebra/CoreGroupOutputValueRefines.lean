import SQLeanite.RelationalAlgebra.OfListWhereRows

namespace SQLeanite
namespace RelationalAlgebra

theorem coreGroup_outputValue_refines (query : Core.GroupQuery)
    (rows : List Core.Row) (group : List Core.Value)
    (output : Core.GroupOutput) (value : Core.Value)
    (success : query.outputValue rows group output = .ok value) :
    coreGroupOutputRefines query rows group output value := by
  cases output with
  | key position =>
      simp [Core.GroupQuery.outputValue] at success
      subst value
      rfl
  | countStar =>
      simp only [Core.GroupQuery.outputValue] at success
      cases counted : Core.countInteger (query.keyRows rows group).length with
      | error message =>
          simp [counted, bind, Functor.map, Except.map] at success
      | ok integer =>
          simp [counted, bind, Functor.map, Except.map] at success
          subst value
          simp [coreGroupOutputRefines, Core.countInteger_exact counted,
            coreGroup_keyRows_length_eq_keyCount]
  | countColumn column =>
      simp only [Core.GroupQuery.outputValue] at success
      cases counted : Core.countInteger ((query.keyRows rows group).countP
          fun row => row.value column != .null) with
      | error message =>
          simp [counted, bind, Functor.map, Except.map] at success
      | ok integer =>
          simp [counted, bind, Functor.map, Except.map] at success
          subst value
          simp [coreGroupOutputRefines, Core.countInteger_exact counted]
  | sumColumn column =>
      simp only [Core.GroupQuery.outputValue] at success
      cases extracted : Core.columnIntegers column
          (query.keyRows rows group) with
      | error message =>
          simpa [coreGroupOutputRefines, Core.sumColumn, extracted] using success
      | ok integers =>
          simp only [coreGroupOutputRefines, extracted]
          cases summed : Core.sumIntegers integers with
          | error message =>
              simp [Core.sumColumn, extracted, summed, bind, Functor.map,
                Except.bind, pure, Except.pure] at success
          | ok result =>
              cases result with
              | none =>
                  simp [Core.sumColumn, extracted, summed, bind, Functor.map,
                    Except.bind, pure, Except.pure] at success
                  subst value
                  exact (core_sumIntegers_none_iff integers).1 summed
              | some integer =>
                  simp [Core.sumColumn, extracted, summed, bind, Functor.map,
                    Except.bind, pure, Except.pure] at success
                  subst value
                  exact Core.sumIntegers_exact summed
  | averageColumn column =>
      simpa [Core.GroupQuery.outputValue, coreGroupOutputRefines] using success.symm
  | totalColumn column =>
      simpa [Core.GroupQuery.outputValue, coreGroupOutputRefines] using success.symm
  | minColumn column =>
      simp [Core.GroupQuery.outputValue] at success
      subst value
      rfl
  | maxColumn column =>
      simp [Core.GroupQuery.outputValue] at success
      subst value
      rfl

inductive Aligned (relation : Left → Right → Prop) :
    List Left → List Right → Prop where
  | nil : Aligned relation [] []
  | cons {left right lefts rights} : relation left right →
      Aligned relation lefts rights →
      Aligned relation (left :: lefts) (right :: rights)

/-- Arbitrary multi-output grouped tuples compose the per-output contracts in
the same order. -/
theorem coreGroup_evalOutputs_refines (query : Core.GroupQuery)
    (rows : List Core.Row) (group : List Core.Value)
    (outputs : List Core.GroupOutput) (result : List Core.Value)
    (success : query.evalOutputs rows group outputs = .ok result) :
    Aligned (coreGroupOutputRefines query rows group) outputs result := by
  induction outputs generalizing result with
  | nil =>
      simp [Core.GroupQuery.evalOutputs] at success
      subst result
      exact .nil
  | cons output outputs induction =>
      simp only [Core.GroupQuery.evalOutputs] at success
      cases head : query.outputValue rows group output with
      | error message => simp [head] at success
      | ok value =>
          simp only [head] at success
          cases tail : query.evalOutputs rows group outputs with
          | error message => simp [tail] at success
          | ok values =>
              simp [tail] at success
              subst result
              exact .cons (coreGroup_outputValue_refines query rows group
                output value head) (induction values tail)

theorem coreGroup_evalKeys_refines (query : Core.GroupQuery)
    (rows : List Core.Row) (groups : List (List Core.Value))
    (results : List (List Core.Value))
    (success : query.evalKeys rows groups = .ok results) :
    Aligned (fun group result =>
      Aligned (coreGroupOutputRefines query rows group)
        query.outputs result) groups results := by
  induction groups generalizing results with
  | nil =>
      simp [Core.GroupQuery.evalKeys] at success
      subst results
      exact .nil
  | cons group groups induction =>
      simp only [Core.GroupQuery.evalKeys] at success
      cases head : query.evalOutputs rows group query.outputs with
      | error message => simp [head] at success
      | ok result =>
          simp only [head] at success
          cases tail : query.evalKeys rows groups with
          | error message => simp [tail] at success
          | ok resultsTail =>
              simp [tail] at success
              subst results
              exact .cons
                (coreGroup_evalOutputs_refines query rows group query.outputs
                  result head)
                (induction resultsTail tail)

/-- End-to-end semantic certificate for every row and column returned by the
live grouped evaluator. -/
theorem coreGroup_eval_refines (query : Core.GroupQuery)
    (rows : List Core.Row) (results : List (List Core.Value))
    (success : query.eval rows = .ok results) :
    Aligned (fun group result =>
      Aligned (coreGroupOutputRefines query rows group)
        query.outputs result) (query.groupKeys rows) results := by
  exact coreGroup_evalKeys_refines query rows (query.groupKeys rows)
    results success

/-- The algebra base relation for a live verified Core table. -/
def coreTable (database : Core.Database) (name : String) :
    Expr QuerySemantics.Row :=
  .relation (ofList (QuerySemantics.tableRows database name))

/-- INNER JOIN is not primitive: it is SQL-TRUE selection over a product. -/
def innerJoin (predicate : Left → Right → Truth)
    (left : Expr Left) (right : Expr Right) : Expr (Left × Right) :=
  .select (fun row => predicate row.1 row.2) (.product left right)

theorem eval_innerJoin (predicate : Left → Right → Truth)
    (left : Expr Left) (right : Expr Right) :
    eval (innerJoin predicate left right) =
      KRelation.select (fun row => predicate row.1 row.2)
        (KRelation.join (eval left) (eval right)) := rfl

/-- POPL'10's cartesian-product primitive is the constant-true special case
of SQLeanite's derived inner join.  Stating the equality explicitly keeps the
parity claim independent of the choice of primitive algebra operators. -/
theorem innerJoin_true_eval (left : Expr Left) (right : Expr Right) :
    eval (innerJoin (fun _ _ => .true) left right) =
      eval (.product left right) := by
  apply KRelation.Relation.ext
  intro row
  simp [innerJoin, eval, KRelation.select]

/-- The two total maps and inverse laws needed for a typed column
permutation.  This small local structure avoids adding a library dependency
to the verified core. -/
structure Bijection (Input Output : Type) where
  forward : Input → Output
  backward : Output → Input
  leftInverse : ∀ input, backward (forward input) = input
  rightInverse : ∀ output, forward (backward output) = output

def Bijection.symm (equiv : Bijection Input Output) :
    Bijection Output Input where
  forward := equiv.backward
  backward := equiv.forward
  leftInverse := equiv.rightInverse
  rightInverse := equiv.leftInverse

/-- A bijective rename is a typed column/tuple permutation.  The executable
direction is the inverse map because relations are observed by output tuple;
the theorem records that no multiplicity is created or lost. -/
def permute (equiv : Bijection Input Output) (input : Expr Input) :
    Expr Output :=
  .rename equiv.backward input

theorem permute_eval (equiv : Bijection Input Output) (input : Expr Input)
    (row : Input) :
    eval (permute equiv input) (equiv.forward row) = eval input row := by
  change eval input (equiv.backward (equiv.forward row)) = eval input row
  rw [equiv.leftInverse]

/-- Applying a permutation and its inverse is denotationally the identity.
This is the explicit witness that `rename` subsumes POPL'10's permutation
operator rather than merely resembling it. -/
theorem permute_symm_eval (equiv : Bijection Input Output)
    (input : Expr Input) :
    eval (permute equiv.symm (permute equiv input)) = eval input := by
  apply KRelation.Relation.ext
  intro row
  change eval input (equiv.backward (equiv.forward row)) = eval input row
  rw [equiv.leftInverse]

/-- Mapping a bijection over an executable list *is* the algebra's permutation
of that list's relation.  Neither direction is a definitional unfolding: the
left side reorders concrete tuples, the right side relabels a multiplicity
function through the inverse map.

This is the lemma that makes the permutation parity claim a statement about the
shipped read path rather than about a standalone module.  A live projection
produces a list; `permute` acts on a denotation; without this bridge the two
never meet, and "we have a permutation primitive" says nothing about what the
executable computes. -/
theorem ofList_map_permute [DecidableEq Input] [DecidableEq Output]
    (equiv : Bijection Input Output) (rows : List Input) :
    ofList (rows.map equiv.forward) =
      eval (permute equiv (.relation (ofList rows))) := by
  apply KRelation.Relation.ext
  intro output
  show listMultiplicity output (rows.map equiv.forward) =
    listMultiplicity (equiv.backward output) rows
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.map_cons, listMultiplicity]
      rw [induction]
      congr 1
      by_cases hit : row = equiv.backward output
      · have forwardHit : equiv.forward row = output := by
          rw [hit, equiv.rightInverse]
        rw [if_pos hit, if_pos forwardHit]
      · have forwardMiss : equiv.forward row ≠ output := by
          intro equal
          exact hit (by rw [← equal, equiv.leftInverse])
        rw [if_neg hit, if_neg forwardMiss]

/-- Duplicate elimination commutes with a permutation.  A bijective relabelling
cannot merge two distinct tuples or split one, so `DISTINCT` is insensitive to
the column order it is applied in. -/
theorem distinct_permute (equiv : Bijection Input Output)
    (relation : Relation Input) :
    KRelation.distinct (eval (permute equiv (.relation relation))) =
      eval (permute equiv (.relation (KRelation.distinct relation))) := rfl

def joinedRows (left right : Expr QuerySemantics.Row) :
    Expr QuerySemantics.Row :=
  .embed (fun
    | .values _ => none
    | .joined leftRow rightRow => some (leftRow, rightRow))
    (.product left right)

theorem joinedRows_eval (left right : Expr QuerySemantics.Row) :
    eval (joinedRows left right) = joinedProduct (eval left) (eval right) := by
  apply KRelation.Relation.ext
  intro row
  cases row <;> rfl

def joinedLeftOuterRows (rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row) : Expr QuerySemantics.Row :=
  .embed (fun
    | .values _ => none
    | .joined leftRow rightRow => some (leftRow, rightRow))
    (.leftOuter inferInstance (supportDomain rightRows) (.values [])
      (fun _ _ => .true) left right)

/-- Predicate-bearing left outer join embedded back into the executable row
shape.  The predicate is evaluated on the joined row, so SQL `unknown` is a
non-match exactly as it is for `ON` in the executable semantics. -/
def joinedLeftOuterOnWith (predicate : QuerySemantics.Predicate)
    (rightRows : List QuerySemantics.Row) (nullRight : QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row) : Expr QuerySemantics.Row :=
  .embed (fun
    | .values _ => none
    | .joined leftRow rightRow => some (leftRow, rightRow))
    (.leftOuter inferInstance (supportDomain rightRows) nullRight
      (fun leftRow rightRow =>
        predicate.eval (.joined leftRow rightRow)) left right)

def joinedLeftOuterOn (predicate : QuerySemantics.Predicate)
    (rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row) : Expr QuerySemantics.Row :=
  joinedLeftOuterOnWith predicate rightRows (.values []) left right

theorem hasMatch_support (predicate : QuerySemantics.Predicate)
    (rows : List QuerySemantics.Row) (left : QuerySemantics.Row) :
    hasMatch (supportDomain rows)
        (fun leftRow rightRow =>
          predicate.eval (.joined leftRow rightRow))
        (ofList rows) left =
      rows.any (fun rightRow =>
        predicate.eval (.joined left rightRow) == .true) := by
  apply Bool.eq_iff_iff.mpr
  simp [hasMatch, supportDomain, Core.mem_deduplicate, ofList,
    listMultiplicity_eq_zero_iff]
  constructor
  · rintro ⟨row, member, passes, _⟩
    exact ⟨row, member, passes⟩
  · rintro ⟨row, member, passes⟩
    exact ⟨row, member, passes, member⟩

private theorem leftOuterMatches_isEmpty
    (predicate : QuerySemantics.Predicate)
    (left : QuerySemantics.Row) (rows : List QuerySemantics.Row) :
    ((rows.map fun rightRow =>
        QuerySemantics.Row.joined left rightRow).filter
      (fun row => predicate.eval row == .true)).isEmpty =
      !(rows.any fun rightRow =>
        predicate.eval (.joined left rightRow) == .true) := by
  apply Bool.eq_iff_iff.mpr
  simp [List.isEmpty_iff]

private theorem listMultiplicity_leftOuterForRowsWith
    (predicate : QuerySemantics.Predicate)
    (nullRight left : QuerySemantics.Row) (rows : List QuerySemantics.Row)
    (target : QuerySemantics.Row) :
    listMultiplicity target
        (QuerySemantics.leftOuterForRowsWith predicate nullRight left rows) =
      match target with
      | .values _ => 0
      | .joined leftTarget rightTarget =>
          if left = leftTarget then
            if rows.any (fun rightRow =>
                predicate.eval (.joined left rightRow) == .true) then
              if predicate.eval (.joined leftTarget rightTarget) = .true then
                listMultiplicity rightTarget rows
              else 0
            else if rightTarget = nullRight then 1 else 0
          else 0 := by
  cases target with
  | values cells =>
      simp only [QuerySemantics.leftOuterForRowsWith]
      rw [leftOuterMatches_isEmpty]
      cases anyResult : rows.any (fun rightRow =>
          predicate.eval (.joined left rightRow) == .true) <;>
        simp [anyResult, listMultiplicity_filter,
          listMultiplicity_values_map_joined, listMultiplicity]
  | joined leftTarget rightTarget =>
      by_cases leftEqual : left = leftTarget
      · subst leftTarget
        simp only [QuerySemantics.leftOuterForRowsWith]
        rw [leftOuterMatches_isEmpty]
        cases anyResult : rows.any (fun rightRow =>
            predicate.eval (.joined left rightRow) == .true) with
        | false =>
            by_cases rightEqual : rightTarget = nullRight
            · subst rightTarget
              simp [anyResult, listMultiplicity]
            · have reverse : nullRight ≠ rightTarget :=
                Ne.symm rightEqual
              simp [anyResult, listMultiplicity, rightEqual, reverse]
        | true =>
          simp [anyResult, listMultiplicity_filter,
              listMultiplicity_joined_map_joined, listMultiplicity]
      · simp only [QuerySemantics.leftOuterForRowsWith]
        rw [leftOuterMatches_isEmpty]
        cases anyResult : rows.any (fun rightRow =>
            predicate.eval (.joined left rightRow) == .true) <;>
          simp [anyResult, listMultiplicity_filter,
            listMultiplicity_joined_map_joined, listMultiplicity, leftEqual]

theorem listMultiplicity_leftOuterOnRowsWith
    (predicate : QuerySemantics.Predicate)
    (nullRight : QuerySemantics.Row)
    (leftRows rightRows : List QuerySemantics.Row)
    (target : QuerySemantics.Row) :
    listMultiplicity target
        (QuerySemantics.leftOuterOnRowsWith predicate nullRight leftRows rightRows) =
      match target with
      | .values _ => 0
      | .joined leftTarget rightTarget =>
          if rightRows.any (fun rightRow =>
              predicate.eval (.joined leftTarget rightRow) == .true) then
            if predicate.eval (.joined leftTarget rightTarget) = .true then
              listMultiplicity leftTarget leftRows *
                listMultiplicity rightTarget rightRows
            else 0
          else if rightTarget = nullRight then
            listMultiplicity leftTarget leftRows
          else 0 := by
  induction leftRows with
  | nil =>
      cases target <;>
        simp [QuerySemantics.leftOuterOnRowsWith, listMultiplicity]
  | cons row rows induction =>
      rw [show QuerySemantics.leftOuterOnRowsWith predicate nullRight
          (row :: rows) rightRows =
        QuerySemantics.leftOuterForRowsWith predicate nullRight row rightRows ++
          QuerySemantics.leftOuterOnRowsWith predicate nullRight rows rightRows by rfl]
      rw [listMultiplicity_append,
        listMultiplicity_leftOuterForRowsWith, induction]
      cases target with
      | values cells => rfl
      | joined leftTarget rightTarget =>
          by_cases leftEqual : row = leftTarget
          · subst leftTarget
            cases anyResult : rightRows.any (fun rightRow =>
                predicate.eval (.joined row rightRow) == .true) with
            | false =>
                by_cases rightEqual : rightTarget = nullRight
                · subst rightTarget
                  simp [anyResult, listMultiplicity]
                · have reverse : nullRight ≠ rightTarget :=
                    Ne.symm rightEqual
                  simp [anyResult, rightEqual, reverse, listMultiplicity]
            | true =>
                by_cases passes :
                    predicate.eval (.joined row rightTarget) = .true <;>
                  simp [anyResult, passes, listMultiplicity, Nat.add_mul]
          · simp [leftEqual, listMultiplicity]

theorem listMultiplicity_leftOuterOnRows
    (predicate : QuerySemantics.Predicate)
    (leftRows rightRows : List QuerySemantics.Row)
    (target : QuerySemantics.Row) :
    listMultiplicity target
        (QuerySemantics.leftOuterOnRows predicate leftRows rightRows) =
      match target with
      | .values _ => 0
      | .joined leftTarget rightTarget =>
          if rightRows.any (fun rightRow =>
              predicate.eval (.joined leftTarget rightRow) == .true) then
            if predicate.eval (.joined leftTarget rightTarget) = .true then
              listMultiplicity leftTarget leftRows *
                listMultiplicity rightTarget rightRows
            else 0
          else if rightTarget = .values [] then
            listMultiplicity leftTarget leftRows
          else 0 := by
  simpa [QuerySemantics.leftOuterOnRows] using
    listMultiplicity_leftOuterOnRowsWith predicate (.values [])
      leftRows rightRows target

theorem hasMatch_support_true (first : QuerySemantics.Row)
    (rows : List QuerySemantics.Row) (left : QuerySemantics.Row) :
    hasMatch (supportDomain (first :: rows)) (fun _ _ => .true)
      (ofList (first :: rows)) left = true := by
  apply List.any_eq_true.mpr
  refine ⟨first, ?_, ?_⟩
  · exact (Core.mem_deduplicate first (first :: rows)).2 (by simp)
  · simp [ofList, multiplicity_nonzero_member first (first :: rows) (by simp)]

theorem listMultiplicity_leftNullRows
    (target : QuerySemantics.Row) (left : List QuerySemantics.Row) :
    listMultiplicity target
        (left.map fun row => QuerySemantics.Row.joined row (.values [])) =
      match target with
      | .values _ => 0
      | .joined leftTarget rightTarget =>
          if rightTarget = .values [] then listMultiplicity leftTarget left
          else 0 := by
  induction left with
  | nil => cases target <;> simp [listMultiplicity]
  | cons row rows induction =>
      cases target with
      | values cells => simp [listMultiplicity, induction]
      | joined leftTarget rightTarget =>
          by_cases rightEqual : rightTarget = .values []
          · subst rightTarget
            simp [listMultiplicity, induction]
          · have reverse : QuerySemantics.Row.values [] ≠ rightTarget :=
              Ne.symm rightEqual
            simp [listMultiplicity, induction, rightEqual, reverse]

end RelationalAlgebra

end SQLeanite
