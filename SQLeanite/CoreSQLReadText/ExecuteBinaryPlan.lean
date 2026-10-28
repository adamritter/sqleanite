import SQLeanite.CoreSQL.CreateTableAsCommands
import SQLeanite.CoreSQLReadText.OneResult

namespace SQLeanite
namespace CoreSQLReadText

/-- A two-arm compound plan expressed only in live Core commands. -/
def executeBinaryPlan (state : Core.State) (left : Core.Command)
    (operation : CompoundOp) (right : Core.Command) :
    Except String (Core.State × List Core.Result) := do
  let (leftNext, leftResult) ← Core.execute state left
  let (rightNext, rightResult) ← Core.execute leftNext right
  unless readWidth left = readWidth right do
    throw (CoreCompound.widthError operation)
  return (rightNext, [Core.Result.mk (CoreSQL.combineRows operation
    leftResult.rows rightResult.rows) 0])

/-- Execution-independent translation of one binary compound SELECT.  Both
arms may use every base read form covered above. -/
inductive TranslatedBinaryCompound (state : Core.State) :
    Select → Core.Command → CompoundOp → Core.Command → Prop where
  | intro (select arm : Select) (left right : Core.Command)
      (operation : CompoundOp)
      (compounds : select.compounds = #[(operation, arm)])
      (noOuterOrder : select.orderBy = #[])
      (noOuterLimit : select.limit = none) (noOuterOffset : select.offset = 0)
      (armNoCompounds : arm.compounds = #[])
      (leftTranslated : TranslatedRead state
        (.select { select with compounds := #[] }) left)
      (rightTranslated : TranslatedRead state (.select arm) right) :
      TranslatedBinaryCompound state select left operation right

private theorem binaryCompoundHeight_eq_two (select arm : Select)
    (operation : CompoundOp)
    (compounds : select.compounds = #[(operation, arm)])
    (armNoCompounds : arm.compounds = #[]) : select.compoundHeight = 2 := by
  cases select
  cases arm
  simp_all [Select.compoundHeight, selectCompoundListHeight]

theorem executeStatement_binary_eq_core
    {state : Core.State} {select : Select} {left right : Core.Command}
    {operation : CompoundOp}
    (translated : TranslatedBinaryCompound state select left operation right) :
    CoreSQL.executeStatement state (.select select) =
      executeBinaryPlan state left operation right := by
  cases translated with
  | intro arm left right operation compounds noOuterOrder noOuterLimit
      noOuterOffset armNoCompounds leftTranslated rightTranslated =>
      have height := binaryCompoundHeight_eq_two select arm operation compounds
        armNoCompounds
      have leftColumns := translatedRead_columnsCollation_false leftTranslated
      have rightColumns := translatedRead_columnsCollation_false rightTranslated
      have leftDeclared := translatedRead_columnsDeclaredCollation_false leftTranslated
      have rightDeclared := translatedRead_columnsDeclaredCollation_false rightTranslated
      have leftSource := translatedRead_sources_nonempty leftTranslated
      have rightSource := translatedRead_sources_nonempty rightTranslated
      have noCollation : CoreSQL.requiresCompoundCollation select = false := by
        simp [CoreSQL.requiresCompoundCollation, height, CoreSQL.resultCollationFuel,
          CoreSQL.declaredResultCollationFuel, compounds, leftColumns, rightColumns, leftDeclared, rightDeclared, leftSource, rightSource, armNoCompounds]
      have leftBase := executeSelectBaseComplete_eq_core leftTranslated
      have rightBase := executeSelectBaseComplete_eq_core rightTranslated
      have armBase : { arm with compounds := #[] } = arm := by
        cases arm
        simp_all
      have rightFuel : CoreSQL.executeSelectFuel 1 state arm =
          selectExecution (readWidth right) (Core.execute state right) := by
        simp [CoreSQL.executeSelectFuel, CoreSQL.requiresCompoundCollation, armNoCompounds, armBase, rightBase,
          bind, Functor.map, Except.bind, pure, Except.pure, pure]
        cases execution : Core.execute state right <;>
          simp [execution, selectExecution,
            CoreSQL.executeSelectFuel.executeArms]
      simp only [CoreSQL.executeStatement, CoreSQL.executeSelect, height,
        CoreSQL.executeSelectFuel, noCollation, Bool.false_eq_true, ↓reduceIte]
      rw [leftBase]
      simp [compounds, noOuterOrder, noOuterLimit, noOuterOffset,
        executeBinaryPlan, selectExecution, bind, Functor.map,
        Except.bind, pure, Except.pure, pure]
      cases leftExecution : Core.execute state left with
      | error message => simp [leftExecution, selectExecution]
      | ok leftOutcome =>
          rcases leftOutcome with ⟨leftNext, leftResult⟩
          have leftUnchanged : leftNext = state :=
            core_read_state_eq leftTranslated leftExecution
          subst leftNext
          simp [leftExecution, armNoCompounds, selectExecution]
          simp only [CoreSQL.executeSelectFuel.executeArms]
          rw [rightFuel]
          cases rightExecution : Core.execute state right with
          | error message =>
              simp [rightExecution, selectExecution,
                CoreSQL.executeSelectFuel.executeArms, bind, Functor.map,
                Except.bind, pure, Except.pure, pure] <;> rfl
          | ok rightOutcome =>
              rcases rightOutcome with ⟨rightNext, rightResult⟩
              by_cases widths : readWidth left = readWidth right
              · simp [rightExecution, selectExecution,
                  CoreSQL.executeSelectFuel.executeArms,
                  CoreOptimizerBridge.optimizeCompoundOp_eq, bind, Functor.map,
                  Except.bind, pure, Except.pure, widths] <;> rfl
              · simp [rightExecution, selectExecution,
                  CoreSQL.executeSelectFuel.executeArms,
                  CoreOptimizerBridge.optimizeCompoundOp_eq, bind, Functor.map,
                  Except.bind, pure, Except.pure, widths] <;> rfl

/-- A recursively nested compound read whose leaves are live Core read
commands.  The shape deliberately mirrors SQLite's left-to-right compound
evaluation while retaining a separate plan for every recursively nested arm. -/
inductive CompoundReadPlan where
  | node (base : Core.Command)
      (arms : List (CompoundOp × CompoundReadPlan))

mutual
  /-- Execution-independent translation of every compound arm.  Unlike the
  former binary certificate, this relation has no bound on nesting or on the
  number of arms. -/
  inductive TranslatedCompoundRead (state : Core.State) :
      Select → CompoundReadPlan → Prop where
    | node (select : Select) (base : Core.Command)
        (syntaxArms : List (CompoundOp × Select))
        (planArms : List (CompoundOp × CompoundReadPlan))
        (shape : (select.compounds.isEmpty ||
          (select.orderBy.isEmpty && select.limit.isNone &&
            decide (select.offset = 0))) = true)
        (syntaxEq : select.compounds.toList = syntaxArms)
        (baseTranslated : TranslatedRead state
          (.select { select with compounds := #[] }) base)
        (armsTranslated : TranslatedCompoundReadArms state syntaxArms planArms) :
        TranslatedCompoundRead state select (.node base planArms)

  /-- Pointwise recursive translation of the ordered compound tail. -/
  inductive TranslatedCompoundReadArms (state : Core.State) :
      List (CompoundOp × Select) →
        List (CompoundOp × CompoundReadPlan) → Prop where
    | nil : TranslatedCompoundReadArms state [] []
    | cons (operation : CompoundOp) (arm : Select)
        (plan : CompoundReadPlan)
        (syntaxArms : List (CompoundOp × Select))
        (planArms : List (CompoundOp × CompoundReadPlan))
        (head : TranslatedCompoundRead state arm plan)
        (tail : TranslatedCompoundReadArms state syntaxArms planArms) :
        TranslatedCompoundReadArms state
          ((operation, arm) :: syntaxArms)
          ((operation, plan) :: planArms)
end

theorem translatedCompound_resultCollation_false (fuel : Nat) {state : Core.State}
    {select : Select} {plan : CompoundReadPlan}
    (translated : TranslatedCompoundRead state select plan) :
    CoreSQL.resultCollationFuel fuel select = false := by
  induction fuel generalizing select plan with
  | zero => rfl
  | succ fuel ihFuel =>
      cases translated with
      | node select base syntaxArms planArms shape syntaxEq baseTranslated armsTranslated =>
          have head := translatedRead_columnsCollation_false baseTranslated
          have source := translatedRead_sources_nonempty baseTranslated
          let rec armsDefault {syntaxTail : List (CompoundOp × Select)}
              {planTail : List (CompoundOp × CompoundReadPlan)}
              (valid : TranslatedCompoundReadArms state syntaxTail planTail) :
              ∀ entry ∈ syntaxTail, CoreSQL.resultCollationFuel fuel entry.2 = false := by
            cases valid with
            | nil => simp
            | cons operation arm plan syntaxRest planRest head tail =>
                intro entry member
                rcases List.mem_cons.mp member with rfl | member
                · exact ihFuel head
                · exact armsDefault tail entry member
          simp only [CoreSQL.resultCollationFuel, head, source, Bool.false_and, Bool.false_or, ← Array.any_toList,
            syntaxEq, List.any_eq_false]
          intro entry member
          rw [armsDefault armsTranslated entry member]
          decide

theorem translatedCompound_declaredResultCollation_false (fuel : Nat) {state : Core.State}
    {select : Select} {plan : CompoundReadPlan}
    (translated : TranslatedCompoundRead state select plan) :
    CoreSQL.declaredResultCollationFuel fuel select = false := by
  induction fuel generalizing select plan with
  | zero => rfl
  | succ fuel ihFuel =>
      cases translated with
      | node select base syntaxArms planArms shape syntaxEq baseTranslated armsTranslated =>
          have head := translatedRead_columnsDeclaredCollation_false baseTranslated
          have source := translatedRead_sources_nonempty baseTranslated
          let rec armsDefault {syntaxTail : List (CompoundOp × Select)}
              {planTail : List (CompoundOp × CompoundReadPlan)}
              (valid : TranslatedCompoundReadArms state syntaxTail planTail) :
              ∀ entry ∈ syntaxTail, CoreSQL.declaredResultCollationFuel fuel entry.2 = false := by
            cases valid with
            | nil => simp
            | cons operation arm plan syntaxRest planRest head tail =>
                intro entry member
                rcases List.mem_cons.mp member with rfl | member
                · exact ihFuel head
                · exact armsDefault tail entry member
          simp only [CoreSQL.declaredResultCollationFuel, head, source, Bool.false_and, Bool.false_or, ← Array.any_toList,
            syntaxEq, List.any_eq_false]
          intro entry member
          rw [armsDefault armsTranslated entry member]
          decide

mutual
  /-- Independent bag-semantics postcondition for a recursively nested
  compound plan.  Every leaf must satisfy its existing relational denotation;
  only the duplicate-sensitive compound operator combines their rows. -/
  inductive CompoundReadPlan.Refines (database : Core.Database) :
      CompoundReadPlan → List (List Core.Value) → Nat → Prop where
    | node (base : Core.Command)
        (arms : List (CompoundOp × CompoundReadPlan))
        (baseResult : Core.Result) (rows : List (List Core.Value)) (width : Nat)
        (baseRefines : ReadRefines database base baseResult)
        (tailRefines : CompoundReadArmsRefine database arms
          baseResult.rows (readWidth base) rows width) :
        CompoundReadPlan.Refines database (.node base arms) rows width

  /-- Left-to-right bag fold for a compound tail, including SQLite's explicit
  equal-column-count side condition. -/
  inductive CompoundReadArmsRefine (database : Core.Database) :
      List (CompoundOp × CompoundReadPlan) →
        List (List Core.Value) → Nat →
          List (List Core.Value) → Nat → Prop where
    | nil (rows : List (List Core.Value)) (width : Nat) :
        CompoundReadArmsRefine database [] rows width rows width
    | cons (operation : CompoundOp) (plan : CompoundReadPlan)
        (plans : List (CompoundOp × CompoundReadPlan))
        (currentRows armRows finalRows : List (List Core.Value))
        (width armWidth finalWidth : Nat)
        (head : CompoundReadPlan.Refines database plan armRows armWidth)
        (sameWidth : width = armWidth)
        (independent : RelationalAlgebra.ofList
            ((CoreSQL.combineRows operation currentRows armRows).map Core.distinctRowKey) =
          CoreCompound.denotation operation
            (RelationalAlgebra.ofList (currentRows.map Core.distinctRowKey))
            (RelationalAlgebra.ofList (armRows.map Core.distinctRowKey)))
        (tail : CompoundReadArmsRefine database plans
          (CoreSQL.combineRows operation currentRows armRows)
          width finalRows finalWidth) :
        CompoundReadArmsRefine database ((operation, plan) :: plans)
          currentRows width finalRows finalWidth
end

/-- Every successful recursively nested live compound SELECT is read-only and
refines the independent bag fold of the denotations of all of its leaves. -/
theorem executeSelectFuel_compound_refines :
    ∀ (fuel : Nat) {state : Core.State} {select : Select}
      {plan : CompoundReadPlan} {outcome : CoreSQL.SelectExecution},
      TranslatedCompoundRead state select plan →
      CoreSQL.executeSelectFuel fuel state select = .ok outcome →
      outcome.state = state ∧
        plan.Refines state.database outcome.result.rows outcome.width := by
  intro fuel
  induction fuel with
  | zero =>
      intro state select plan outcome translated success
      simp [CoreSQL.executeSelectFuel] at success
  | succ fuel induction =>
      intro state select plan outcome translated success
      have noCollation : CoreSQL.requiresCompoundCollation select = false := by
        simp [CoreSQL.requiresCompoundCollation, translatedCompound_resultCollation_false select.compoundHeight translated,
          translatedCompound_declaredResultCollation_false select.compoundHeight translated]
      cases translated with
      | node select base syntaxArms planArms shape syntaxEq baseTranslated
          armsTranslated =>
        have baseExecution := executeSelectBaseComplete_eq_core baseTranslated
        simp only [CoreSQL.executeSelectFuel, noCollation, Bool.false_eq_true, ↓reduceIte]
          at success
        simp only [shape, Bool.true_eq, ↓reduceIte] at success
        rw [baseExecution] at success
        cases execution : Core.execute state base with
        | error message =>
            simp [execution, selectExecution, bind, Functor.map, Except.bind,
              pure, Except.pure, pure] at success
        | ok baseOutcome =>
            rcases baseOutcome with ⟨baseNext, baseResult⟩
            have baseUnchanged : baseNext = state :=
              core_read_state_eq baseTranslated execution
            subst baseNext
            simp [execution, selectExecution, syntaxEq] at success
            let rec armsRefine
                {syntaxTail : List (CompoundOp × Select)}
                {planTail : List (CompoundOp × CompoundReadPlan)}
                (translatedTail : TranslatedCompoundReadArms state
                  syntaxTail planTail)
                {current final : CoreSQL.SelectExecution}
                (currentState : current.state = state)
                (tailSuccess :
                  CoreSQL.executeSelectFuel.executeArms fuel current syntaxTail =
                    .ok final) :
                  final.state = state ∧
                    CompoundReadArmsRefine state.database planTail
                      current.result.rows current.width
                      final.result.rows final.width := by
              cases translatedTail with
              | nil =>
                  simp [CoreSQL.executeSelectFuel.executeArms] at tailSuccess
                  subst final
                  exact ⟨currentState, .nil _ _⟩
              | cons operation arm armPlan syntaxRest planRest head tail =>
                  rcases current with ⟨currentStateValue, currentResult,
                    currentWidth⟩
                  simp only at currentState
                  subst currentStateValue
                  simp only [CoreSQL.executeSelectFuel.executeArms] at tailSuccess
                  cases armExecution : CoreSQL.executeSelectFuel fuel state arm with
                  | error message =>
                      rw [armExecution] at tailSuccess
                      simp [bind, Functor.map, Except.bind] at tailSuccess
                  | ok armOutcome =>
                      have armRefines := induction head armExecution
                      rcases armRefines with ⟨armState, armRefines⟩
                      by_cases sameWidth : currentWidth = armOutcome.width
                      · subst currentWidth
                        let combined : CoreSQL.SelectExecution := {
                          state := armOutcome.state
                          result := Core.Result.mk (CoreSQL.combineRows operation
                            currentResult.rows armOutcome.result.rows) 0
                          width := armOutcome.width }
                        have combinedState : combined.state = state := armState
                        have restSuccess :
                            CoreSQL.executeSelectFuel.executeArms fuel combined
                              syntaxRest = .ok final := by
                          rw [armExecution] at tailSuccess
                          simpa [combined,
                            CoreOptimizerBridge.optimizeCompoundOp_eq,
                            bind, Functor.map, Except.bind, pure, Except.pure, pure]
                            using tailSuccess
                        have tailRefines := armsRefine tail combinedState restSuccess
                        exact ⟨tailRefines.1, .cons operation armPlan
                          planRest
                          currentResult.rows armOutcome.result.rows
                          final.result.rows armOutcome.width armOutcome.width
                          final.width armRefines rfl
                          (CoreSQL.combineRows_denotes operation currentResult.rows
                            armOutcome.result.rows) tailRefines.2⟩
                      · rw [armExecution] at tailSuccess
                        simp [sameWidth, bind, Functor.map, Except.bind]
                          at tailSuccess
            have baseTailSuccess :
                CoreSQL.executeSelectFuel.executeArms fuel
                  ⟨state, baseResult, readWidth base⟩ syntaxArms =
                    .ok outcome := by
              simpa [bind, Functor.map, Except.bind, pure, Except.pure, pure]
                using success
            have folded := armsRefine armsTranslated rfl baseTailSuccess
            exact ⟨folded.1, .node base planArms baseResult
              outcome.result.rows outcome.width
              (core_read_refines baseTranslated execution) folded.2⟩

theorem compoundHeight_eq_one (select : Select)
    (noCompounds : select.compounds = #[]) : select.compoundHeight = 1 := by
  rw [show select.compoundHeight =
    selectCompoundListHeight select.compounds.toList + 1 by
      cases select
      rfl]
  rw [noCompounds]
  rfl

end CoreSQLReadText

end SQLeanite
