import SQLeanite.CoreSQLText
import SQLeanite.CoreReadSemantics

namespace SQLeanite
namespace CoreSQLReadText

private def oneResult
    (execution : Except String (Core.State × Core.Result)) :
    Except String (Core.State × List Core.Result) :=
  (fun outcome => (outcome.1, [outcome.2])) <$> execution

/-- The non-aggregate single-table SELECT translation admitted by the Core.
Every premise is a syntax or translation equation; no query result appears in
the relation. -/
inductive TranslatedRead (state : Core.State) :
    Statement → Core.Command → Prop where
  | query (select : Select) (source : TableRef) (stored : Core.Table)
      (predicate : Option Core.Predicate) (columns : List Nat)
      (ordering : List (Nat × Bool))
      (noCompounds : select.compounds = #[])
      (oneSource : select.sources = #[source])
      (noGroups : select.groupBy = #[])
      (noHaving : select.having = none) (noOffset : select.offset = 0)
      (plainSource : source.subquerySql = none ∧ source.joinOn = none)
      (found : state.database.findTable?
        (CoreSQL.canonical source.name) = some stored)
      (predicateTranslated : select.where_.mapM
        (CoreSQL.predicate stored.schema) = .ok predicate)
      (notCount : CoreSQL.countTarget? stored.schema select.columns.toList =
        .ok none)
      (notSum : CoreSQL.sumColumn? stored.schema select.columns.toList =
        .ok none)
      (notExtreme : CoreSQL.extremeColumn? stored.schema
        select.columns.toList = .ok none)
      (projectionTranslated : CoreSQL.projection stored.schema
        select.columns.toList = .ok columns)
      (orderingTranslated : CoreSQL.orderBy stored.schema
        select.orderBy.toList = .ok ordering) :
      TranslatedRead state (.select select)
        (.query (CoreSQL.canonical source.name) {
          columns
          predicate
          orderBy := ordering
          limit := select.limit
          distinct := select.distinct })

theorem executeStatement_eq_core
    {state : Core.State} {statement : Statement} {command : Core.Command}
    (translated : TranslatedRead state statement command) :
    CoreSQL.executeStatement state statement =
      oneResult (Core.execute state command) := by
  cases translated with
  | query select source stored predicate columns ordering noCompounds oneSource
      noGroups noHaving noOffset plainSource found predicateTranslated
      notCount notSum notExtreme projectionTranslated orderingTranslated =>
      have height : select.compoundHeight = 1 := by
        rw [show select.compoundHeight =
          selectCompoundListHeight select.compounds.toList + 1 by
            cases select
            rfl]
        rw [noCompounds]
        rfl
      simp [CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.executeSelectBase, height,
        noCompounds,
        oneSource, noGroups, noHaving, noOffset, plainSource, found,
        predicateTranslated, notCount, notSum, notExtreme,
        projectionTranslated, orderingTranslated, oneResult,
        Except.instMonad, Except.bind, Except.pure, pure]
      cases execution : Core.execute state
          (.query (CoreSQL.canonical source.name) {
            columns
            predicate
            orderBy := ordering
            limit := select.limit
            distinct := select.distinct }) with
      | error message =>
          simp only [Except.map]
      | ok outcome =>
          rcases outcome with ⟨actualNext, actualResult⟩
          simp only [CoreSQL.executeSelectFuel.executeArms, Except.map]

inductive SupportedReadText (state : Core.State) (text : String)
    (command : Core.Command) : Prop where
  | intro (statement : Statement)
      (parsed : parse text = .ok #[statement])
      (translated : TranslatedRead state statement command) :
      SupportedReadText state text command

theorem execute_eq_core
    {state : Core.State} {text : String} {command : Core.Command}
    (supported : SupportedReadText state text command) :
    CoreSQL.execute state text = oneResult (Core.execute state command) := by
  rcases supported with ⟨statement, parsed, translated⟩
  simp only [CoreSQL.execute, parsed, Except.instMonad, Except.bind,
    CoreSQL.runStatements]
  rw [executeStatement_eq_core translated]
  unfold oneResult
  cases Core.execute state command <;> rfl

theorem core_success_of_execute
    {state next : Core.State} {text : String} {command : Core.Command}
    {result : Core.Result}
    (supported : SupportedReadText state text command)
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    Core.execute state command = .ok (next, result) := by
  have mapped : oneResult (Core.execute state command) =
      .ok (next, [result]) := (execute_eq_core supported).symm.trans success
  unfold oneResult at mapped
  cases execution : Core.execute state command with
  | error message =>
      rw [execution] at mapped
      change (Except.error message :
        Except String (Core.State × List Core.Result)) =
          .ok (next, [result]) at mapped
      cases mapped
  | ok outcome =>
      rcases outcome with ⟨actualNext, actualResult⟩
      rw [execution] at mapped
      change Except.ok (actualNext, [actualResult]) =
        Except.ok (next, [result]) at mapped
      have pairEqual : (actualNext, [actualResult]) = (next, [result]) :=
        Except.ok.inj mapped
      have stateEqual : actualNext = next := congrArg Prod.fst pairEqual
      have listEqual : [actualResult] = [result] := congrArg Prod.snd pairEqual
      have resultEqual : actualResult = result := (List.cons.inj listEqual).1
      rw [stateEqual, resultEqual]

/-- Actual SQL text to the independent bag denotation for the live simple
query form.  The state equality rules out read-side mutation. -/
theorem executeText_read_refines
    {state next : Core.State} {text tableName : String}
    {query : Core.Query} {result : Core.Result}
    (supported : SupportedReadText state text (.query tableName query))
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    ∃ table, state.database.findTable? tableName = some table ∧
      next = state ∧
      RelationalAlgebra.ofList result.rows =
        CoreReadSemantics.queryDenotation query table.rows := by
  exact CoreReadSemantics.execute_query_denotes
    (core_success_of_execute supported success)

end CoreSQLReadText
end SQLeanite
