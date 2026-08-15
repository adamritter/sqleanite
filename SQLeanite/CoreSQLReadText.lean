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
  | count (select : Select) (source : TableRef) (stored : Core.Table)
      (predicate : Option Core.Predicate) (target : Core.CountTarget)
      (noCompounds : select.compounds = #[])
      (oneSource : select.sources = #[source])
      (noGroups : select.groupBy = #[])
      (noHaving : select.having = none) (noOffset : select.offset = 0)
      (plainSource : source.subquerySql = none ∧ source.joinOn = none)
      (found : state.database.findTable?
        (CoreSQL.canonical source.name) = some stored)
      (predicateTranslated : select.where_.mapM
        (CoreSQL.predicate stored.schema) = .ok predicate)
      (countTranslated : CoreSQL.countTarget? stored.schema
        select.columns.toList = .ok (some target))
      (notSum : CoreSQL.sumColumn? stored.schema select.columns.toList =
        .ok none)
      (notExtreme : CoreSQL.extremeColumn? stored.schema
        select.columns.toList = .ok none)
      (notDistinct : select.distinct = false)
      (noOrdering : select.orderBy = #[]) (noLimit : select.limit = none) :
      TranslatedRead state (.select select)
        (.count (CoreSQL.canonical source.name) target predicate)
  | sum (select : Select) (source : TableRef) (stored : Core.Table)
      (predicate : Option Core.Predicate) (column : Nat)
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
      (sumTranslated : CoreSQL.sumColumn? stored.schema
        select.columns.toList = .ok (some column))
      (notExtreme : CoreSQL.extremeColumn? stored.schema
        select.columns.toList = .ok none)
      (notDistinct : select.distinct = false)
      (noOrdering : select.orderBy = #[]) (noLimit : select.limit = none) :
      TranslatedRead state (.select select)
        (.sum (CoreSQL.canonical source.name) column predicate)
  | extreme (select : Select) (source : TableRef) (stored : Core.Table)
      (predicate : Option Core.Predicate) (minimum : Bool) (column : Nat)
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
      (extremeTranslated : CoreSQL.extremeColumn? stored.schema
        select.columns.toList = .ok (some (minimum, column)))
      (notDistinct : select.distinct = false)
      (noOrdering : select.orderBy = #[]) (noLimit : select.limit = none) :
      TranslatedRead state (.select select)
        (.extreme (CoreSQL.canonical source.name) minimum column predicate)
  | group (select : Select) (source : TableRef) (stored : Core.Table)
      (predicate : Option Core.Predicate) (groups : List Nat)
      (outputs : List Core.GroupOutput)
      (noCompounds : select.compounds = #[])
      (oneSource : select.sources = #[source])
      (hasGroups : select.groupBy.isEmpty = false)
      (noHaving : select.having = none) (noOffset : select.offset = 0)
      (plainSource : source.subquerySql = none ∧ source.joinOn = none)
      (found : state.database.findTable?
        (CoreSQL.canonical source.name) = some stored)
      (predicateTranslated : select.where_.mapM
        (CoreSQL.predicate stored.schema) = .ok predicate)
      (notDistinct : select.distinct = false)
      (noOrdering : select.orderBy = #[]) (noLimit : select.limit = none)
      (groupsTranslated : CoreSQL.groupColumns stored.schema
        select.groupBy.toList = .ok groups)
      (outputsTranslated : CoreSQL.groupOutputs stored.schema groups
        select.columns.toList = .ok outputs) :
      TranslatedRead state (.select select)
        (.group (CoreSQL.canonical source.name) {
          groupBy := groups
          outputs
          predicate })
  | join (select : Select) (leftSource rightSource : TableRef)
      (left right : Core.Table) (query : CoreJoin.Query)
      (noCompounds : select.compounds = #[])
      (twoSources : select.sources = #[leftSource, rightSource])
      (plainSources : leftSource.subquerySql = none ∧
        rightSource.subquerySql = none ∧ leftSource.joinOn = none ∧
        rightSource.rightJoin = false ∧ rightSource.naturalJoin = false ∧
        rightSource.usingColumns = #[])
      (noGroups : select.groupBy = #[]) (noHaving : select.having = none)
      (notDistinct : select.distinct = false) (noOffset : select.offset = 0)
      (leftFound : state.database.findTable?
        (CoreSQL.canonical leftSource.name) = some left)
      (rightFound : state.database.findTable?
        (CoreSQL.canonical rightSource.name) = some right)
      (queryTranslated : CoreSQL.joinQuery select
        (CoreSQL.canonical leftSource.name)
        (CoreSQL.canonical rightSource.name) left.schema right.schema =
          .ok query) :
      TranslatedRead state (.select select)
        (.join (CoreSQL.canonical leftSource.name)
          (CoreSQL.canonical rightSource.name)
          (CoreOptimizerBridge.optimizeJoin
            (CoreSQL.canonical leftSource.name)
            (CoreSQL.canonical rightSource.name) query))

private theorem compoundHeight_eq_one (select : Select)
    (noCompounds : select.compounds = #[]) : select.compoundHeight = 1 := by
  rw [show select.compoundHeight =
    selectCompoundListHeight select.compounds.toList + 1 by
      cases select
      rfl]
  rw [noCompounds]
  rfl

theorem executeStatement_eq_core
    {state : Core.State} {statement : Statement} {command : Core.Command}
    (translated : TranslatedRead state statement command) :
    CoreSQL.executeStatement state statement =
      oneResult (Core.execute state command) := by
  cases translated with
  | query select source stored predicate columns ordering noCompounds oneSource
      noGroups noHaving noOffset plainSource found predicateTranslated
      notCount notSum notExtreme projectionTranslated orderingTranslated =>
      have height := compoundHeight_eq_one select noCompounds
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
  | count select source stored predicate target noCompounds oneSource noGroups
      noHaving noOffset plainSource found predicateTranslated countTranslated
      notSum notExtreme notDistinct noOrdering noLimit =>
      have height := compoundHeight_eq_one select noCompounds
      simp [CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.executeSelectBase, height,
        noCompounds, oneSource, noGroups, noHaving, noOffset, plainSource,
        found, predicateTranslated, countTranslated, notSum, notExtreme,
        notDistinct, noOrdering, noLimit, oneResult, Except.instMonad,
        Except.bind, Except.pure, pure]
      cases execution : Core.execute state
          (.count (CoreSQL.canonical source.name) target predicate) with
      | error message => simp only [Except.map]
      | ok outcome =>
          rcases outcome with ⟨actualNext, actualResult⟩
          simp only [CoreSQL.executeSelectFuel.executeArms, Except.map]
  | sum select source stored predicate column noCompounds oneSource noGroups
      noHaving noOffset plainSource found predicateTranslated notCount
      sumTranslated notExtreme notDistinct noOrdering noLimit =>
      have height := compoundHeight_eq_one select noCompounds
      simp [CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.executeSelectBase, height,
        noCompounds, oneSource, noGroups, noHaving, noOffset, plainSource,
        found, predicateTranslated, notCount, sumTranslated, notExtreme,
        notDistinct, noOrdering, noLimit, oneResult, Except.instMonad,
        Except.bind, Except.pure, pure]
      cases execution : Core.execute state
          (.sum (CoreSQL.canonical source.name) column predicate) with
      | error message => simp only [Except.map]
      | ok outcome =>
          rcases outcome with ⟨actualNext, actualResult⟩
          simp only [CoreSQL.executeSelectFuel.executeArms, Except.map]
  | extreme select source stored predicate minimum column noCompounds oneSource
      noGroups noHaving noOffset plainSource found predicateTranslated notCount
      notSum extremeTranslated notDistinct noOrdering noLimit =>
      have height := compoundHeight_eq_one select noCompounds
      simp [CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.executeSelectBase, height,
        noCompounds, oneSource, noGroups, noHaving, noOffset, plainSource,
        found, predicateTranslated, notCount, notSum, extremeTranslated,
        notDistinct, noOrdering, noLimit, oneResult, Except.instMonad,
        Except.bind, Except.pure, pure]
      cases execution : Core.execute state
          (.extreme (CoreSQL.canonical source.name) minimum column predicate) with
      | error message => simp only [Except.map]
      | ok outcome =>
          rcases outcome with ⟨actualNext, actualResult⟩
          simp only [CoreSQL.executeSelectFuel.executeArms, Except.map]
  | group select source stored predicate groups outputs noCompounds oneSource
      hasGroups noHaving noOffset plainSource found predicateTranslated
      notDistinct noOrdering noLimit groupsTranslated outputsTranslated =>
      have height := compoundHeight_eq_one select noCompounds
      simp [CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.executeSelectBase, height,
        noCompounds, oneSource, hasGroups, noHaving, noOffset, plainSource,
        found, predicateTranslated, notDistinct, noOrdering, noLimit,
        groupsTranslated, outputsTranslated, oneResult, Except.instMonad,
        Except.bind, Except.pure, pure]
      cases execution : Core.execute state
          (.group (CoreSQL.canonical source.name) {
            groupBy := groups
            outputs
            predicate }) with
      | error message => simp only [Except.map]
      | ok outcome =>
          rcases outcome with ⟨actualNext, actualResult⟩
          simp only [CoreSQL.executeSelectFuel.executeArms, Except.map]
  | join select leftSource rightSource left right query noCompounds twoSources
      plainSources noGroups noHaving notDistinct noOffset leftFound rightFound
      queryTranslated =>
      have height := compoundHeight_eq_one select noCompounds
      have baseSelect : { select with compounds := #[] } = select := by
        cases select
        simp_all
      have sourceSize : select.sources.size = 2 := by
        rw [twoSources]
        rfl
      have joinExecution : CoreSQL.executeJoin state
          { select with compounds := #[] } =
          match Core.execute state
            (.join (CoreSQL.canonical leftSource.name)
              (CoreSQL.canonical rightSource.name)
              (CoreOptimizerBridge.optimizeJoin
                (CoreSQL.canonical leftSource.name)
                (CoreSQL.canonical rightSource.name) query)) with
          | .error message => .error message
          | .ok outcome => .ok (CoreSQL.SelectExecution.mk outcome.1 outcome.2
              (CoreOptimizerBridge.optimizeJoin
                (CoreSQL.canonical leftSource.name)
                (CoreSQL.canonical rightSource.name) query).columns.length) := by
        rw [baseSelect]
        simp [CoreSQL.executeJoin, twoSources, plainSources, noGroups,
          noHaving, notDistinct, noOffset, leftFound, rightFound,
          queryTranslated, Except.instMonad, Except.bind, Except.pure, pure]
        cases execution : Core.execute state
            (.join (CoreSQL.canonical leftSource.name)
              (CoreSQL.canonical rightSource.name)
              (CoreOptimizerBridge.optimizeJoin
                (CoreSQL.canonical leftSource.name)
                (CoreSQL.canonical rightSource.name) query)) <;>
          simp [execution]
      simp [CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.executeSelectBase,
        height, noCompounds, sourceSize, joinExecution, oneResult,
        Except.instMonad, Except.bind, Except.pure, pure]
      cases execution : Core.execute state
          (.join (CoreSQL.canonical leftSource.name)
            (CoreSQL.canonical rightSource.name)
            (CoreOptimizerBridge.optimizeJoin
              (CoreSQL.canonical leftSource.name)
              (CoreSQL.canonical rightSource.name) query)) with
      | error message => simp only [Except.map]
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

theorem executeText_count_refines
    {state next : Core.State} {text tableName : String}
    {target : Core.CountTarget} {predicate : Option Core.Predicate}
    {result : Core.Result}
    (supported : SupportedReadText state text
      (.count tableName target predicate))
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    ∃ table count,
      state.database.findTable? tableName = some table ∧
      next = state ∧ result.rows = [[.integer count]] ∧
      count.value = Int.ofNat
        (Core.countRows target predicate table.rows) := by
  exact CoreReadSemantics.execute_count_denotes
    (core_success_of_execute supported success)

theorem executeText_sum_refines
    {state next : Core.State} {text tableName : String}
    {column : Nat} {predicate : Option Core.Predicate} {result : Core.Result}
    (supported : SupportedReadText state text
      (.sum tableName column predicate))
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    ∃ table value,
      state.database.findTable? tableName = some table ∧
      Core.sumColumn column (table.rows.filter (Core.selects predicate)) =
        .ok value ∧ next = state ∧ result.rows = [[value]] := by
  exact CoreReadSemantics.execute_sum_denotes
    (core_success_of_execute supported success)

theorem executeText_extreme_refines
    {state next : Core.State} {text tableName : String}
    {minimum : Bool} {column : Nat} {predicate : Option Core.Predicate}
    {result : Core.Result}
    (supported : SupportedReadText state text
      (.extreme tableName minimum column predicate))
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    ∃ table, state.database.findTable? tableName = some table ∧
      next = state ∧
      result.rows = [[Core.extremeColumn minimum column
        (table.rows.filter (Core.selects predicate))]] := by
  exact CoreReadSemantics.execute_extreme_denotes
    (core_success_of_execute supported success)

theorem executeText_group_refines
    {state next : Core.State} {text tableName : String}
    {query : Core.GroupQuery} {result : Core.Result}
    (supported : SupportedReadText state text (.group tableName query))
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    ∃ table,
      state.database.findTable? tableName = some table ∧
      next = state ∧
      RelationalAlgebra.Aligned (fun group output =>
        RelationalAlgebra.Aligned
          (RelationalAlgebra.coreGroupOutputRefines query table.rows group)
          query.outputs output)
        (query.groupKeys table.rows) result.rows := by
  exact CoreReadSemantics.execute_group_denotes
    (core_success_of_execute supported success)

theorem executeText_join_refines
    {state next : Core.State} {text leftName rightName : String}
    {query : CoreJoin.Query} {result : Core.Result}
    (supported : SupportedReadText state text
      (.join leftName rightName query))
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    ∃ left right,
      state.database.findTable? leftName = some left ∧
      state.database.findTable? rightName = some right ∧
      next = state ∧
      RelationalAlgebra.ofList result.rows =
        CoreReadSemantics.joinDenotation query left.rows right.rows := by
  exact CoreReadSemantics.execute_join_denotes
    (core_success_of_execute supported success)

end CoreSQLReadText
end SQLeanite
