import SQLeanite.CoreSQLReadText.ExecuteBinaryPlan

namespace SQLeanite
namespace CoreSQLReadText

theorem executeStatement_eq_core
    {state : Core.State} {statement : Statement} {command : Core.Command}
    (translated : TranslatedRead state statement command) :
    CoreSQL.executeStatement state statement =
      oneResult (Core.execute state command) := by
  cases translated with
  | query select source stored predicate columns ordering noCompounds oneSource
      noGroups noHaving noOffset plainSource found namesBound predicateTranslated
      notCount notSum notExtreme projectionTranslated orderingTranslated directQuery =>
      have height := compoundHeight_eq_one select noCompounds
      simp_all [CoreSQL.selectNamesBound, CoreSQL.resolvedOrdering, CoreSQL.directOrdering, CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.requiresCompoundCollation, CoreSQL.executeSelectBaseComplete, CoreSQL.executeSelectBase, height,
        noCompounds,
        oneSource, noGroups, noHaving, noOffset, plainSource, found, namesBound,
        predicateTranslated, notCount, notSum, notExtreme,
        projectionTranslated, orderingTranslated, directQuery, oneResult,
        bind, Functor.map, Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.query (CoreSQL.resolveTableName state source.name) {
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
      noHaving noOffset plainSource found namesBound predicateTranslated countTranslated
      notSum notExtreme notDistinct noOrdering noLimit =>
      have height := compoundHeight_eq_one select noCompounds
      simp_all [CoreSQL.selectNamesBound, CoreSQL.resolvedOrdering, CoreSQL.directOrdering, CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.requiresCompoundCollation, CoreSQL.executeSelectBaseComplete, CoreSQL.executeSelectBase, height,
        noCompounds, oneSource, noGroups, noHaving, noOffset, plainSource,
        found, namesBound, predicateTranslated, countTranslated, notSum, notExtreme,
        notDistinct, noOrdering, noLimit, oneResult, bind, Functor.map,
        Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.count (CoreSQL.resolveTableName state source.name) target predicate) with
      | error message => simp only [Except.map]
      | ok outcome =>
          rcases outcome with ⟨actualNext, actualResult⟩
          simp only [CoreSQL.executeSelectFuel.executeArms, Except.map]
  | sum select source stored predicate column noCompounds oneSource noGroups
      noHaving noOffset plainSource found namesBound predicateTranslated notCount
      sumTranslated notExtreme notDistinct noOrdering noLimit =>
      have height := compoundHeight_eq_one select noCompounds
      simp_all [CoreSQL.selectNamesBound, CoreSQL.resolvedOrdering, CoreSQL.directOrdering, CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.requiresCompoundCollation, CoreSQL.executeSelectBaseComplete, CoreSQL.executeSelectBase, height,
        noCompounds, oneSource, noGroups, noHaving, noOffset, plainSource,
        found, namesBound, predicateTranslated, notCount, sumTranslated, notExtreme,
        notDistinct, noOrdering, noLimit, oneResult, bind, Functor.map,
        Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.sum (CoreSQL.resolveTableName state source.name) column predicate) with
      | error message => simp only [Except.map]
      | ok outcome =>
          rcases outcome with ⟨actualNext, actualResult⟩
          simp only [CoreSQL.executeSelectFuel.executeArms, Except.map]
  | extreme select source stored predicate minimum column noCompounds oneSource
      noGroups noHaving noOffset plainSource found namesBound predicateTranslated notCount
      notSum extremeTranslated notDistinct noOrdering noLimit =>
      have height := compoundHeight_eq_one select noCompounds
      simp_all [CoreSQL.selectNamesBound, CoreSQL.resolvedOrdering, CoreSQL.directOrdering, CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.requiresCompoundCollation, CoreSQL.executeSelectBaseComplete, CoreSQL.executeSelectBase, height,
        noCompounds, oneSource, noGroups, noHaving, noOffset, plainSource,
        found, namesBound, predicateTranslated, notCount, notSum, extremeTranslated,
        notDistinct, noOrdering, noLimit, oneResult, bind, Functor.map,
        Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.extreme (CoreSQL.resolveTableName state source.name) minimum column predicate) with
      | error message => simp only [Except.map]
      | ok outcome =>
          rcases outcome with ⟨actualNext, actualResult⟩
          simp only [CoreSQL.executeSelectFuel.executeArms, Except.map]
  | group select source stored predicate groups outputs noCompounds oneSource
      hasGroups noHaving noOffset plainSource found namesBound predicateTranslated
      notDistinct noOrdering noLimit groupsTranslated outputsTranslated =>
      have height := compoundHeight_eq_one select noCompounds
      simp_all [CoreSQL.selectNamesBound, CoreSQL.resolvedOrdering, CoreSQL.directOrdering, CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.requiresCompoundCollation, CoreSQL.executeSelectBaseComplete, CoreSQL.executeSelectBase, height,
        noCompounds, oneSource, hasGroups, noHaving, noOffset, plainSource,
        found, namesBound, predicateTranslated, notDistinct, noOrdering, noLimit,
        groupsTranslated, outputsTranslated, oneResult, bind, Functor.map,
        Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.group (CoreSQL.resolveTableName state source.name) {
            groupBy := groups
            outputs
            predicate }) with
      | error message => simp only [Except.map]
      | ok outcome =>
          rcases outcome with ⟨actualNext, actualResult⟩
          simp only [CoreSQL.executeSelectFuel.executeArms, Except.map]
  | join select leftSource rightSource left right query noCompounds twoSources
      plainSources noGroups noHaving leftFound rightFound
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
            (.join (CoreSQL.resolveTableName state leftSource.name)
              (CoreSQL.resolveTableName state rightSource.name)
              (CoreOptimizerBridge.optimizeJoin
                (CoreSQL.resolveTableName state leftSource.name)
                (CoreSQL.resolveTableName state rightSource.name) query)) with
          | .error message => .error message
          | .ok outcome => .ok (CoreSQL.SelectExecution.mk outcome.1 outcome.2
              (CoreOptimizerBridge.optimizeJoin
                (CoreSQL.resolveTableName state leftSource.name)
                (CoreSQL.resolveTableName state rightSource.name) query).columns.length) := by
        rw [baseSelect]
        simp [CoreSQL.executeJoin, CoreSQL.joinAliasQuery, CoreSQL.joinQueryComplete, CoreSQL.joinQueryForRows, CoreSQL.joinQueryWithZero, twoSources, plainSources, noGroups,
          noHaving, leftFound, rightFound,
          queryTranslated, bind, Functor.map, Except.bind, pure, Except.pure, pure]
        cases execution : Core.execute state
            (.join (CoreSQL.resolveTableName state leftSource.name)
              (CoreSQL.resolveTableName state rightSource.name)
              (CoreOptimizerBridge.optimizeJoin
                (CoreSQL.resolveTableName state leftSource.name)
                (CoreSQL.resolveTableName state rightSource.name) query)) <;>
          simp [execution]
      simp [CoreSQL.executeStatement, CoreSQL.executeSelect,
        CoreSQL.executeSelectFuel, CoreSQL.requiresCompoundCollation, CoreSQL.executeSelectBaseComplete,
        CoreSQL.executeSelectBase, Core.execute, leftFound, rightFound,
        height, noCompounds, sourceSize, joinExecution, oneResult,
        CoreSQL.executeSelectFuel.executeArms, bind, Functor.map, Except.map, Except.bind, pure, Except.pure]

inductive SupportedReadText (state : Core.State) (text : String)
    (command : Core.Command) : Prop where
  | intro (statement : Statement)
      (parsed : CoreTokenGrammar.Parses text #[statement])
      (translated : TranslatedRead state statement command) :
      SupportedReadText state text command

inductive SupportedBinaryCompoundText (state : Core.State) (text : String)
    (left : Core.Command) (operation : CompoundOp) (right : Core.Command) :
    Prop where
  | intro (select : Select)
      (parsed : CoreTokenGrammar.Parses text #[.select select])
      (translated : TranslatedBinaryCompound state select left operation right) :
      SupportedBinaryCompoundText state text left operation right

/-- An actual SQL string whose certified parse has a recursively translated
compound plan. -/
inductive SupportedCompoundText (state : Core.State) (text : String)
    (plan : CompoundReadPlan) : Prop where
  | intro (select : Select)
      (parsed : CoreTokenGrammar.Parses text #[.select select])
      (translated : TranslatedCompoundRead state select plan) :
      SupportedCompoundText state text plan

theorem execute_binary_eq_core
    {state : Core.State} {text : String} {left right : Core.Command}
    {operation : CompoundOp}
    (supported : SupportedBinaryCompoundText state text left operation right) :
    CoreSQL.execute state text = executeBinaryPlan state left operation right := by
  rcases supported with ⟨select, parsed, translated⟩
  rcases parsed with ⟨certificate, certified, statements⟩
  simp only [CoreSQL.execute, certified, statements, bind, Functor.map, Except.bind,
    CoreSQL.runStatements]
  rw [executeStatement_binary_eq_core translated]
  cases execution : executeBinaryPlan state left operation right <;>
    simp [execution, bind, Functor.map, Except.bind, pure, Except.pure, pure]

/-- The arbitrary-nesting refinement begins at certified SQL text, not at a
pre-parsed AST.  The existential width preserves SQLite's empty-result column
count, which cannot in general be recovered from the row list. -/
theorem executeText_compound_refines
    {state next : Core.State} {text : String} {plan : CompoundReadPlan}
    {result : Core.Result}
    (supported : SupportedCompoundText state text plan)
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    ∃ width, next = state ∧
      plan.Refines state.database result.rows width := by
  rcases supported with ⟨select, parsed, translated⟩
  rcases parsed with ⟨certificate, certified, statements⟩
  simp only [CoreSQL.execute, certified, statements, bind, Functor.map,
    Except.bind, CoreSQL.runStatements] at success
  cases selected : CoreSQL.executeSelect state select with
  | error message =>
      simp [CoreSQL.executeStatement, selected, bind, Functor.map, Except.bind]
        at success
  | ok outcome =>
      simp [CoreSQL.executeStatement, selected, bind, Functor.map, Except.bind,
        pure, Except.pure, pure] at success
      have nextEq : outcome.state = next := success.1
      have resultEq : outcome.result = result := success.2
      have fuelSuccess : CoreSQL.executeSelectFuel select.compoundHeight
          state select = .ok outcome := by
        simpa [CoreSQL.executeSelect] using selected
      have refined := executeSelectFuel_compound_refines select.compoundHeight
        translated fuelSuccess
      subst next
      subst result
      exact ⟨outcome.width, refined.1, refined.2⟩

theorem execute_eq_core
    {state : Core.State} {text : String} {command : Core.Command}
    (supported : SupportedReadText state text command) :
    CoreSQL.execute state text = oneResult (Core.execute state command) := by
  rcases supported with ⟨statement, parsed, translated⟩
  rcases parsed with ⟨certificate, certified, statements⟩
  simp only [CoreSQL.execute, certified, statements, bind, Functor.map, Except.bind,
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

/-- Actual SQL text for a binary UNION ALL/UNION/INTERSECT/EXCEPT reaches
both base denotations and the independent duplicate-sensitive bag operator. -/
theorem executeText_binary_refines
    {state next : Core.State} {text : String} {left right : Core.Command}
    {operation : CompoundOp} {result : Core.Result}
    (supported : SupportedBinaryCompoundText state text left operation right)
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    ∃ leftResult rightResult,
      Core.execute state left = .ok (state, leftResult) ∧
      Core.execute state right = .ok (state, rightResult) ∧
      ReadRefines state.database left leftResult ∧
      ReadRefines state.database right rightResult ∧
      readWidth left = readWidth right ∧ next = state ∧
      result.rows = CoreSQL.combineRows operation
        leftResult.rows rightResult.rows ∧
      RelationalAlgebra.ofList (result.rows.map Core.distinctRowKey) =
        CoreCompound.denotation operation
          (RelationalAlgebra.ofList (leftResult.rows.map Core.distinctRowKey))
          (RelationalAlgebra.ofList (rightResult.rows.map Core.distinctRowKey)) := by
  have planSuccess : executeBinaryPlan state left operation right =
      .ok (next, [result]) := (execute_binary_eq_core supported).symm.trans success
  rcases supported with ⟨select, parsed, translated⟩
  cases translated with
  | intro arm left right operation compounds noOuterOrder noOuterLimit
      noOuterOffset armNoCompounds leftTranslated rightTranslated =>
      unfold executeBinaryPlan at planSuccess
      cases leftExecution : Core.execute state left with
      | error message =>
          simp [leftExecution, bind, Functor.map, Except.bind] at planSuccess
      | ok leftOutcome =>
          rcases leftOutcome with ⟨leftNext, leftResult⟩
          have leftUnchanged : leftNext = state :=
            core_read_state_eq leftTranslated leftExecution
          subst leftNext
          cases rightExecution : Core.execute state right with
          | error message =>
              simp [leftExecution, rightExecution, bind, Functor.map,
                Except.bind] at planSuccess
          | ok rightOutcome =>
              rcases rightOutcome with ⟨rightNext, rightResult⟩
              have rightUnchanged : rightNext = state :=
                core_read_state_eq rightTranslated rightExecution
              subst rightNext
              by_cases widths : readWidth left = readWidth right
              · simp [leftExecution, rightExecution, widths, bind, Functor.map,
                  Except.bind, pure, Except.pure, pure] at planSuccess
                have resultEqual : Core.Result.mk (CoreSQL.combineRows operation
                    leftResult.rows rightResult.rows) 0 = result :=
                  planSuccess.2
                have nextEqual : state = next := planSuccess.1
                subst next
                subst result
                refine ⟨leftResult, rightResult, rfl,
                  rfl, core_read_refines leftTranslated leftExecution,
                  core_read_refines rightTranslated rightExecution, widths, rfl,
                  rfl, ?_⟩
                exact CoreSQL.combineRows_denotes operation leftResult.rows rightResult.rows
              · simp [leftExecution, rightExecution, widths, bind, Functor.map,
                  Except.bind, pure, Except.pure, pure] at planSuccess

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
