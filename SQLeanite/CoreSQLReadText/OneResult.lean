import SQLeanite.CoreCollationRead
import SQLeanite.CoreReadSemantics.CoreRow
import SQLeanite.CoreSQL.JoinStreamPrepared

namespace SQLeanite
namespace CoreSQLReadText

def oneResult
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
      (plainSource : source.schema = none ∧ source.functionArgs = none ∧ source.subquerySql = none ∧ source.joinOn = none)
      (found : state.database.findTable?
        (CoreSQL.resolveTableName state source.name) = some stored)
      (namesBound : CoreSQL.selectNamesBound stored.schema source select = true)
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
      (orderingTranslated : CoreSQL.directOrdering stored.schema source select = .ok ordering)
      (directQuery : CoreSQL.queryNeedsRepresentatives select.distinct columns ordering = false) :
      TranslatedRead state (.select select)
        (.query (CoreSQL.resolveTableName state source.name) {
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
      (plainSource : source.schema = none ∧ source.functionArgs = none ∧ source.subquerySql = none ∧ source.joinOn = none)
      (found : state.database.findTable?
        (CoreSQL.resolveTableName state source.name) = some stored)
      (namesBound : CoreSQL.selectNamesBound stored.schema source select = true)
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
        (.count (CoreSQL.resolveTableName state source.name) target predicate)
  | sum (select : Select) (source : TableRef) (stored : Core.Table)
      (predicate : Option Core.Predicate) (column : Nat)
      (noCompounds : select.compounds = #[])
      (oneSource : select.sources = #[source])
      (noGroups : select.groupBy = #[])
      (noHaving : select.having = none) (noOffset : select.offset = 0)
      (plainSource : source.schema = none ∧ source.functionArgs = none ∧ source.subquerySql = none ∧ source.joinOn = none)
      (found : state.database.findTable?
        (CoreSQL.resolveTableName state source.name) = some stored)
      (namesBound : CoreSQL.selectNamesBound stored.schema source select = true)
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
        (.sum (CoreSQL.resolveTableName state source.name) column predicate)
  | extreme (select : Select) (source : TableRef) (stored : Core.Table)
      (predicate : Option Core.Predicate) (minimum : Bool) (column : Nat)
      (noCompounds : select.compounds = #[])
      (oneSource : select.sources = #[source])
      (noGroups : select.groupBy = #[])
      (noHaving : select.having = none) (noOffset : select.offset = 0)
      (plainSource : source.schema = none ∧ source.functionArgs = none ∧ source.subquerySql = none ∧ source.joinOn = none)
      (found : state.database.findTable?
        (CoreSQL.resolveTableName state source.name) = some stored)
      (namesBound : CoreSQL.selectNamesBound stored.schema source select = true)
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
        (.extreme (CoreSQL.resolveTableName state source.name) minimum column predicate)
  | group (select : Select) (source : TableRef) (stored : Core.Table)
      (predicate : Option Core.Predicate) (groups : List Nat)
      (outputs : List Core.GroupOutput)
      (noCompounds : select.compounds = #[])
      (oneSource : select.sources = #[source])
      (hasGroups : select.groupBy.isEmpty = false)
      (noHaving : select.having = none) (noOffset : select.offset = 0)
      (plainSource : source.schema = none ∧ source.functionArgs = none ∧ source.subquerySql = none ∧ source.joinOn = none)
      (found : state.database.findTable?
        (CoreSQL.resolveTableName state source.name) = some stored)
      (namesBound : CoreSQL.selectNamesBound stored.schema source select = true)
      (predicateTranslated : select.where_.mapM
        (CoreSQL.predicate stored.schema) = .ok predicate)
      (notDistinct : select.distinct = false)
      (noOrdering : select.orderBy = #[]) (noLimit : select.limit = none)
      (groupsTranslated : CoreSQL.groupColumns stored.schema
        select.groupBy.toList = .ok groups)
      (outputsTranslated : CoreSQL.groupOutputs stored.schema groups
        select.columns.toList = .ok outputs) :
      TranslatedRead state (.select select)
        (.group (CoreSQL.resolveTableName state source.name) {
          groupBy := groups
          outputs
          predicate })
  | join (select : Select) (leftSource rightSource : TableRef)
      (left right : Core.Table) (query : CoreJoin.Query)
      (noCompounds : select.compounds = #[])
      (twoSources : select.sources = #[leftSource, rightSource])
      (plainSources : leftSource.schema = none ∧ rightSource.schema = none ∧
        leftSource.functionArgs = none ∧ rightSource.functionArgs = none ∧
        leftSource.subquerySql = none ∧ rightSource.subquerySql = none ∧ leftSource.joinOn = none ∧
        rightSource.rightJoin = false)
      (noGroups : select.groupBy = #[]) (noHaving : select.having = none)
      (leftFound : state.database.findTable?
        (CoreSQL.resolveTableName state leftSource.name) = some left)
      (rightFound : state.database.findTable?
        (CoreSQL.resolveTableName state rightSource.name) = some right)
      (queryTranslated : CoreSQL.joinQuery select
        (CoreSQL.resolveTableName state leftSource.name)
        (CoreSQL.resolveTableName state rightSource.name) left.schema right.schema =
          .ok query) :
      TranslatedRead state (.select select)
        (.join (CoreSQL.resolveTableName state leftSource.name)
          (CoreSQL.resolveTableName state rightSource.name)
          (CoreOptimizerBridge.optimizeJoin
            (CoreSQL.resolveTableName state leftSource.name)
            (CoreSQL.resolveTableName state rightSource.name) query))

theorem translatedRead_noCollation {state : Core.State} {select : Select} {command : Core.Command}
    (translated : TranslatedRead state (.select select) command) :
    ∀ column ∈ select.columns.toList, NoExplicitCollation column.expr := by
  cases translated with
  | query select source stored predicate columns ordering noCompounds oneSource
      noGroups noHaving noOffset plainSource found namesBound predicateTranslated
      notCount notSum notExtreme projectionTranslated orderingTranslated directQuery =>
      intro column member
      exact projection_noCollation column (CoreSQL.projectionSyntax_of_success stored.schema projectionTranslated column member)
  | count select source stored predicate target noCompounds oneSource noGroups
      noHaving noOffset plainSource found namesBound predicateTranslated countTranslated
      notSum notExtreme notDistinct noOrdering noLimit =>
      exact count_noCollation stored.schema select.columns.toList target countTranslated
  | sum select source stored predicate column noCompounds oneSource noGroups
      noHaving noOffset plainSource found namesBound predicateTranslated notCount
      sumTranslated notExtreme notDistinct noOrdering noLimit =>
      exact sum_noCollation stored.schema select.columns.toList column sumTranslated
  | extreme select source stored predicate minimum column noCompounds oneSource noGroups
      noHaving noOffset plainSource found namesBound predicateTranslated notCount
      notSum extremeTranslated notDistinct noOrdering noLimit =>
      exact extreme_noCollation stored.schema select.columns.toList (minimum, column) extremeTranslated
  | group select source stored predicate groups outputs noCompounds oneSource
      hasGroups noHaving noOffset plainSource found namesBound predicateTranslated
      notDistinct noOrdering noLimit groupsTranslated outputsTranslated =>
      exact groups_noCollation stored.schema groups select.columns.toList outputs outputsTranslated
  | join select leftSource rightSource left right query noCompounds twoSources
      plainSources noGroups noHaving leftFound rightFound queryTranslated =>
      exact joinQuery_noCollation select _ _ left.schema right.schema query queryTranslated

theorem translatedRead_columnsCollation_false {state : Core.State} {select : Select}
    {command : Core.Command} (translated : TranslatedRead state (.select select) command) :
    select.columns.any (fun column => (SQLite.ExprCollation.name column.expr).isSome) = false := by
  have absent := translatedRead_noCollation translated
  simp only [← Array.any_toList, List.any_eq_false]
  intro column member
  simp [SQLite.ExprCollation.name, absent column member column.expr.height]

theorem translatedRead_noDeclaredCollation {state : Core.State} {select : Select} {command : Core.Command}
    (translated : TranslatedRead state (.select select) command) :
    ∀ column ∈ select.columns.toList, NoDeclaredCollation column.expr := by
  cases translated with
  | query select source stored predicate columns ordering noCompounds oneSource
      noGroups noHaving noOffset plainSource found namesBound predicateTranslated
      notCount notSum notExtreme projectionTranslated orderingTranslated directQuery =>
      intro column member
      exact projection_noDeclaredCollation column (CoreSQL.projectionSyntax_of_success stored.schema projectionTranslated column member)
  | count select source stored predicate target noCompounds oneSource noGroups
      noHaving noOffset plainSource found namesBound predicateTranslated countTranslated
      notSum notExtreme notDistinct noOrdering noLimit =>
      exact count_noDeclaredCollation stored.schema select.columns.toList target countTranslated
  | sum select source stored predicate column noCompounds oneSource noGroups
      noHaving noOffset plainSource found namesBound predicateTranslated notCount
      sumTranslated notExtreme notDistinct noOrdering noLimit =>
      exact sum_noDeclaredCollation stored.schema select.columns.toList column sumTranslated
  | extreme select source stored predicate minimum column noCompounds oneSource noGroups
      noHaving noOffset plainSource found namesBound predicateTranslated notCount
      notSum extremeTranslated notDistinct noOrdering noLimit =>
      exact extreme_noDeclaredCollation stored.schema select.columns.toList (minimum, column) extremeTranslated
  | group select source stored predicate groups outputs noCompounds oneSource
      hasGroups noHaving noOffset plainSource found namesBound predicateTranslated
      notDistinct noOrdering noLimit groupsTranslated outputsTranslated =>
      exact groups_noDeclaredCollation stored.schema groups select.columns.toList outputs outputsTranslated
  | join select leftSource rightSource left right query noCompounds twoSources
      plainSources noGroups noHaving leftFound rightFound queryTranslated =>
      exact joinQuery_noDeclaredCollation select _ _ left.schema right.schema query queryTranslated

theorem translatedRead_columnsDeclaredCollation_false {state : Core.State} {select : Select}
    {command : Core.Command} (translated : TranslatedRead state (.select select) command) :
    select.columns.any (fun column => (SQLite.ExprCollation.declaredNameFuel column.expr.height column.expr).isSome) = false := by
  have absent := translatedRead_noDeclaredCollation translated
  simp only [← Array.any_toList, List.any_eq_false]
  intro column member
  simp [absent column member column.expr.height]

theorem translatedRead_noCompounds {state : Core.State} {select : Select} {command : Core.Command}
    (translated : TranslatedRead state (.select select) command) : select.compounds = #[] := by
  cases translated <;> assumption

theorem translatedRead_sources_nonempty {state : Core.State} {select : Select}
    {command : Core.Command} (translated : TranslatedRead state (.select select) command) :
    select.sources.isEmpty = false := by
  cases translated <;> simp_all

theorem translatedRead_resultCollation_false {state : Core.State} {select : Select}
    {command : Core.Command} (translated : TranslatedRead state (.select select) command) (fuel : Nat) :
    CoreSQL.resultCollationFuel fuel select = false := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [CoreSQL.resultCollationFuel, translatedRead_noCompounds translated,
      translatedRead_columnsCollation_false translated, translatedRead_sources_nonempty translated]

/-- The number of values produced by a translated read command.  Unsupported
write commands are assigned zero; `TranslatedRead` ensures they cannot occur
at this boundary. -/
def readWidth : Core.Command → Nat
  | .query _ query => query.columns.length
  | .count .. | .sum .. | .extreme .. => 1
  | .group _ query => query.outputs.length
  | .join _ _ query => query.columns.length
  | _ => 0

def selectExecution (width : Nat)
    (execution : Except String (Core.State × Core.Result)) :
    Except String CoreSQL.SelectExecution :=
  match execution with
  | .error message => .error message
  | .ok outcome => .ok ⟨outcome.1, outcome.2, width⟩

/-- Base SELECT translation preserves the executor's explicit row width.  This
is stronger than the public one-result theorem and is the composition lemma
needed by duplicate-sensitive compound SELECTs. -/
theorem executeSelectBase_eq_core
    {state : Core.State} {select : Select} {command : Core.Command}
    (translated : TranslatedRead state (.select select) command) :
    CoreSQL.executeSelectBase state select =
      selectExecution (readWidth command) (Core.execute state command) := by
  cases translated with
  | query select source stored predicate columns ordering noCompounds oneSource
      noGroups noHaving noOffset plainSource found namesBound predicateTranslated
      notCount notSum notExtreme projectionTranslated orderingTranslated directQuery =>
      simp [CoreSQL.executeSelectBase, oneSource, noGroups, noHaving, noOffset,
        plainSource, found, namesBound, predicateTranslated, notCount, notSum, notExtreme,
        projectionTranslated, orderingTranslated, directQuery, readWidth, selectExecution,
        bind, Functor.map, Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.query (CoreSQL.resolveTableName state source.name) {
            columns
            predicate
            orderBy := ordering
            limit := select.limit
            distinct := select.distinct }) <;>
        simp [execution] <;> rfl

  | count select source stored predicate target noCompounds oneSource noGroups
      noHaving noOffset plainSource found namesBound predicateTranslated countTranslated
      notSum notExtreme notDistinct noOrdering noLimit =>
      simp [CoreSQL.executeSelectBase, oneSource, noGroups, noHaving, noOffset,
        plainSource, found, namesBound, predicateTranslated, countTranslated, notSum,
        notExtreme, notDistinct, noOrdering, noLimit, readWidth,
        selectExecution, bind, Functor.map, Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.count (CoreSQL.resolveTableName state source.name) target predicate) <;>
        simp [execution] <;> rfl
  | sum select source stored predicate column noCompounds oneSource noGroups
      noHaving noOffset plainSource found namesBound predicateTranslated notCount
      sumTranslated notExtreme notDistinct noOrdering noLimit =>
      simp [CoreSQL.executeSelectBase, oneSource, noGroups, noHaving, noOffset,
        plainSource, found, namesBound, predicateTranslated, notCount, sumTranslated,
        notExtreme, notDistinct, noOrdering, noLimit, readWidth,
        selectExecution, bind, Functor.map, Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.sum (CoreSQL.resolveTableName state source.name) column predicate) <;>
        simp [execution] <;> rfl
  | extreme select source stored predicate minimum column noCompounds oneSource
      noGroups noHaving noOffset plainSource found namesBound predicateTranslated notCount
      notSum extremeTranslated notDistinct noOrdering noLimit =>
      simp [CoreSQL.executeSelectBase, oneSource, noGroups, noHaving, noOffset,
        plainSource, found, namesBound, predicateTranslated, notCount, notSum,
        extremeTranslated, notDistinct, noOrdering, noLimit, readWidth,
        selectExecution, bind, Functor.map, Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.extreme (CoreSQL.resolveTableName state source.name) minimum column predicate) <;>
        simp [execution] <;> rfl
  | group select source stored predicate groups outputs noCompounds oneSource
      hasGroups noHaving noOffset plainSource found namesBound predicateTranslated
      notDistinct noOrdering noLimit groupsTranslated outputsTranslated =>
      simp [CoreSQL.executeSelectBase, oneSource, hasGroups, noHaving, noOffset,
        plainSource, found, namesBound, predicateTranslated, notDistinct, noOrdering,
        noLimit, groupsTranslated, outputsTranslated, readWidth,
        selectExecution, bind, Functor.map, Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.group (CoreSQL.resolveTableName state source.name) {
            groupBy := groups
            outputs
            predicate }) <;>
        simp [execution] <;> rfl
  | join select leftSource rightSource left right query noCompounds twoSources
      plainSources noGroups noHaving leftFound rightFound
      queryTranslated =>
      have sourceSize : select.sources.size = 2 := by
        rw [twoSources]
        rfl
      simp [CoreSQL.executeSelectBase, sourceSize, CoreSQL.executeJoin, CoreSQL.joinAliasQuery, CoreSQL.joinQueryComplete, CoreSQL.joinQueryForRows, CoreSQL.joinQueryWithZero,
        twoSources, plainSources, noGroups, noHaving,
        leftFound, rightFound, queryTranslated, readWidth, selectExecution,
        bind, Functor.map, Except.bind, pure, Except.pure, pure]
      cases execution : Core.execute state
          (.join (CoreSQL.resolveTableName state leftSource.name)
            (CoreSQL.resolveTableName state rightSource.name)
            (CoreOptimizerBridge.optimizeJoin
              (CoreSQL.resolveTableName state leftSource.name)
              (CoreSQL.resolveTableName state rightSource.name) query)) <;>
        simp [execution] <;> rfl

/-- The generalized joined-expression fallback cannot replace any previously
translated Core read. Stored JOIN inputs make the existing join command total. -/
theorem executeSelectBaseComplete_eq_core
    {state : Core.State} {select : Select} {command : Core.Command}
    (translated : TranslatedRead state (.select select) command) :
    CoreSQL.executeSelectBaseComplete state select =
      selectExecution (readWidth command) (Core.execute state command) := by
  have base := executeSelectBase_eq_core translated
  cases translated <;>
    simp_all [CoreSQL.executeSelectBaseComplete, selectExecution, Core.execute,
      bind, Except.bind, pure, Except.pure]

/-- Every command admitted by `TranslatedRead` is observationally read-only.
This fact is used to translate later compound arms in the same database
context as the first arm. -/
theorem core_read_state_eq
    {state next : Core.State} {statement : Statement}
    {command : Core.Command} {result : Core.Result}
    (translated : TranslatedRead state statement command)
    (success : Core.execute state command = .ok (next, result)) :
    next = state := by
  cases translated with
  | query =>
      rcases CoreReadSemantics.execute_query_denotes success with
        ⟨_, _, unchanged, _⟩
      exact unchanged
  | count =>
      rcases CoreReadSemantics.execute_count_denotes success with
        ⟨_, _, _, unchanged, _, _⟩
      exact unchanged
  | sum =>
      rcases CoreReadSemantics.execute_sum_denotes success with
        ⟨_, _, _, _, unchanged, _⟩
      exact unchanged
  | extreme =>
      rcases CoreReadSemantics.execute_extreme_denotes success with
        ⟨_, _, unchanged, _⟩
      exact unchanged
  | group =>
      rcases CoreReadSemantics.execute_group_denotes success with
        ⟨_, _, unchanged, _⟩
      exact unchanged
  | join =>
      rcases CoreReadSemantics.execute_join_denotes success with
        ⟨_, _, _, _, unchanged, _⟩
      exact unchanged

/-- One uniform semantic postcondition for every live base-read command. -/
def ReadRefines (database : Core.Database) (command : Core.Command)
    (result : Core.Result) : Prop :=
  match command with
  | .query tableName query =>
      ∃ table, database.findTable? tableName = some table ∧
        RelationalAlgebra.ofList result.rows =
          CoreReadSemantics.queryDenotation query table.rows
  | .count tableName target predicate =>
      ∃ table count, database.findTable? tableName = some table ∧
        result.rows = [[.integer count]] ∧
        count.value = Int.ofNat (Core.countRows target predicate table.rows)
  | .sum tableName column predicate =>
      ∃ table value, database.findTable? tableName = some table ∧
        Core.sumColumn column (table.rows.filter (Core.selects predicate)) =
          .ok value ∧ result.rows = [[value]]
  | .extreme tableName minimum column predicate =>
      ∃ table, database.findTable? tableName = some table ∧
        result.rows = [[Core.extremeColumn minimum column
          (table.rows.filter (Core.selects predicate))]]
  | .group tableName query =>
      ∃ table, database.findTable? tableName = some table ∧
        RelationalAlgebra.Aligned (fun group output =>
          RelationalAlgebra.Aligned
            (RelationalAlgebra.coreGroupOutputRefines query table.rows group)
            query.outputs output)
          (query.groupKeys table.rows) result.rows
  | .join leftName rightName query =>
      ∃ left right, database.findTable? leftName = some left ∧
        database.findTable? rightName = some right ∧
        RelationalAlgebra.ofList result.rows =
          CoreReadSemantics.joinDenotation query left.rows right.rows
  | _ => False

theorem core_read_refines
    {state next : Core.State} {statement : Statement}
    {command : Core.Command} {result : Core.Result}
    (translated : TranslatedRead state statement command)
    (success : Core.execute state command = .ok (next, result)) :
    ReadRefines state.database command result := by
  cases translated with
  | query =>
      rcases CoreReadSemantics.execute_query_denotes success with
        ⟨table, found, _, denotes⟩
      exact ⟨table, found, denotes⟩
  | count =>
      rcases CoreReadSemantics.execute_count_denotes success with
        ⟨table, count, found, _, rows, exactCount⟩
      exact ⟨table, count, found, rows, exactCount⟩
  | sum =>
      rcases CoreReadSemantics.execute_sum_denotes success with
        ⟨table, value, found, summed, _, rows⟩
      exact ⟨table, value, found, summed, rows⟩
  | extreme =>
      rcases CoreReadSemantics.execute_extreme_denotes success with
        ⟨table, found, _, rows⟩
      exact ⟨table, found, rows⟩
  | group =>
      rcases CoreReadSemantics.execute_group_denotes success with
        ⟨table, found, _, denotes⟩
      exact ⟨table, found, denotes⟩
  | join =>
      rcases CoreReadSemantics.execute_join_denotes success with
        ⟨left, right, leftFound, rightFound, _, denotes⟩
      exact ⟨left, right, leftFound, rightFound, denotes⟩

end CoreSQLReadText

end SQLeanite
