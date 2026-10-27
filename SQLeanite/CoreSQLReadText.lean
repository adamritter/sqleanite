import SQLeanite.CoreSQLText
import SQLeanite.CoreCollationRead
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
      (plainSource : source.schema = none ∧ source.subquerySql = none ∧ source.joinOn = none)
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
      (plainSource : source.schema = none ∧ source.subquerySql = none ∧ source.joinOn = none)
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
      (plainSource : source.schema = none ∧ source.subquerySql = none ∧ source.joinOn = none)
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
      (plainSource : source.schema = none ∧ source.subquerySql = none ∧ source.joinOn = none)
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
      (plainSource : source.schema = none ∧ source.subquerySql = none ∧ source.joinOn = none)
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

private def selectExecution (width : Nat)
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

/-- A two-arm compound plan expressed only in live Core commands. -/
def executeBinaryPlan (state : Core.State) (left : Core.Command)
    (operation : CompoundOp) (right : Core.Command) :
    Except String (Core.State × List Core.Result) := do
  let (leftNext, leftResult) ← Core.execute state left
  let (rightNext, rightResult) ← Core.execute leftNext right
  unless readWidth left = readWidth right do
    throw "SELECTs to the left and right of a compound operator must have the same number of result columns"
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
      have leftSource := translatedRead_sources_nonempty leftTranslated
      have rightSource := translatedRead_sources_nonempty rightTranslated
      have noCollation : CoreSQL.requiresCompoundCollation select = false := by
        simp [CoreSQL.requiresCompoundCollation, height, CoreSQL.resultCollationFuel,
          compounds, leftColumns, rightColumns, leftSource, rightSource, armNoCompounds]
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
        simp [CoreSQL.requiresCompoundCollation, translatedCompound_resultCollation_false select.compoundHeight translated]
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
