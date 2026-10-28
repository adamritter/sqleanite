import SQLeanite.CoreSQLText
import SQLeanite.CoreEndToEnd

namespace SQLeanite
namespace CoreSQLWriteText

/-!
# Supported SQL write text to durable Core commands

This module makes the write side of the text boundary explicit.  The relation
below is independent of execution success: its premises are parser and
translation equations plus the syntactic restrictions of the supported Core
surface.  The first version covers one persisted command per SQL statement;
multi-row INSERT and multi-statement transaction traces are composed later.
-/

private def oneResult
    (execution : Except String (Core.State × Core.Result)) :
    Except String (Core.State × List Core.Result) :=
  (fun outcome => (outcome.1, [outcome.2])) <$> execution

/-- A parsed statement translates to exactly one persisted Core command. -/
inductive TranslatedWrite (state : Core.State) :
    Statement → CoreEndToEnd.WriteCommand → Prop where
  | createTable (name : String) (columns : Array ColumnDef)
      (constraints : Array TableConstraintDef) (ifNotExists : Bool)
      (schema : Core.Schema)
      (ready : CoreSQL.prepareCreateTable state name ifNotExists = .ok true)
      (translated : CoreSQL.schema name columns constraints = .ok schema)
      (noAuto : schema.autoIncrement = false)
      (noUnique : (columns.any (·.unique) ||
        constraints.any (fun constraint => !constraint.primaryKey)) = false)
      (noChecks : (CoreCheck.collect columns constraints).isEmpty = true)
      (noGenerated : columns.all (fun column => column.generated.isNone) = true)
      (noDeclaredCollation : columns.all (fun column => column.collation.toLower == "binary") = true)
      (noReferences : (columns.all (fun column => column.references.isNone) &&
        constraints.all (fun constraint => constraint.references.isNone)) = true) :
      TranslatedWrite state
        (.createTable name columns constraints ifNotExists)
        (.createTable schema)
  | createIndex (name table : String) (expression : Expr)
      (ifNotExists : Bool) (stored : Core.Table) (columnName : String)
      (columnIndex : Nat)
      (ready : CoreSQL.prepareCreateIndex state name ifNotExists (CoreSQL.resolveTableName state table) = .ok true)
      (found : state.database.findTable? (CoreSQL.resolveTableName state table) =
        some stored)
      (expressionName : CoreSQL.indexColumnName? expression = some columnName)
      (columnFound : CoreSQL.indexColumn stored.schema columnName = .ok columnIndex) :
      TranslatedWrite state
        (.createIndex name table #[expression] false none ifNotExists)
        (.createIndex (CoreSQL.resolveTableName state table)
          { name := name, column := columnIndex })
  | insert (table : String) (columns : Option (Array String))
      (expressions : Array Expr) (conflict : ConflictAction)
      (allowed : conflict = .default ∨ conflict = .abort)
      (stored : Core.Table) (values : List Core.Value)
      (ordinarySchema : conflict = .default → CoreDefaultConflict.active stored.schema = false)
      (noAuto : stored.schema.autoIncrement = false)
      (found : state.database.findTable? (CoreSQL.resolveTableName state table) =
        some stored)
      (noRegisterReads : expressions.any CoreLastInsert.uses = false)
      (translated : CoreSQL.rowValues stored.schema columns expressions =
        .ok values) :
      TranslatedWrite state (.insert table columns #[expressions] conflict)
        (.insert (CoreSQL.resolveTableName state table) values)
  | replace (table : String) (columns : Option (Array String))
      (expressions : Array Expr) (stored : Core.Table)
      (values : List Core.Value)
      (ordinary : CoreSQL.hasReplaceKeys stored = false)
      (noAuto : stored.schema.autoIncrement = false)
      (found : state.database.findTable? (CoreSQL.resolveTableName state table) =
        some stored)
      (noRegisterReads : expressions.any CoreLastInsert.uses = false)
      (translated : CoreSQL.rowValues stored.schema columns expressions =
        .ok values) :
      TranslatedWrite state
        (.insert table columns #[expressions] .replace)
        (.replace (CoreSQL.resolveTableName state table) values)
  | delete (table : String) (alias : Option String) (where_ : Option Expr)
      (stored : Core.Table) (predicate : Option Core.Predicate)
      (found : state.database.findTable? (CoreSQL.resolveTableName state table) =
        some stored)
      (namesBound : CoreSQL.writeNamesBound stored.schema table alias #[] where_ = true)
      (translated : where_.mapM (CoreSQL.predicate stored.schema) =
        .ok predicate) :
      TranslatedWrite state (.delete table alias where_ #[])
        (.deleteWhere (CoreSQL.resolveTableName state table) predicate)
  | update (table : String) (alias : Option String)
      (assignments : Array (String × Expr)) (where_ : Option Expr)
      (conflict : ConflictAction)
      (allowed : conflict = .default ∨ conflict = .abort)
      (stored : Core.Table) (updates : List (Nat × Core.Value))
      (predicate : Option Core.Predicate)
      (ordinarySchema : conflict = .default → CoreDefaultConflict.active stored.schema = false)
      (noChecks : stored.hasChecks = false)
      (found : state.database.findTable? (CoreSQL.resolveTableName state table) =
        some stored)
      (namesBound : CoreSQL.writeNamesBound stored.schema table alias assignments where_ = true)
      (assignmentsTranslated :
        CoreSQL.updateAssignments stored.schema assignments.toList =
          .ok updates)
      (predicateTranslated : where_.mapM
        (CoreSQL.predicate stored.schema) = .ok predicate) :
      TranslatedWrite state
        (.update table alias assignments where_ conflict)
        (.updateWhere (CoreSQL.resolveTableName state table) updates predicate)
  | commit : TranslatedWrite state .commit .commit

theorem executeStatement_eq_core
    {state : Core.State} {statement : Statement}
    {command : CoreEndToEnd.WriteCommand}
    (translated : TranslatedWrite state statement command) :
    CoreSQL.executeStatement state statement =
      oneResult (Core.execute state command.toCore) := by
  cases translated with
  | createTable name columns constraints ifNotExists schema ready translation noAuto noUnique noChecks noGenerated noDeclaredCollation noReferences =>
      cases outcome : Core.execute state (.createTable schema) <;>
        simp [CoreSQL.executeStatement, ready, translation, noAuto, noUnique, noChecks, noGenerated, noDeclaredCollation, noReferences, outcome, Except.map,
        CoreSQL.executeCommand_eq_core, CoreEndToEnd.WriteCommand.toCore,
        bind, Functor.map, Except.bind, pure, Except.pure, pure, oneResult]
  | createIndex name table expression ifNotExists stored columnName
      columnIndex ready found expressionName columnFound =>
      simp [CoreSQL.executeStatement, ready, found, expressionName, columnFound,
        CoreSQL.executeCommand_eq_core, CoreEndToEnd.WriteCommand.toCore,
        bind, Functor.map, Except.bind, pure, Except.pure, pure, oneResult]
  | insert table columns expressions conflict allowed stored values ordinarySchema noAuto found
      noRegisterReads translation =>
      rcases allowed with rfl | rfl <;>
        simp [CoreSQL.executeStatement, CoreSQL.automaticTable, found, ordinarySchema, noAuto,
          CoreSQL.insertRows_singleton, noRegisterReads, translation,
          CoreSQL.executeCommand_eq_core, CoreEndToEnd.WriteCommand.toCore,
          bind, Functor.map, Except.bind, pure, Except.pure, pure, oneResult]
  | replace table columns expressions stored values ordinary noAuto found noRegisterReads translation =>
      simp [CoreSQL.executeStatement, CoreSQL.automaticTable, found, ordinary, noAuto, CoreSQL.insertRows_singleton,
        noRegisterReads, translation, CoreSQL.executeCommand_eq_core,
        CoreEndToEnd.WriteCommand.toCore, bind, Functor.map, Except.bind, pure,
        pure, Except.pure, oneResult]
  | delete table alias where_ stored predicate found namesBound translation =>
      simp [CoreSQL.executeStatement, found, namesBound, translation,
        CoreSQL.executeCommand_eq_core, CoreEndToEnd.WriteCommand.toCore,
        bind, Functor.map, Except.bind, pure, Except.pure, pure, oneResult]
  | update table alias assignments where_ conflict allowed stored updates
      predicate ordinarySchema noChecks found namesBound assignmentsTranslated predicateTranslated =>
      rcases allowed with rfl | rfl <;>
        simp [CoreSQL.executeStatement, found, ordinarySchema, noChecks, namesBound, assignmentsTranslated,
          predicateTranslated, CoreSQL.executeCommand_eq_core,
          CoreEndToEnd.WriteCommand.toCore, bind, Functor.map, Except.bind,
          pure, Except.pure, pure, oneResult]
  | commit => rfl

/-- Multi-row INSERT/REPLACE translates to the exact Core command trace run
by the live recursive statement executor. -/
inductive TranslatedInsertRows (state : Core.State) :
    Statement → List CoreEndToEnd.WriteCommand → Prop where
  | insert (table : String) (columns : Option (Array String))
      (rows : Array (Array Expr)) (conflict : ConflictAction)
      (allowed : conflict = .default ∨ conflict = .abort)
      (stored : Core.Table) (values : List (List Core.Value))
      (ordinarySchema : conflict = .default → CoreDefaultConflict.active stored.schema = false)
      (noAuto : stored.schema.autoIncrement = false)
      (found : state.database.findTable? (CoreSQL.resolveTableName state table) =
        some stored)
      (noRegisterReads : rows.any (fun row => row.any CoreLastInsert.uses) = false)
      (translated : rows.toList.mapM
        (CoreSQL.inputRowValues stored.schema columns (1 < rows.size)) = .ok values) :
      TranslatedInsertRows state (.insert table columns rows conflict)
        (values.map fun row =>
          .insert (CoreSQL.resolveTableName state table) row)
  | replace (table : String) (columns : Option (Array String))
      (rows : Array (Array Expr)) (stored : Core.Table)
      (values : List (List Core.Value))
      (ordinary : CoreSQL.hasReplaceKeys stored = false)
      (noAuto : stored.schema.autoIncrement = false)
      (found : state.database.findTable? (CoreSQL.resolveTableName state table) =
        some stored)
      (noRegisterReads : rows.any (fun row => row.any CoreLastInsert.uses) = false)
      (translated : rows.toList.mapM
        (CoreSQL.inputRowValues stored.schema columns (1 < rows.size)) = .ok values) :
      TranslatedInsertRows state (.insert table columns rows .replace)
        (values.map fun row =>
          .replace (CoreSQL.resolveTableName state table) row)

def executeWriteCommands (state : Core.State)
    (commands : List CoreEndToEnd.WriteCommand) :
    Except String (Core.State × List Core.Result) :=
  CoreSQL.runCoreCommands state (commands.map (·.toCore))

theorem map_toCore_inserts (table : String)
    (values : List (List Core.Value)) :
    (values.map fun row =>
      CoreEndToEnd.WriteCommand.insert table row).map (·.toCore) =
      values.map fun row => Core.Command.insert table row := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [induction, CoreEndToEnd.WriteCommand.toCore]

theorem map_toCore_replaces (table : String)
    (values : List (List Core.Value)) :
    (values.map fun row =>
      CoreEndToEnd.WriteCommand.replace table row).map (·.toCore) =
      values.map fun row => Core.Command.replace table row := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [induction, CoreEndToEnd.WriteCommand.toCore]

theorem map_comp_toCore_inserts (table : String)
    (values : List (List Core.Value)) :
    values.map ((fun command : CoreEndToEnd.WriteCommand => command.toCore) ∘
      fun row => CoreEndToEnd.WriteCommand.insert table row) =
      values.map fun row => Core.Command.insert table row := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [Function.comp_apply, CoreEndToEnd.WriteCommand.toCore, induction]

theorem map_comp_toCore_replaces (table : String)
    (values : List (List Core.Value)) :
    values.map ((fun command : CoreEndToEnd.WriteCommand => command.toCore) ∘
      fun row => CoreEndToEnd.WriteCommand.replace table row) =
      values.map fun row => Core.Command.replace table row := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [Function.comp_apply, CoreEndToEnd.WriteCommand.toCore, induction]

theorem executeStatement_insertRows_eq_core
    {state : Core.State} {statement : Statement}
    {commands : List CoreEndToEnd.WriteCommand}
    (translated : TranslatedInsertRows state statement commands) :
    CoreSQL.executeStatement state statement =
      executeWriteCommands state commands := by
  cases translated with
  | insert table columns rows conflict allowed stored values ordinarySchema noAuto found noRegisterReads translation =>
      rcases allowed with rfl | rfl <;>
        simp [CoreSQL.executeStatement, CoreSQL.automaticTable, found, ordinarySchema, noAuto,
          CoreSQL.insertRows_eq_runCoreCommands, noRegisterReads, translation,
          executeWriteCommands, map_toCore_inserts, map_comp_toCore_inserts,
          bind, Functor.map, Except.bind, pure, Except.pure, pure]
  | replace table columns rows stored values ordinary noAuto found noRegisterReads translation =>
      simp [CoreSQL.executeStatement, CoreSQL.automaticTable, found, ordinary, noAuto,
        CoreSQL.insertRows_eq_runCoreCommands, noRegisterReads, translation,
        executeWriteCommands, map_toCore_replaces, map_comp_toCore_replaces,
        bind, Functor.map, Except.bind, pure, Except.pure, pure]

/-- Command-by-command logical effects for a persisted write trace. -/
inductive WriteTraceEffect : List CoreEndToEnd.WriteCommand → Core.State →
    Core.State → List Core.Result → Prop where
  | nil (state : Core.State) : WriteTraceEffect [] state state []
  | cons {command : CoreEndToEnd.WriteCommand}
      {commands : List CoreEndToEnd.WriteCommand}
      {state middle next : Core.State} {result : Core.Result}
      {results : List Core.Result}
      (head : CoreEndToEnd.WriteEffect command state middle result)
      (tail : WriteTraceEffect commands middle next results) :
      WriteTraceEffect (command :: commands) state next (result :: results)

theorem executeWriteCommands_exact :
    ∀ (commands : List CoreEndToEnd.WriteCommand)
      (state next : Core.State) (results : List Core.Result),
      executeWriteCommands state commands = .ok (next, results) →
      WriteTraceEffect commands state next results
  | [], state, next, results, success => by
      simp [executeWriteCommands, CoreSQL.runCoreCommands] at success
      rcases success with ⟨rfl, rfl⟩
      exact .nil state
  | command :: commands, state, next, results, success => by
      unfold executeWriteCommands at success
      simp only [List.map_cons, CoreSQL.runCoreCommands] at success
      cases headExecution : Core.execute state command.toCore with
      | error message =>
          simp [headExecution, bind, Functor.map, Except.bind] at success
      | ok headOutcome =>
          rcases headOutcome with ⟨middle, result⟩
          cases tailExecution : CoreSQL.runCoreCommands middle
              (commands.map (·.toCore)) with
          | error message =>
              simp [headExecution, tailExecution, bind, Functor.map,
                Except.bind] at success
          | ok tailOutcome =>
              rcases tailOutcome with ⟨actualNext, actualResults⟩
              simp [headExecution, tailExecution, bind, Functor.map,
                Except.bind, pure, Except.pure, pure] at success
              rcases success with ⟨rfl, rfl⟩
              exact .cons (CoreEndToEnd.execute_write_exact command
                headExecution) (executeWriteCommands_exact commands middle
                  actualNext actualResults tailExecution)

theorem executeWriteCommands_append (state : Core.State)
    (left right : List CoreEndToEnd.WriteCommand) :
    executeWriteCommands state (left ++ right) =
      match executeWriteCommands state left with
      | .error message => .error message
      | .ok (middle, leftResults) =>
          match executeWriteCommands middle right with
          | .error message => .error message
          | .ok (next, rightResults) =>
              .ok (next, leftResults ++ rightResults) := by
  unfold executeWriteCommands
  rw [List.map_append, CoreSQL.runCoreCommands_append]
  rfl

/-- One SQL write statement may translate to one Core command or to the
command block generated by a multi-row INSERT/REPLACE. -/
inductive TranslatedWriteBlock (state : Core.State) :
    Statement → List CoreEndToEnd.WriteCommand → Prop where
  | single {statement : Statement} {command : CoreEndToEnd.WriteCommand}
      (translated : TranslatedWrite state statement command) :
      TranslatedWriteBlock state statement [command]
  | insertRows {statement : Statement}
      {commands : List CoreEndToEnd.WriteCommand}
      (translated : TranslatedInsertRows state statement commands) :
      TranslatedWriteBlock state statement commands

theorem executeStatement_block_eq_core
    {state : Core.State} {statement : Statement}
    {commands : List CoreEndToEnd.WriteCommand}
    (translated : TranslatedWriteBlock state statement commands) :
    CoreSQL.executeStatement state statement =
      executeWriteCommands state commands := by
  cases translated with
  | single translated =>
      rw [executeStatement_eq_core translated]
      unfold oneResult executeWriteCommands
      simp only [List.map_cons, List.map_nil, CoreSQL.runCoreCommands]
      cases execution : Core.execute state _ <;>
        simp [execution, bind, Functor.map, Except.bind, pure, Except.pure, pure] <;>
        rfl
  | insertRows translated =>
      exact executeStatement_insertRows_eq_core translated

/-- A write-only statement list whose translation is threaded through every
possible successful intermediate state.  No concrete execution result is
stored in the support witness. -/
inductive TranslatedWriteTrace : Core.State → List Statement →
    List CoreEndToEnd.WriteCommand → Prop where
  | nil (state : Core.State) : TranslatedWriteTrace state [] []
  | cons {state : Core.State} {statement : Statement}
      {statements : List Statement}
      {headCommands tailCommands : List CoreEndToEnd.WriteCommand}
      (head : TranslatedWriteBlock state statement headCommands)
      (tail : ∀ next results,
        executeWriteCommands state headCommands = .ok (next, results) →
        TranslatedWriteTrace next statements tailCommands) :
      TranslatedWriteTrace state (statement :: statements)
        (headCommands ++ tailCommands)

theorem runStatements_eq_writeTrace
    {state : Core.State} {statements : List Statement}
    {commands : List CoreEndToEnd.WriteCommand}
    (translated : TranslatedWriteTrace state statements commands) :
    CoreSQL.runStatements state statements =
      executeWriteCommands state commands := by
  induction translated with
  | nil state => rfl
  | @cons state statement statements headCommands tailCommands head tail
      induction =>
      unfold CoreSQL.runStatements
      rw [executeStatement_block_eq_core head,
        executeWriteCommands_append]
      cases headExecution : executeWriteCommands state headCommands with
      | error message => simp [headExecution]
      | ok outcome =>
          rcases outcome with ⟨middle, headResults⟩
          have tailTranslation := tail middle headResults headExecution
          have tailEquality := induction middle headResults headExecution
          simp only
          rw [tailEquality]
          cases tailExecution : executeWriteCommands middle tailCommands with
          | error message =>
              simp [headExecution, tailExecution, bind, Functor.map,
                Except.bind, pure, Except.pure, pure]

          | ok outcome =>
              rcases outcome with ⟨next, tailResults⟩
              simp [headExecution, tailExecution, bind, Functor.map,
                Except.bind, pure, Except.pure, pure]

inductive SupportedWriteTraceText (state : Core.State) (text : String)
    (commands : List CoreEndToEnd.WriteCommand) : Prop where
  | intro (statements : Array Statement)
      (parsed : CoreTokenGrammar.Parses text statements)
      (translated : TranslatedWriteTrace state statements.toList commands) :
      SupportedWriteTraceText state text commands

theorem execute_trace_eq_core
    {state : Core.State} {text : String}
    {commands : List CoreEndToEnd.WriteCommand}
    (supported : SupportedWriteTraceText state text commands) :
    CoreSQL.execute state text = executeWriteCommands state commands := by
  rcases supported with ⟨statements, parsed, translated⟩
  rcases parsed with ⟨certificate, certified, statementList⟩
  simp only [CoreSQL.execute, certified, statementList,
    bind, Functor.map, Except.bind]
  exact runStatements_eq_writeTrace translated

theorem writeTrace_success
    {state next : Core.State} {text : String}
    {commands : List CoreEndToEnd.WriteCommand} {results : List Core.Result}
    (supported : SupportedWriteTraceText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results)) :
    WriteTraceEffect commands state next results := by
  exact executeWriteCommands_exact commands state next results
    ((execute_trace_eq_core supported).symm.trans success)

theorem executeText_trace_commit_crash_atomic
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteTraceText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain recoveredJournal) :
    WriteTraceEffect commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some next.database.canonicalize) := by
  exact ⟨writeTrace_success supported success,
    CoreDurability.rollbackWrites_represents_crash_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain recoveredJournal outcome⟩

theorem executeText_trace_returned_recovers_new
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteTraceText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes .committed)
      recoveredMain recoveredJournal) :
    WriteTraceEffect commands state next results ∧
      CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some next.database.canonicalize := by
  exact ⟨writeTrace_success supported success,
    CoreDurability.rollbackWrites_represents_returned_recovers_new
      next.database oldImage writes newRepresents recoveredMain
      recoveredJournal outcome⟩

theorem executeText_trace_recovery_crash_trace_atomic
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteTraceText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain finalMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain (some journal))
    (recoveryCrashes : GrowableStorage.RecoveryCrashTrace journal
      recoveredMain finalMain) :
    WriteTraceEffect commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some next.database.canonicalize) := by
  exact ⟨writeTrace_success supported success,
    CoreDurability.rollbackWrites_represents_recovery_crash_trace_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain finalMain journal outcome recoveryCrashes⟩

inductive SupportedInsertRowsText (state : Core.State) (text : String)
    (commands : List CoreEndToEnd.WriteCommand) : Prop where
  | intro (statement : Statement)
      (parsed : CoreTokenGrammar.Parses text #[statement])
      (translated : TranslatedInsertRows state statement commands) :
      SupportedInsertRowsText state text commands

theorem execute_insertRows_eq_core
    {state : Core.State} {text : String}
    {commands : List CoreEndToEnd.WriteCommand}
    (supported : SupportedInsertRowsText state text commands) :
    CoreSQL.execute state text = executeWriteCommands state commands := by
  rcases supported with ⟨statement, parsed, translated⟩
  rcases parsed with ⟨certificate, certified, statements⟩
  simp only [CoreSQL.execute, certified, statements, bind, Functor.map, Except.bind,
    CoreSQL.runStatements]
  rw [executeStatement_insertRows_eq_core translated]
  cases execution : executeWriteCommands state commands <;>
    simp [execution, bind, Functor.map, Except.bind, pure, Except.pure, pure]

theorem insertRows_trace_success
    {state next : Core.State} {text : String}
    {commands : List CoreEndToEnd.WriteCommand} {results : List Core.Result}
    (supported : SupportedInsertRowsText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results)) :
    WriteTraceEffect commands state next results := by
  exact executeWriteCommands_exact commands state next results
    ((execute_insertRows_eq_core supported).symm.trans success)

theorem executeText_insertRows_commit_crash_atomic
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedInsertRowsText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain recoveredJournal) :
    WriteTraceEffect commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some next.database.canonicalize) := by
  exact ⟨insertRows_trace_success supported success,
    CoreDurability.rollbackWrites_represents_crash_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain recoveredJournal outcome⟩

theorem executeText_insertRows_returned_recovers_new
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedInsertRowsText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes .committed)
      recoveredMain recoveredJournal) :
    WriteTraceEffect commands state next results ∧
      CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some next.database.canonicalize := by
  exact ⟨insertRows_trace_success supported success,
    CoreDurability.rollbackWrites_represents_returned_recovers_new
      next.database oldImage writes newRepresents recoveredMain
      recoveredJournal outcome⟩

theorem executeText_insertRows_recovery_crash_trace_atomic
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedInsertRowsText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain finalMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain (some journal))
    (recoveryCrashes : GrowableStorage.RecoveryCrashTrace journal
      recoveredMain finalMain) :
    WriteTraceEffect commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some next.database.canonicalize) := by
  exact ⟨insertRows_trace_success supported success,
    CoreDurability.rollbackWrites_represents_recovery_crash_trace_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain finalMain journal outcome recoveryCrashes⟩

/-- A single supported write statement beginning at an actual SQL string. -/
inductive SupportedWriteText (state : Core.State) (text : String)
    (command : CoreEndToEnd.WriteCommand) : Prop where
  | intro (statement : Statement)
      (parsed : CoreTokenGrammar.Parses text #[statement])
      (translated : TranslatedWrite state statement command) :
      SupportedWriteText state text command

theorem execute_eq_core
    {state : Core.State} {text : String}
    {command : CoreEndToEnd.WriteCommand}
    (supported : SupportedWriteText state text command) :
    CoreSQL.execute state text = oneResult
      (Core.execute state command.toCore) := by
  rcases supported with ⟨statement, parsed, translated⟩
  rcases parsed with ⟨certificate, certified, statements⟩
  simp only [CoreSQL.execute, certified, statements, bind, Functor.map, Except.bind,
    CoreSQL.runStatements]
  rw [executeStatement_eq_core translated]
  unfold oneResult
  cases Core.execute state command.toCore <;> rfl

theorem core_success_of_execute
    {state next : Core.State} {text : String}
    {command : CoreEndToEnd.WriteCommand} {result : Core.Result}
    (supported : SupportedWriteText state text command)
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    Core.execute state command.toCore = .ok (next, result) := by
  have mapped : oneResult (Core.execute state command.toCore) =
      .ok (next, [result]) := (execute_eq_core supported).symm.trans success
  unfold oneResult at mapped
  cases execution : Core.execute state command.toCore with
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

/-- Supported SQL write text, not a pre-parsed command, composes with the
concrete page-level rollback theorem.  The post-image evidence must identify
the actual construction path (ordinary localized, bulk, or freelist-padded);
an opaque decoder equality is no longer an admissible premise. -/
theorem executeText_commit_crash_atomic
    (text : String) (command : CoreEndToEnd.WriteCommand)
    (state next : Core.State) (result : Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteText state text command)
    (success : CoreSQL.execute state text = .ok (next, [result]))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (postImage : CoreDurability.PostImageCertificate oldImage writes
      next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain recoveredJournal) :
    CoreEndToEnd.WriteEffect command state next result ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some next.database.canonicalize) := by
  exact CoreEndToEnd.executeCommand_commit_crash_atomic command state next
    result oldImage writes (core_success_of_execute supported success)
    oldRepresents postImage.representsDatabase phase recoveredMain
    recoveredJournal outcome

theorem executeText_returned_recovers_new
    (text : String) (command : CoreEndToEnd.WriteCommand)
    (state next : Core.State) (result : Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteText state text command)
    (success : CoreSQL.execute state text = .ok (next, [result]))
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes .committed)
      recoveredMain recoveredJournal) :
    CoreEndToEnd.WriteEffect command state next result ∧
      CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some next.database.canonicalize := by
  exact CoreEndToEnd.executeCommand_returned_recovers_new command state next
    result oldImage writes (core_success_of_execute supported success)
    newRepresents recoveredMain recoveredJournal outcome

theorem executeText_recovery_crash_trace_atomic
    (text : String) (command : CoreEndToEnd.WriteCommand)
    (state next : Core.State) (result : Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteText state text command)
    (success : CoreSQL.execute state text = .ok (next, [result]))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain finalMain :
      GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain (some journal))
    (recoveryCrashes : GrowableStorage.RecoveryCrashTrace journal
      recoveredMain finalMain) :
    CoreEndToEnd.WriteEffect command state next result ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some next.database.canonicalize) := by
  exact CoreEndToEnd.executeCommand_recovery_crash_trace_atomic command state
    next result oldImage writes (core_success_of_execute supported success)
    oldRepresents newRepresents phase recoveredMain finalMain journal outcome
    recoveryCrashes

end CoreSQLWriteText
end SQLeanite
