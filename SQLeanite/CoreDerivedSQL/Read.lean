import SQLeanite.CoreTriggerProgram.Rows
import SQLeanite.CoreTriggerProgram.InputEffects
import SQLeanite.CoreTriggerProgram.RegisterInput
import SQLeanite.CoreTriggerProgram.ValuesInput
import SQLeanite.CorePartialSQL
import SQLeanite.CoreDerivedSQL.Binding
import SQLeanite.CoreForeignKey
import SQLeanite.CoreGeneratedSQL
import SQLeanite.CoreUpsertSQL
import SQLeanite.CoreViewRename
import SQLeanite.CoreTriggerControl

namespace SQLeanite.CoreDerivedSQL

def read : Nat → Core.State → List Binding → Statement → Except String (List Core.Result)
  | 0, _, _, _ => .error "derived-query nesting limit exceeded"
  | fuel + 1, state, bindings, sql => do
      match sql with
      | .select query =>
          let (temporary, query) ← prepare fuel state bindings query
          if CoreScalarQuery.has query.compoundHeight query then
            return [(← executeScalar fuel temporary bindings query).result]
          if CoreWindow.has query then return [← CoreWindow.execute temporary query]
          let (_, results) ← CoreConnectionSQL.executeStatement temporary (.select query) ""
          return results
      | .values rows =>
          let (_, results) ← CoreConnectionSQL.executeStatement state (.select (valuesQuery rows)) ""
          return results
      | .withRecursive name aliases seed step all body _ =>
          unless ← statementReferences fuel name body do return ← read fuel state bindings body
          let lowered ← recursiveStep name all step.compoundHeight step
          let (temporary, seed) ← prepare fuel state bindings seed
          let seed := CoreConnectionSQL.select temporary seed.compoundHeight seed
          let definitions ← resultDefinitions temporary seed aliases
          let (metadataState, table) ← materializeRows temporary definitions []
          let (metadataState, boundStep) ← prepareWithSources [] true fuel metadataState ({name,table} :: bindings) step
          discard <| CoreScalarQuery.executePrepared
            (fun mode depth state parents query => prepareWithSources parents mode depth state bindings query)
            true fuel metadataState [] { boundStep with limit := some 0 }
          let compound := {
            seed with
            compounds := seed.compounds.push ((if all then .unionAll else .unionDistinct),boundStep) }
          let collations ← CoreSQL.resultCollationsFuel compound.compoundHeight metadataState compound
          let kinds ← collations.mapM (fun collation => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName collation))
          let selection ← CoreSQL.executeSelect temporary seed
          let (seen, initial) := enqueueCollated all kinds [] selection.result.rows
          let rows ← recursiveRows temporary bindings name definitions lowered all kinds 100000 initial seen []
          let (temporary, table) ← materializeRows temporary definitions rows
          read fuel temporary ({name, table} :: bindings) body
      | .withCte name aliases source body materialization =>
          unless ← statementReferences fuel name body do return ← read fuel state bindings body
          let query ← match source with
            | .select query => pure query
            | .values rows => pure (valuesQuery rows)
            | _ => throw "unsupported CTE source"
          if query.sources.any (fun source => source.name.toLower == name.toLower) then
            throw s!"circular reference: {name}"
          let flatten := materialization != .materialized && CoreJsonTable.flattenable query
          let original := query
          let (temporary, query) ← prepare fuel state bindings query
          if flatten then
            if let .select outer := body then
              if outer.sources.size == 1 && outer.compounds.isEmpty then
                if let some source := outer.sources[0]? then
                  if source.name.toLower == name.toLower && source.schema.isNone &&
                      source.subquerySql.isNone && source.functionArgs.isNone then
                    let definitions ← resultDefinitions temporary query aliases
                    let query := if aliases.isEmpty then query else { query with
                      columns := query.columns.mapIdx fun i col =>
                        { col with alias := definitions[i]?.map (·.name) } }
                    let flattened ← CoreJsonTable.inlineProjection temporary outer query source original
                    let (_, results) ← CoreConnectionSQL.executeStatement temporary (.select flattened) ""
                    return results
          let (temporary, table) ← materialize temporary query aliases
          read fuel temporary ({name, table} :: bindings) body
      | _ => throw "unsupported writable CTE body"

def hasDerived : Nat → Select → Bool
  | 0, _ => true
  | fuel + 1, query => CoreScalarQuery.has query.compoundHeight query || CoreWindow.has query || query.sources.any (fun source => source.subquerySql.isSome || source.schema.isSome || source.functionArgs.isSome ||
        (CorePragmaTable.names source.name).isSome) ||
      query.compounds.any (fun arm => hasDerived fuel arm.2)

def executeRead (state : Core.State) (sql : Statement) :
    Except String (Core.State × List Core.Result) := do
  let results ← read 256 state [] sql
  return (state, results)

theorem executeRead_preserves_state (state next : Core.State) (sql : Statement)
    (results : List Core.Result) (success : executeRead state sql = .ok (next, results)) :
    next = state := by
  unfold executeRead at success
  cases outcome : read 256 state [] sql with
  | error message => simp [outcome, bind, Except.bind] at success
  | ok rows =>
      simp [outcome, bind, Except.bind, pure, Except.pure] at success
      exact success.1.symm

/-- Shared coroutine admission for the ordinary INSERT SELECT path. -/
def streamingValues (query : Select) : Option (Array (Array Expr)) :=
  CoreTriggerProgram.streamingInput query

theorem streamingValues_ordered (query : Select) (ordered : query.orderBy.isEmpty = false) :
    streamingValues query = none := by
  exact CoreTriggerProgram.streamingInput_ordered query ordered

/-- Connection-level row tracking reuses the existing per-row executors.
The source-free Core SQL command translation keeps its ordinary AST domain. -/
def executeConnectionStatement (state : Core.State) (sql : Statement) (source : String)
    (registers : Option CoreSQL.RowInput := none) :
    Except String (Core.State × List Core.Result) := do
  let sql ← CoreDeclaredCollationSQL.statement state sql
  let preparation ← match CoreForeignKey.target? sql with
    | none => pure none
    | some target => CoreGeneratedSQL.preparation state target
  let preparation := match registers with
    | none => preparation
    | some input => some {
        row := fun state table action _ => match preparation with
          | none => .ok (some input)
          | some prepare => prepare.row state table action input }
  if !state.foreignKeys && preparation.isNone then return ← CoreConnectionSQL.executeStatement state sql source
  let bound := CoreConnectionSQL.statement state sql
  let (next, results) ← match bound with
    | .insert table columns rows conflict returning =>
        if CoreSQL.automaticTable state table then
          CoreSQL.executeAutoInsert state table columns (.inl rows) conflict returning preparation
        else CoreSQL.executeInsertReturning state table columns (.inl rows) conflict returning preparation
    | .insertSelect table columns query conflict returning =>
        if CoreLastInsert.queryUses query.compoundHeight query then
          CoreSQL.executeRegisterInsertSelect state table columns query conflict returning preparation
        else if CoreSQL.automaticTable state table then
          CoreSQL.executeAutoInsert state table columns (.inr query) conflict returning preparation
        else CoreSQL.executeInsertReturning state table columns (.inr query) conflict returning preparation
    | .update table alias assignments condition conflict returning => do
        unless conflict == .default || conflict == .abort || conflict == .ignore || conflict == .replace do
          throw "unsupported general verified-MVP SQL: UPDATE conflict policy"
        let tableName := CoreSQL.resolveTableName state table
        let some stored := state.database.findTable? tableName | throw s!"no such table: {table}"
        unless CoreSQL.writeNamesBound stored.schema table alias assignments condition do
          let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD table }
          for expression in assignments.toList.map (·.2) ++ condition.toList do
            if let some message := SQLite.Scalar.resolutionError (fun q n => (ctx.column? q n).isSome) expression then
              throw message
          throw "unsupported general verified-MVP SQL: unbound UPDATE name"
        let (next, results) ← CoreSQL.executeUpdateReturning state tableName alias stored
          assignments.toList condition conflict returning preparation
        pure (next, if returning.isEmpty then results.map (fun result => { result with rows := [] }) else results)
    | _ => CoreSourceSQL.executeStatement state bound source
  return (CoreConnectionSQL.account state next sql results, results)

/-- Derived SELECT inputs are evaluated in a private read state. Only their
values cross back into the original connection's ordinary INSERT machinery;
private table names, counters and transaction snapshots cannot escape. -/
def insertSelect (state : Core.State) (table : String) (columns : Option (Array String))
    (query : Select) (conflict : ConflictAction) (returning : Array ResultColumn)
    (source : String) : Except String (Core.State × List Core.Result) := do
  let some stored := CoreNames.table? state.database table | throw s!"no such table: {table}"
  if let some inputs := streamingValues query then
    return ← executeConnectionStatement state (.insert table columns inputs conflict returning) source
  let (temporary, query) ← prepare 256 state [] query
  let query := CoreConnectionSQL.select state query.compoundHeight query
  let definitions ← CoreCreateTableAs.columns temporary.database query
  let preparation ← CoreGeneratedSQL.preparation state table
  let targets ← CoreSQL.prepareInsertTargets columns (.inr query) preparation
  CoreSQL.checkInsertSelectColumns stored.schema targets.columns definitions.size targets.implicitWidth
  let selected ← if CoreScalarQuery.has query.compoundHeight query then
      (·.result) <$> executeScalar 256 temporary [] query
    else if CoreWindow.has query then CoreWindow.execute temporary query
    else (·.result) <$> CoreSQL.executeSelect temporary query
  let inputs ← selected.rows.mapM CoreSQL.selectedRowExpressions
  executeConnectionStatement state (.insert table columns inputs.toArray conflict returning) source

def createTableAs (state : Core.State) (name : String) (query : Select) (guard : Bool) :
    Except String (Core.State × List Core.Result) := do
  unless ← CoreSQL.prepareCreateTable state name guard do return (state,[{}])
  let (temporary,query) ← prepare 256 state [] query
  let query := CoreConnectionSQL.select state query.compoundHeight query
  let definitions ← CoreCreateTableAs.columns temporary.database query
  let selected ← if CoreScalarQuery.has query.compoundHeight query then
      (·.result) <$> executeScalar 256 temporary [] query
    else if CoreWindow.has query then CoreWindow.execute temporary query
    else (·.result) <$> CoreSQL.executeSelect temporary query
  let schema ← CoreSQL.schema name definitions #[]
  let inputs ← selected.rows.mapM CoreSQL.selectedRowExpressions
  let values ← inputs.mapM (CoreSQL.rowValues schema none)
  let (next,_) ← CoreSQL.runCoreCommands state (.createTable schema :: values.map (Core.Command.insert name))
  let next ← CoreSQL.retainCreateTableAsSQL next name
  let results := [({} : Core.Result)]
  return (CoreConnectionSQL.account state next (.createTableAs name query guard) results,results)

def inspectViewPragma (state : Core.State) (name : String) (argument : Option Expr) (schema : Option String) :
    Except String (Core.State × List Core.Result) := do
  if schema.any (fun name => !["main","temp"].contains name.toLower) then throw s!"unknown database {schema.getD ""}"
  let target ← argument.mapM fun argument => do
    let some target := CoreSchemaPragma.argumentName argument | throw "unsupported PRAGMA argument"
    return target
  let values ← viewInspection 256 state schema name target
  let rows ← values.mapM (List.mapM SQLSurface.value)
  return (state,[{ rows }])

def executeBase (state : Core.State) (sql : Statement) (source : String)
    (registers : Option CoreSQL.RowInput := none) :
    Except String (Core.State × List Core.Result) :=
  match sql with
  | .pragma name argument schema =>
      if name.toLower == "schema_version" && argument.isNone then do
        if schema.any (fun name => !["main","temp"].contains name.toLower) then throw s!"unknown database {schema.getD ""}"
        let cookie := if schema.any (fun name => name.toLower == "temp") then 0 else state.catalog.current.schemaVersion
        let value ← SQLSurface.value (.integer (SQLite.ApplicationHeader.signed (SQLite.ApplicationHeader.word cookie)))
        return (state,[{ rows := [[value]] }])
      else if name.toLower == "encoding" && argument.isNone then do
        if schema.any (fun name => !["main","temp"].contains name.toLower) then throw s!"unknown database {schema.getD ""}"
        let encoding := match state.catalog.current.textEncoding with
          | 2 => "UTF-16le" | 3 => "UTF-16be" | _ => "UTF-8"
        let value ← SQLSurface.value (.text encoding)
        return (state,[{ rows := [[value]] }])
      else if ["index_list","index_info","index_xinfo"].contains name.toLower && !state.catalog.current.filteredIndexes.isEmpty then
        CorePartialSQL.pragma state name argument schema
      else if ["table_info","table_xinfo","table_list"].contains name.toLower && !state.catalog.current.views.isEmpty then
        inspectViewPragma state name argument schema
      else executeConnectionStatement state sql source registers
  | .createView .. | .dropView .. => CoreViewSQL.executeDDL state sql source
  | .createTrigger .. | .dropTrigger .. => CoreTriggerSQL.executeDDL state sql source
  | .createTable .. | .createStrictTable .. =>
      if CoreViewSQL.schemaNoop state sql then .ok (state,[{}])
      else executeConnectionStatement state sql source registers
  | .createTableAs name query guard =>
      if CoreViewSQL.schemaNoop state sql then .ok (state,[{}]) else

      if CoreViewSQL.uses query.compoundHeight state query || hasDerived query.compoundHeight query then createTableAs state name query guard
      else executeConnectionStatement state sql source registers
  | .insertSelect table columns query conflict returning =>
      if CoreViewSQL.uses query.compoundHeight state query || hasDerived query.compoundHeight query then insertSelect state table columns query conflict returning source
      else executeConnectionStatement state sql source registers
  | .upsert base alias clauses => do
      let transformed ← CoreDeclaredCollationSQL.statement state (.upsert base alias clauses)
      let .upsert base alias clauses := transformed | throw "invalid declared UPSERT preparation"
      let preparation ← match CoreForeignKey.target? base with
        | none => pure none
        | some target => CoreGeneratedSQL.preparation state target
      CoreUpsertSQL.execute state base alias clauses preparation
  | .withCte .. | .withRecursive .. => executeRead state sql
  | .select query =>
      if CoreViewSQL.uses query.compoundHeight state query || hasDerived query.compoundHeight query then executeRead state sql
      else executeConnectionStatement state sql source registers
  | _ => executeConnectionStatement state sql source registers

/-- Keep SQLite's live schema-hash insertion/removal order independently of
Core's physical table list. Transaction schema invalidation reloads catalog
order; private query materialization starts from the caller's cached order. -/
def schemaTransition (before next : Core.State) (sql : Statement) : Core.State := Id.run do
  let original := before.schemaHashValue
  let oldNames := before.database.tables.map (·.schema.name) ++ before.catalog.current.views.map (·.definition.name)
  let newNames := next.database.tables.map (·.schema.name) ++ next.catalog.current.views.map (·.definition.name)
  let mut cached := original
  for name in oldNames.filter (fun name => !newNames.contains name) do
    cached := SQLite.SchemaHash.remove cached name
  let catalogAdditions := (newNames.filter (fun name => !oldNames.contains name)).reverse
  let creation := cached.creation ++ catalogAdditions
  -- sqlite_sequence enters the live hash before its first AUTOINCREMENT
  -- owner, while its persistent sqlite_schema row follows that owner.
  let insertions := if catalogAdditions.contains CoreAutoIncrement.sequenceName then
      CoreAutoIncrement.sequenceName :: catalogAdditions.filter (· != CoreAutoIncrement.sequenceName)
    else catalogAdditions
  for name in insertions do
    cached := SQLite.SchemaHash.add cached name
  cached := { cached with creation }
  let mut result := { next with schemaHash := some cached }
  match sql with
  | .begin => result := { result with transactionSchemaHash := some original }
  | .commit => result := { result with transactionSchemaHash := none, schemaHashSavepoints := [] }
  | .rollback =>
      let snapshot := before.transactionSchemaHash.getD original
      result := { result with
        schemaHash := some (SQLite.SchemaHash.rollback original snapshot)
        transactionSchemaHash := none
        schemaHashSavepoints := [] }
  | .savepoint name =>
      result := { result with
        transactionSchemaHash := if before.transactionSnapshot.isNone then some original else before.transactionSchemaHash
        schemaHashSavepoints := (name, original) :: before.schemaHashSavepoints }
  | .rollbackTo name =>
      let marks := before.schemaHashSavepoints.dropWhile (fun mark => mark.1.toLower != name.toLower)
      if let some mark := marks.head? then
        result := { result with
          schemaHash := some (SQLite.SchemaHash.rollback original mark.2)
          schemaHashSavepoints := marks }
  | .release name =>
      let marks := before.schemaHashSavepoints.dropWhile (fun mark => mark.1.toLower != name.toLower)
      result := { result with
        schemaHashSavepoints := marks.drop 1
        transactionSchemaHash := if next.transactionSnapshot.isNone then none else before.transactionSchemaHash }
  | .alterRenameTable oldName newName =>
      let creation := original.creation.map fun name =>
        if name.toLower == oldName.toLower then newName else name
      result := { result with schemaHash := some (SQLite.SchemaHash.reload { original with creation }) }
  | .alterAddColumn .. | .alterDropColumn .. | .alterRenameColumn .. =>
      result := { result with schemaHash := some (SQLite.SchemaHash.reload original) }
  | _ => pure ()
  return result

def executeStatementUntriggeredWithForeign (deferredForeign : Bool) (state : Core.State) (sql : Statement) (source : String)
    (registers : Option CoreSQL.RowInput := none) :
    Except String (Core.State × List Core.Result) := do
  let state := CoreViewSQL.prepareCatalog state
  CoreViewSQL.guard state sql
  CoreTriggerSQL.guard state sql
  CorePartialSQL.guard state sql
  if let .pragma name argument schema := sql then
    if name.toLower == "foreign_keys" then return ← CoreForeignKey.pragma state argument schema
    if name.toLower == "recursive_triggers" then return ← CoreTriggerControl.pragma state argument schema
  let sql ← CoreGeneratedSQL.statement state sql
  let edges ← if state.foreignKeys then CoreForeignKey.edges state sql else pure []
  let cached := { state with schemaHash := some state.schemaHashValue }
  let input := if state.foreignKeys && !deferredForeign then { cached with foreignWrites := [] } else cached
  let hasRename := (CoreForeignKeyRename.request state sql source).isSome
  if hasRename then
    for view in state.catalog.current.views do
      match viewMetadataState 256 state view.definition.name with
      | .ok _ => pure ()
      | .error message => throw s!"error in view {view.definition.name}: {message}"
  let (next, results) ← match ← CorePartialSQL.execute? input sql source with
    | some result => pure result
    | none => executeBase input sql source registers
  let next ← CoreForeignKeyRename.execute state next sql source
  let next ← CoreViewRename.execute state next sql source
  let droppedColumn := match sql with | .alterDropColumn .. => true | _ => false
  if hasRename || droppedColumn then
    for view in next.catalog.current.views do
      match viewMetadataState 256 next view.definition.name with
      | .ok _ => pure ()
      | .error message =>
          let operation := if droppedColumn then "drop column" else "rename"
          throw s!"error in view {view.definition.name} after {operation}: {message}"
  unless edges.isEmpty || deferredForeign do CoreForeignKey.requireTransition state next edges
  let next := CorePartialSQL.removeDroppedOwners (CoreTriggerSQL.removeDroppedOwners next sql) sql
  let next := CoreViewSQL.transition state next sql
  let next ← CoreViewSQL.orderDatabase next
  let next := schemaTransition state next sql
  return (if state.foreignKeys && !deferredForeign then { next with foreignWrites := state.foreignWrites } else next, results)

def executeStatementUntriggered (state : Core.State) (sql : Statement) (source : String) :
    Except String (Core.State × List Core.Result) :=
  executeStatementUntriggeredWithForeign false state sql source

/-- Capture actual register metadata after original source preparation. The
private projection flag is restored before any trigger program can execute. -/
def executeTriggerPoint (state : Core.State) (sql : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  let (next,results) ← executeStatementUntriggeredWithForeign true { state with internalReturning := true } sql source
  return ({ next with internalReturning := state.internalReturning },results)

theorem executeTriggerPoint_restores (state next : Core.State) (sql : Statement) (source : String)
    (results : List Core.Result) (success : executeTriggerPoint state sql source = .ok (next,results)) :
    next.internalReturning = state.internalReturning := by
  unfold executeTriggerPoint at success
  cases outcome : executeStatementUntriggeredWithForeign true { state with internalReturning := true } sql source with
  | error message => simp [outcome, bind, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨actual,rows⟩
      simp [outcome, bind, Except.bind, pure, Except.pure] at success
      rcases success with ⟨rfl,rfl⟩
      rfl

/-- A REPLACE UPDATE retains the actual pre-deletion physical register image
and its original SET footprint across auxiliary DELETE programs. -/
def executeTriggerPointWithRegisters (registers : Option CoreSQL.RowInput) : CoreTriggerProgram.Executor :=
  match registers with
  | none => executeTriggerPoint
  | some input => fun state sql source => do
      let (next,results) ← executeStatementUntriggeredWithForeign true { state with internalReturning := true } sql source (some input)
      return ({ next with internalReturning := state.internalReturning },results)

theorem executeTriggerPointWithRegisters_restores (registers : Option CoreSQL.RowInput)
    (state next : Core.State) (sql : Statement) (source : String) (results : List Core.Result)
    (success : executeTriggerPointWithRegisters registers state sql source = .ok (next,results)) :
    next.internalReturning = state.internalReturning := by
  cases registers with
  | none => exact executeTriggerPoint_restores state next sql source results success
  | some input =>
      unfold executeTriggerPointWithRegisters at success
      cases outcome : executeStatementUntriggeredWithForeign true { state with internalReturning := true } sql source (some input) with
      | error message => simp [outcome, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨actual,rows⟩
          simp [outcome, bind, Except.bind, pure, Except.pure] at success
          rcases success with ⟨rfl,rfl⟩
          rfl

/-- Trigger SELECTs share the existing lexical scalar-query compiler. Their
source text and captured subqueries are never rendered from bound values. -/
def executeTriggerRead (preparing : Bool) (state : Core.State)
    (parents : List CoreScalarQuery.Frame) (query : Select) : Except String CoreScalarQuery.Result := do
  let state := { state with
    schemaProgram := state.schemaProgram || state.triggerDepth != 0 || parents.any (·.qualifiedOnly)
    triggerDepth := if parents.any (·.qualifiedOnly) then max 1 state.triggerDepth else state.triggerDepth }
  if parents.isEmpty && CoreWindow.has query && !CoreScalarQuery.has query.compoundHeight query then
    let (temporary,query) ← prepareWithSources [] preparing 256 state [] query
    let query := CoreConnectionSQL.select temporary query.compoundHeight query
    let definitions ← CoreCreateTableAs.baseColumns temporary.database query
    let result ← CoreWindow.execute temporary (if preparing then { query with limit := some 0 } else query)
    return {
      result
      width := definitions.length
      affinity := definitions.head?.bind (·.affinity)
      inputState := temporary
      inputQuery := query }
  let selected ← CoreScalarQuery.executePrepared
    (fun mode depth current frames input => prepareWithSources frames mode depth current [] input)
    preparing 256 state parents query
  return selected

def prepareTriggerStatement : Nat → List String → CoreTriggerProgram.PrepareExecutor
  | 0, _, _, _, _ => .error "too many levels of trigger recursion"
  | fuel + 1, active, state, parents, statement => do
      CoreTriggerProgram.prepareBody executeStatementUntriggered executeTriggerRead state parents statement
      if let some deletion := CoreTriggerProgram.Replacement.preparation state statement then
        prepareTriggerStatement fuel active state [] deletion
      let programs := (CoreTriggerProgram.programs state statement).filter fun program =>
        !active.any (fun name => name.toLower == program.definition.name.toLower)
      unless programs.isEmpty do
        let some target := CoreViewSQL.target? statement | throw "trigger program has no target"
        let table ← CoreTriggerProgram.tableFor state target
        CoreTriggerProgram.preparePrograms
          (fun name => prepareTriggerStatement fuel (name :: active)) executeTriggerRead state table statement programs

/-- Immediate NO ACTION constraints share the complete outer statement's
boundary. Collect actual affected relationships from prepared reachable body
statements; retain the ordinary FK compiler and its missing-parent diagnostics. -/
def triggerForeignEdges : Nat → List String → Core.State → Statement → Except String (List CoreForeignKey.Edge)
  | 0, _, _, _ => .error "too many levels of trigger recursion"
  | fuel + 1, active, state, statement => do
      let mut edges ← CoreForeignKey.edges state statement
      if let some deletion := CoreTriggerProgram.Replacement.preparation state statement then
        edges := edges ++ (← triggerForeignEdges fuel active state deletion)
      let programs := (CoreTriggerProgram.programs state statement).filter fun program =>
        !active.any (fun name => name.toLower == program.definition.name.toLower)
      for program in programs do
        for action in program.definition.body do
          edges := edges ++ (← triggerForeignEdges fuel (program.definition.name :: active) state action)
      return edges

/-- Flatten source syntax through the existing metadata compiler. Only real
original source tables can enter the register producer; private materialized
sources keep the original statement and its own execution plan. -/
def registerInputStatement (state : Core.State) (statement : Statement) : Except String Statement := do
  let .insertSelect target columns query action outputs := statement | return statement
  let [source] := query.sources.toList | return statement
  let some sql := source.subquerySql | return statement
  unless (CoreNames.table? state.database target).isSome && source.columnAliases.isEmpty do return statement
  let parsed ← CoreTokenGrammar.parseCertified sql
  let [.select inner] := parsed.statements.toList | return statement
  let [input] := inner.sources.toList | return statement
  unless input.subquerySql.isNone && input.functionArgs.isNone && input.schema.isNone &&
      input.joinOn.isNone && inner.valueRows.isNone && inner.compounds.isEmpty &&
      inner.groupBy.isEmpty && inner.having.isNone && inner.orderBy.isEmpty &&
      !inner.distinct && inner.limit.isNone && inner.offset == 0 && !CoreWindow.has inner &&
      !CoreScalarQuery.has inner.compoundHeight inner &&
      !inner.columns.any (fun column => CoreAggregate.containsAggregate column.expr) do return statement
  let some table := CoreNames.table? state.database input.name | return statement
  let context : CoreExpr.Context := { schema := table.schema, sourceName := input.alias.getD input.name }
  let expanded ← CoreOrder.expandResults context inner.columns.toList
  let prepared := { inner with columns := expanded.toArray }
  let flattened ← CoreJsonTable.inlineProjection state query prepared source inner
  let candidate := Statement.insertSelect target columns flattened action outputs
  return if CoreTriggerProgram.RegisterInput.eligible state candidate then candidate else statement

def executeStatementFuel : Nat → List String → Bool → CoreTriggerProgram.ScopedEffectExecutor
  | 0, _, _, _, _, _, _ => throw "too many levels of trigger recursion"
  | fuel + 1, active, deferredForeign, parents, state, sql, source => do
      let state := CoreViewSQL.prepareCatalog state
      CoreTriggerProgram.Execution.remember state
      CoreViewSQL.guard state sql
      let requiredForeign ← if state.foreignKeys && CoreConnectionSQL.isDML sql then do
          let relationships ← CoreForeignKey.edges state sql
          pure (!relationships.isEmpty)
        else pure false
      let programs := (CoreTriggerProgram.programs state sql).filter fun program =>
        state.recursiveTriggers || !active.any (fun name => name.toLower == program.definition.name.toLower)
      let scopedInsert := !parents.isEmpty && (match sql with | .insert .. | .insertSelect .. => true | _ => false)
      let requiredReplacement := (CoreTriggerProgram.Replacement.preparation state sql).isSome
      let requiredOutput := !(CoreTriggerProgram.returning sql).isEmpty
      let requiredPartial := CorePartialSQL.affected state sql
      let requiredInput := CoreTriggerProgram.requiresInputEffects sql
      if programs.isEmpty && !requiredForeign && !scopedInsert && !requiredReplacement && !requiredOutput then
        if let some rows := CoreTriggerProgram.ValuesInput.rows? state sql then
          prepareTriggerStatement 1000 active state parents sql
          let prepared ← CoreTriggerProgram.ValuesInput.prepare executeTriggerRead state sql rows
          CoreTriggerProgram.Execution.start
          return ← CoreTriggerProgram.ValuesInput.execute executeTriggerPointWithRegisters
            (fun name => executeStatementFuel fuel (name :: active) true)
            (executeStatementFuel fuel active true) executeTriggerRead state prepared source
      let registerSql ← if programs.isEmpty && !requiredForeign && !scopedInsert && !requiredReplacement && !requiredOutput then
          registerInputStatement state sql
        else pure sql
      if programs.isEmpty && !requiredForeign && !scopedInsert && !requiredReplacement && !requiredOutput &&
          CoreTriggerProgram.RegisterInput.eligible state registerSql then
        prepareTriggerStatement 1000 active state parents sql
        let prepared ← CoreTriggerProgram.RegisterInput.prepare state registerSql
        CoreTriggerProgram.Execution.start
        return ← CoreTriggerProgram.RegisterInput.execute executeTriggerPointWithRegisters
          (fun name => executeStatementFuel fuel (name :: active) true)
          (executeStatementFuel fuel active true) executeTriggerRead state prepared source
      if programs.isEmpty && !requiredForeign && !scopedInsert && !requiredReplacement && !requiredOutput && !requiredInput && !requiredPartial then
        if let .upsert base .. := sql then
          unless (CoreTriggerProgram.programs state base).isEmpty do
            throw "unsupported triggered UPSERT"
        if CoreConnectionSQL.isDML sql then
          let some target := CoreViewSQL.target? sql | throw "DML has no target"
          unless (CoreNames.table? state.database target).isSome do throw s!"no such table: {target}"
          CoreTriggerProgram.prepareBody executeStatementUntriggered executeTriggerRead state parents sql
          CoreTriggerProgram.Execution.start
        let result ← executeStatementUntriggeredWithForeign deferredForeign state sql source
        CoreTriggerProgram.Execution.remember result.1
        return result
      let some target := CoreViewSQL.target? sql | throw "triggered statement has no target"
      let some table := CoreNames.table? state.database target | throw s!"no such table: {target}"
      prepareTriggerStatement 1000 active state parents sql
      if state.foreignKeys && !deferredForeign then discard <| triggerForeignEdges 1000 active state sql
      let input := if state.foreignKeys && !deferredForeign then { state with foreignWrites := [], foreignCounter := 0 } else state
      CoreTriggerProgram.Execution.start
      let (next,results) ← CoreTriggerProgram.executeRows executeTriggerPointWithRegisters
        (fun name => executeStatementFuel fuel (name :: active) true)
        (executeStatementFuel fuel active true) executeTriggerRead input table sql source programs parents
      if state.foreignKeys && !deferredForeign then
        CoreTriggerProgram.Execution.remember { next with totalChanges := next.totalChanges - (results.map (·.changes)).sum }
        CoreTriggerProgram.ForeignCounter.require next.foreignCounter
      let next := if state.foreignKeys && !deferredForeign then { next with foreignWrites := state.foreignWrites, foreignCounter := state.foreignCounter } else next
      CoreTriggerProgram.Execution.remember next
      return (next,results)

/-- Keep connection effects on a failed statement while restoring its logical
ABORT data. Failure-closing callers can use the existing Except adapter. -/
def executeStatementEffects (state : Core.State) (sql : Statement) (source : String) :
    CoreTriggerProgram.ExecutionOutcome :=
  match (executeStatementFuel 4096 [] false [] state sql source).run { state } with
  | .ok (next,results) _ => .success next results
  | .error message context => .failure (CoreTriggerProgram.Execution.abort state context) message

def executeStatement (state : Core.State) (sql : Statement) (source : String) :
    Except String (Core.State × List Core.Result) :=
  (executeStatementEffects state sql source).toExcept

end SQLeanite.CoreDerivedSQL
