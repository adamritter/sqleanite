import SQLeanite.CorePartialIndex
import SQLeanite.CoreViewSQL
import SQLeanite.SQLite.IndexCatalog

namespace SQLeanite.CorePartialSQL

def find? (state : Core.State) (name : String) : Option CoreCatalogData.FilteredIndex :=
  state.catalog.current.filteredIndexes.find? (fun index => index.definition.name.toLower == name.toLower)

def target? (statement : Statement) : Option String :=
  match statement with
  | .insert name .. | .insertSelect name .. | .update name .. | .delete name .. => some name
  | .upsert base .. => target? base
  | _ => none

def affected (state : Core.State) (statement : Statement) : Bool :=
  (target? statement).any fun name => state.catalog.current.filteredIndexes.any
    (fun index => index.owner.toLower == (CoreSQL.resolveTableName state name).toLower)

def action (statement : Statement) : ConflictAction := match statement with
  | .insert _ _ _ action _ | .insertSelect _ _ _ action _ | .update _ _ _ _ action _ => action
  | _ => .default

def replacementNeeded (state : Core.State) (statement : Statement) : Bool :=
  action statement == .replace && (target? statement).any fun name =>
    state.catalog.current.filteredIndexes.any (fun index =>
      index.owner.toLower == (CoreSQL.resolveTableName state name).toLower && index.definition.unique)

def guard (state : Core.State) (statement : Statement) : Except String Unit := do
  let uniqueTarget := (target? statement).any fun name => state.catalog.current.filteredIndexes.any
    (fun index => index.owner.toLower == (CoreSQL.resolveTableName state name).toLower && index.definition.unique)
  if uniqueTarget then
    let action := match statement with
      | .insert _ _ _ action _ | .insertSelect _ _ _ action _ | .update _ _ _ _ action _ => action
      | _ => ConflictAction.default
    unless action == .default || action == .abort || action == .ignore || action == .replace do throw "unsupported partial-index conflict policy"
    if action == .replace && state.recursiveTriggers then
      if let some name := target? statement then
        if state.catalog.current.triggers.any (fun trigger =>
            trigger.owner.toLower == (CoreSQL.resolveTableName state name).toLower &&
              (match trigger.definition.event with | .delete => true | _ => false)) then
          throw "unsupported partial-index REPLACE with DELETE programs"
    if let some name := target? statement then
      if let some table := CoreNames.table? state.database name then
        unless CoreDefaultConflict.primaryPolicy table.schema == .abort do
          throw "unsupported partial index with declared primary conflict policy"
  match statement with
  | .alterRenameTable name _ | .alterRenameColumn name _ _ | .alterDropColumn name _ | .alterAddColumn name _ =>
      if state.catalog.current.filteredIndexes.any (fun index => index.owner.toLower == name.toLower) then
        throw "unsupported ALTER TABLE with partial indexes"
  | .upsert .. => if affected state statement then throw "unsupported UPSERT with partial indexes"
  | _ => pure ()

def execute? (state : Core.State) (statement : Statement) (text : String) :
    Except String (Option (Core.State × List Core.Result)) := do
  match statement with
  | .createIndex name target expressions unique predicate ifNotExists =>
      let some table := CoreNames.table? state.database target | throw s!"no such table: {target}"
      let inherited ← match expressions.toList with
        | [key] => match CoreCatalogData.indexColumnName? key with
          | some name => CoreIndexPrepare.columnCollation table name
          | none => pure "binary"
        | _ => pure "binary"
      unless CoreCatalogData.auxiliaryIndex expressions predicate || inherited.toLower != "binary" do return none
      unless ← CoreIndexPrepare.prepareCreateIndex state name ifNotExists table.schema.name do
        return some (state,[{}])
      let some text := SQLite.IndexCatalog.normalize text | throw "cannot retain partial index source"
      let source ← CoreCatalogData.filteredIndexAtOwner text table.schema.name
      let parsed ← CoreTokenGrammar.parseCertified text
      CoreTokenGrammar.check parsed.tokens #[.createIndex name target expressions unique predicate false]
      let compiled ← CorePartialIndex.prepare state.database source
      discard <| CorePartialIndex.sortedRows compiled
      let current := { state.catalog.current with
        filteredIndexes := state.catalog.current.filteredIndexes ++ [source] }
      return some ({ state with catalog := { state.catalog with current } },[{}])
  | .dropIndex name _ =>
      let some _ := find? state name | return none
      let current := { state.catalog.current with
        filteredIndexes := state.catalog.current.filteredIndexes.filter (fun index => index.definition.name.toLower != name.toLower) }
      return some ({ state with catalog := { state.catalog with current } },[{}])
  | _ => return none

def removeDroppedOwners (state : Core.State) (statement : Statement) : Core.State :=
  match statement with
  | .dropTable name _ =>
      let remaining := state.catalog.current.filteredIndexes.filter (fun index => index.owner.toLower != name.toLower)
      let current := { state.catalog.current with filteredIndexes := remaining }
      { state with catalog := { state.catalog with current } }
  | _ => state

/-- Pure accepted candidate checking precedes actual publication. Ordinary
constraint/IGNORE preparation remains authoritative; only real accepted NEW
registers evaluate the retained partial predicates. -/
def preparePoint (base : Core.State → Statement → String → Except String (Core.State × List Core.Result))
    (capture : Statement → Except String Statement) (state : Core.State) (table : Core.Table)
    (statement : Statement) : Except String (Core.State × Bool) := do
  unless affected state statement do return (state,true)
  if let .delete .. := statement then return (state,true)
  let (accepted,results) ← base state (← capture statement) ""
  if (results.map (·.changes)).sum == 0 then return (state,true)
  let [image] := results.flatMap (·.rows) | throw "partial index lost its accepted candidate"
  let values := image.take table.schema.columns.length
  for source in state.catalog.current.filteredIndexes do
    unless source.owner.toLower == table.schema.name.toLower do continue
    if source.definition.unique && action statement != .replace then
      let compiled ← CorePartialIndex.prepare accepted.database source
      let ordered ← CorePartialIndex.orderedRows compiled
      if !CoreIndexExpression.adjacentUnique compiled.index compiled.collation ordered then
        if action statement == .ignore then
          let next ← if table.schema.autoIncrement then do
              let some keyValue := values[table.schema.primaryKey]? | throw "ignored partial candidate lost its rowid"
              let .integer key := (keyValue : Core.Value) | throw "ignored partial candidate rowid is not an integer"
              let counter ← CoreAutoIncrement.beginContext state table.schema.name
              CoreAutoIncrement.finish state (CoreAutoIncrement.advance counter key)
            else pure state
          return (next,false)
        discard <| CorePartialIndex.sortedRows compiled
    else
      let compiled ← CorePartialIndex.prepare state.database source
      if ← CoreIndexExpression.acceptsPredicate compiled.context values compiled.predicate then
        discard <| CorePartialIndex.keyValue compiled values
  return (state,true)

def replacementVictims (state : Core.State) (statement : Statement) (values : List Core.Value)
    (old : Option Core.Integer) : Except String (List Core.Row) := do
  unless replacementNeeded state statement do return []
  let some name := target? statement | return []
  let mut victims : List Core.Row := []
  for source in state.catalog.current.filteredIndexes.reverse do
    unless source.owner.toLower == (CoreSQL.resolveTableName state name).toLower && source.definition.unique do continue
    let compiled ← CorePartialIndex.prepare state.database source
    unless ← CoreIndexExpression.acceptsPredicate compiled.context values compiled.predicate do continue
    let candidate ← Core.Row.create compiled.table.schema values
    let candidateKey ← CorePartialIndex.keyValue compiled candidate.values
    for row in ← CorePartialIndex.rows compiled do
      if old.any (· == row.rowid) || row.rowid == candidate.rowid || victims.any (fun previous => previous.rowid == row.rowid) then continue
      let oldKey ← CorePartialIndex.keyValue compiled row.values
      if CoreIndexExpression.uniqueConflict compiled.collation candidateKey oldKey then victims := victims ++ [row]
  return victims

abbrev pragmaRows := CoreSchemaPragma.rowsWithState

def pragma (state : Core.State) (name : String) (argument : Option Expr) (schema : Option String) :
    Except String (Core.State × List Core.Result) := do
  if schema.any (fun name => !["main","temp"].contains name.toLower) then
    throw s!"unknown database {schema.getD ""}"
  let rows ← if schema.any (fun name => name.toLower == "temp") then pure [] else match argument with
    | none => pure []
    | some argument => do
        let some target := CoreSchemaPragma.argumentName argument | throw "unsupported PRAGMA argument"
        pragmaRows state name target
  let rows ← rows.mapM (List.mapM SQLSurface.value)
  return (state,[{ rows }])

end SQLeanite.CorePartialSQL
