import SQLeanite.CoreSQL.ObserveSingleSelect
import SQLeanite.CorePartialIndex

namespace SQLeanite.CoreViewSQL

abbrev Objects := CoreCatalogData.Objects
abbrev Identity := CoreCatalogData.Identity

def find? (state : Core.State) (name : String) : Option CoreCatalogData.View :=
  state.catalog.current.views.find? (fun source => source.definition.name.toLower == name.toLower)

def objectNames (state : Core.State) : List (String × String) :=
  state.database.tables.flatMap (fun table =>
    ("table",table.schema.name) :: table.indexes.map (fun index => ("index",index.name))) ++
  state.catalog.current.views.map (fun source => ("view",source.definition.name)) ++
  state.catalog.current.triggers.map (fun source => ("trigger",source.definition.name)) ++
  state.catalog.current.filteredIndexes.map (fun source => ("index",source.definition.name)) ++
  (state.catalog.current.identities.filter (fun identity =>
    !["table","index","view","trigger"].contains identity.kind)).map (fun identity => (identity.kind,identity.name))

def prepareCatalog (state : Core.State) : Core.State :=
  if state.catalog.loaded then state else
    let identities := (objectNames state).zipIdx.map fun ((kind,name),position) =>
      ({ kind, name, rowid := position + 1 } : Identity)
    let current := { state.catalog.current with identities }
    { state with catalog := { current, durable := current, loaded := true } }

def text? : Core.Value → Option String
  | .text text => String.fromUTF8? (ByteArray.mk text.bytes.toArray)
  | _ => none

def integer? : Core.Value → Option Int
  | .integer value => some value.value
  | _ => none

/-- Load the same physical sqlite_schema rows used by schema queries. View
sources are certified independently and must describe the actual root-zero
catalog object. Unknown object kinds remain visible and block unsupported writes. -/
def load (state : Core.State) (schemaVersion : Nat) (records : List Core.Row) (textEncoding : Nat := 1) : Except String Core.State := do
  let mut identities := []
  let mut views := []
  let mut triggers := []
  let mut filteredIndexes : List CoreCatalogData.FilteredIndex := []
  for row in records do
    let some kind := row.values[0]?.bind text? | throw "invalid schema object type"
    let some name := row.values[1]?.bind text? | throw "invalid schema object name"
    unless row.rowid.value > 0 do throw "unsupported nonpositive schema rowid"
    identities := identities ++ [{ kind, name, rowid := row.rowid.value.toNat }]
    if kind == "view" then
      let some owner := row.values[2]?.bind text? | throw "invalid view owner"
      let some root := row.values[3]?.bind integer? | throw "invalid view root"
      let some text := row.values[4]?.bind text? | throw "invalid view source"
      let source ← CoreCatalogData.view text
      unless owner == name && root == 0 && source.definition.name == name do
        throw "view declaration does not match its catalog identity"
      views := views ++ [source]
    if kind == "index" then
      if let some text := row.values[4]?.bind text? then
        if (CoreCatalogData.parseFilteredIndex text).isSome && !state.database.tables.any
            (fun table => (CoreNames.index? table name).isSome) then
          let some owner := row.values[2]?.bind text? | throw "invalid partial index owner"
          let some root := row.values[3]?.bind integer? | throw "invalid partial index root"
          let source ← CoreCatalogData.filteredIndexAtOwner text owner
          unless root > 0 && source.definition.name == name &&
              !filteredIndexes.any (fun index => index.definition.name.toLower == name.toLower) do
            throw "partial index declaration does not match its catalog identity"
          discard <| CorePartialIndex.prepare state.database source
          filteredIndexes := filteredIndexes ++ [source]
    if kind == "trigger" then
      let some owner := row.values[2]?.bind text? | throw "invalid trigger owner"
      let some root := row.values[3]?.bind integer? | throw "invalid trigger root"
      let some text := row.values[4]?.bind text? | throw "invalid trigger source"
      let source ← CoreCatalogData.triggerAtOwner text owner
      unless root == 0 && source.definition.name == name && source.owner == owner do
        throw "trigger declaration does not match its catalog identity"
      triggers := triggers ++ [source]
  let current : Objects := { views, triggers, filteredIndexes, identities, schemaVersion, textEncoding := if textEncoding == 0 then 1 else textEncoding }
  return { state with
    catalog := { current, durable := current, loaded := true }
    schemaHash := some (SQLite.SchemaHash.build ((identities.filter fun identity =>
      ["table","view"].contains identity.kind).map (·.name))) }

def sourceName? (source : TableRef) : Option String :=
  match source.schema with
  | none => some source.name
  | some schema => if schema.toLower == "main" then
      some (String.ofList (source.name.toList.drop (schema.length + 1))) else none

def uses : Nat → Core.State → Select → Bool
  | 0, _, _ => false
  | fuel + 1, state, query =>
      query.sources.any (fun source => (sourceName? source).any (fun name => (find? state name).isSome)) ||
      query.compounds.any (fun (_,arm) => uses fuel state arm)

def schemaNoop (state : Core.State) : Statement → Bool
  | .createTrigger name _ _ _ _ _ guard _ _ _ => guard &&
      state.catalog.current.triggers.any (fun trigger => trigger.definition.name.toLower == name.toLower)
  | .dropTrigger name guard => guard &&
      !state.catalog.current.triggers.any (fun trigger => trigger.definition.name.toLower == name.toLower)
  | .createView name _ _ guard _ _ => guard &&
      ((find? state name).isSome || (CoreNames.table? state.database name).isSome)
  | .dropView name guard => guard && (find? state name).isNone && (CoreNames.table? state.database name).isNone
  | .createTable name _ _ guard | .createStrictTable name _ _ guard | .createTableAs name _ guard =>
      guard && (find? state name).isSome
  | _ => false

def target? : Statement → Option String
  | .insert name .. | .insertSelect name .. | .update name .. | .delete name .. => some name
  | .upsert base .. => target? base
  | _ => none

def guard (state : Core.State) (statement : Statement) : Except String Unit := do
  if let some target := target? statement then
    if let some source := find? state target then
      throw s!"cannot modify {source.definition.name} because it is a view"
  match statement with
  | .dropTable name _ =>
      if let some source := find? state name then
        throw s!"use DROP VIEW to delete view {source.definition.name}"
  | .createIndex name table _ _ _ _ =>
      if (find? state name).isSome then throw s!"there is already a table named {name}"
      if (find? state table).isSome then throw "views may not be indexed"
  | .createTable name _ _ ifNotExists | .createStrictTable name _ _ ifNotExists | .createTableAs name _ ifNotExists =>
      if !ifNotExists && (find? state name).isSome then throw s!"view {name} already exists"
  | _ => pure ()

def executeDDL (state : Core.State) (statement : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  match statement with
  | .createView name _ _ ifNotExists temporary original =>
      if temporary then throw "unsupported temporary view"
      if name.toLower.startsWith "sqlite_" then throw s!"object name reserved for internal use: {name}"
      if (CoreNames.table? state.database name).isSome then
        if ifNotExists then return (state,[{}]) else throw s!"table {name} already exists"
      if (find? state name).isSome then
        if ifNotExists then return (state,[{}]) else throw s!"view {name} already exists"
      if CoreSQL.indexNameExists state name then throw s!"there is already an index named {name}"
      let text := if original.isEmpty then source else original
      let some text := CoreCatalogData.normalizeView text | throw "invalid view source normalization"
      let compiled ← CoreCatalogData.view text
      unless compiled.definition.name == name do throw "view source target mismatch"
      let current := { state.catalog.current with views := state.catalog.current.views ++ [compiled] }
      return ({ state with catalog := { state.catalog with current } },[{}])
  | .dropView name ifExists =>
      match find? state name with
      | none =>
          if (CoreNames.table? state.database name).isSome then throw s!"use DROP TABLE to delete table {name}"
          if ifExists then return (state,[{}]) else throw s!"no such view: {name}"
      | some found =>
          let current := {
            state.catalog.current with
            views := state.catalog.current.views.filter (fun candidate => candidate.definition.name != found.definition.name) }
          return ({ state with catalog := { state.catalog with current } },[{}])
  | _ => throw "not a view DDL statement"

def schemaContents (state : Core.State) :=
  (state.database.tables.map (fun table => (table.schema,table.indexes,table.catalogSQL)),
    (state.catalog.current.views.map (·.text), state.catalog.current.triggers.map (fun trigger => (trigger.text,trigger.owner)),
      state.catalog.current.filteredIndexes.map (fun index => (index.text,index.owner))))

def renamedIdentity (statement : Statement) (identity : Identity) : Identity :=
  match statement with
  | .alterRenameTable oldName newName =>
      if identity.kind == "table" && identity.name.toLower == oldName.toLower then { identity with name := newName }
      else
        let oldAutoPrefix := "sqlite_autoindex_" ++ oldName ++ "_"
        if identity.kind == "index" && identity.name.toLower.startsWith oldAutoPrefix.toLower then
          { identity with name := "sqlite_autoindex_" ++ newName ++ "_" ++ String.ofList (identity.name.toList.drop oldAutoPrefix.length) }
        else identity
  | _ => identity

/-- Schema identity allocation and object snapshots follow successful SQL
transitions. Renaming preserves a catalog rowid; creation uses the current
maximum, including holes and preceding drops. -/
def transitionCatalog (before next : Core.State) (statement : Statement) : CoreCatalogData.State := Id.run do
  let names := objectNames next
  let mut identities := (before.catalog.current.identities.map (renamedIdentity statement)).filter fun identity =>
    names.any (fun (kind,name) => kind == identity.kind && name.toLower == identity.name.toLower)
  for (kind,name) in names do
    unless identities.any (fun identity => kind == identity.kind && name.toLower == identity.name.toLower) do
      let rowid := identities.foldl (fun largest identity => max largest identity.rowid) 0 + 1
      identities := identities ++ [{ kind := kind, name := name, rowid := rowid }]
  let changed := schemaContents before != schemaContents next
  let current := {
    next.catalog.current with
    identities
    schemaVersion := before.catalog.current.schemaVersion + if changed then 1 else 0 }
  let mut catalog := { before.catalog with current }
  match statement with
  | .begin => catalog := { catalog with transactionSnapshot := some before.catalog.current }
  | .savepoint name =>
      catalog := { catalog with
        transactionSnapshot := if before.transactionSnapshot.isNone then some before.catalog.current else catalog.transactionSnapshot
        savepoints := (name,before.catalog.current) :: catalog.savepoints }
  | .rollback =>
      catalog := {
        catalog with
        current := catalog.transactionSnapshot.getD catalog.current
        transactionSnapshot := none
        savepoints := [] }
  | .rollbackTo name =>
      let marks := catalog.savepoints.dropWhile (fun mark => mark.1.toLower != name.toLower)
      if let some (_,snapshot) := marks.head? then catalog := { catalog with current := snapshot, savepoints := marks }
  | .release name =>
      let marks := catalog.savepoints.dropWhile (fun mark => mark.1.toLower != name.toLower)
      catalog := {
        catalog with
        savepoints := marks.drop 1
        transactionSnapshot := if next.transactionSnapshot.isNone then none else catalog.transactionSnapshot }
  | .commit => catalog := { catalog with transactionSnapshot := none, savepoints := [] }
  | _ => pure ()
  return catalog

def transition (before next : Core.State) (statement : Statement) : Core.State :=
  { next with catalog := transitionCatalog before next statement }

/-- The logical table list follows the catalog's physical rowid order. This
keeps the existing order-sensitive Core serialization relation while preserving
every table object, row tree and checked source. -/
def orderedTables (state : Core.State) : List Core.Table :=
  let rank := fun table : Core.Table =>
    ((state.catalog.current.identities.find? (fun identity =>
      identity.kind == "table" && identity.name.toLower == table.schema.name.toLower)).map (·.rowid)).getD 0
  state.database.tables.mergeSort (fun left right => rank left ≤ rank right)

def orderDatabase (state : Core.State) : Except String Core.State := do
  let database ← Core.Database.rebuild (orderedTables state)
  return { state with database }

/-- Catalog ordering only permutes complete existing Core table objects. -/
theorem orderDatabase_tables_perm (state next : Core.State)
    (success : orderDatabase state = .ok next) : next.database.tables.Perm state.database.tables := by
  unfold orderDatabase at success
  cases rebuilt : Core.Database.rebuild (orderedTables state) with
  | error message => simp [rebuilt, bind, Except.bind] at success
  | ok database =>
      simp [rebuilt, bind, Except.bind, pure, Except.pure] at success
      cases success
      rw [Core.Database.rebuild_tables rebuilt]
      exact List.mergeSort_perm _ _

theorem transition_database (before next : Core.State) (statement : Statement) :
    (transition before next statement).database = next.database := by
  rfl

end SQLeanite.CoreViewSQL
