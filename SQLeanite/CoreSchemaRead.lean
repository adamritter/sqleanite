import SQLeanite.CoreDecode.ValidateCanonicalIndexGroupsFromEncodeOverflowIndexTableGroups
import SQLeanite.CoreDerivedSQL.Read

/-! sqlite_schema reads use actual catalog B-tree records, including their
rowids and rootpage values. The transient read tables never enter persistent
connection state. Pending schema DDL needs a separate transactional catalog. -/
namespace SQLeanite.CoreSchemaRead

def schema (name : String := "sqlite_schema") : Core.Schema := {
  name
  columns := [{ name := "type", declaredType := "TEXT" },
    { name := "name", declaredType := "TEXT" }, { name := "tbl_name", declaredType := "TEXT" },
    { name := "rootpage", declaredType := "INTEGER" }, { name := "sql", declaredType := "TEXT" },
    Core.hiddenRowidColumn]
  primaryKey := 5
  declaredPrimaryKey := 6 }

def walk (source : CoreDecode.IOPageSource) : Nat → List Nat → List Nat →
    List Core.Row → IO (Option (List Core.Row))
  | _, [], _, rows => pure (some rows.reverse)
  | 0, _ :: _, _, _ => pure none
  | fuel+1, pageNumber :: pending, visited, rows => do
      if pageNumber == 0 || source.pageCount < pageNumber || visited.contains pageNumber then return none
      let some page ← source.readPage pageNumber | return none
      let some decoded := CoreDecode.catalogPage? source.usable.val pageNumber page | return none
      match decoded with
      | .branch children => walk source fuel (children ++ pending) (pageNumber :: visited) rows
      | .leaf cells =>
          let decoded ← cells.mapM (CoreDecode.decodeRowCellIOFrom schema source (source.pageCount + 1))
          let some decoded := decoded.mapM id | return none
          walk source fuel pending (pageNumber :: visited) (decoded.reverse ++ rows)

def rows (source : CoreDecode.IOPageSource) : IO (Option (List Core.Row)) :=
  walk source source.pageCount [1] [] []

/-- Pure counterpart for a checked 4096-byte publication image. Physical
catalog rowids and overflow payloads are decoded before object comparison. -/
def walkFrom (source : CoreDecode.PageSource) : Nat → List Nat → List Nat →
    List Core.Row → Option (List Core.Row)
  | _, [], _, rows => some rows.reverse
  | 0, _ :: _, _, _ => none
  | fuel + 1, pageNumber :: pending, visited, rows => do
      if pageNumber == 0 || source.pageCount < pageNumber || visited.contains pageNumber then none else do
        let page ← source.readPage pageNumber
        let decoded ← CoreDecode.catalogPage? PhysicalCodec.usablePageSize.val pageNumber page
        match decoded with
        | .branch children => walkFrom source fuel (children ++ pending) (pageNumber :: visited) rows
        | .leaf cells =>
            let decoded ← cells.mapM (CoreDecode.decodeRowCellFrom schema source (source.pageCount + 1))
            walkFrom source fuel pending (pageNumber :: visited) (decoded.reverse ++ rows)

def rowsFrom (source : CoreDecode.PageSource) : Option (List Core.Row) :=
  walkFrom source source.pageCount [1] [] []

def catalogName (source : TableRef) : Option String :=
  let name := match source.schema with
    | none => source.name
    | some owner => if owner.toLower == "main" then String.ofList (source.name.toList.drop (owner.length + 1)) else ""
  if ["sqlite_schema", "sqlite_master"].contains name.toLower then some name else none

def normalize : Nat → Select → Select
  | 0, query => query
  | fuel+1, query => { query with
      sources := query.sources.map fun source => match catalogName source with
        | none => source
        | some name => { source with name, schema := none }
      compounds := query.compounds.map fun (op,arm) => (op,normalize fuel arm) }

def uses : Nat → Select → Bool
  | 0, _ => false
  | fuel+1, query => query.sources.any (fun source => (catalogName source).isSome) ||
    query.compounds.any (fun (_,arm) => uses fuel arm)

def sameSchema (left right : Core.Database) : Bool :=
  left.tables.map (fun table => (table.schema,table.indexes,table.catalogSQL)) ==
    right.tables.map (fun table => (table.schema,table.indexes,table.catalogSQL))

/-- Root-zero program objects come from the actual connection catalog.
Retained table/index roots remain the supplied physical records. New or altered
table layouts still need their own transactional page allocation support. -/
def schemaSubset (snapshot current : Core.Database) : Bool :=
  current.tables.all fun table => snapshot.tables.any fun old =>
    old.schema == table.schema && old.catalogSQL == table.catalogSQL && table.indexes.all old.indexes.contains

def currentRecords (state : Core.State) (records : List Core.Row) : Except String (List Core.Row) := do
  if !state.catalog.loaded || !state.catalog.changed then return records
  if state.transactionSnapshot.any (fun snapshot => !schemaSubset snapshot state.database) then
    throw "unsupported sqlite_schema query after pending schema changes"
  let retained := records.filter fun row =>
    let kind := row.values[0]?.bind CoreViewSQL.text?
    let name := row.values[1]?.bind CoreViewSQL.text?
    kind != some "view" && kind != some "trigger" &&
      state.catalog.current.identities.any (fun identity =>
        some identity.kind == kind && some identity.name == name && Int.ofNat identity.rowid == row.rowid.value)
  let programs := state.catalog.current.views.map (fun view => ("view",view.definition.name,view.definition.name,view.text)) ++
    state.catalog.current.triggers.map (fun trigger => ("trigger",trigger.definition.name,trigger.owner,trigger.text))
  let programs ← programs.mapM fun (kind,name,owner,text) => do
    let some identity := state.catalog.current.identities.find? (fun identity => identity.kind == kind && identity.name == name)
      | throw "missing transactional schema object identity"
    let rowid ← SQLSurface.value (.integer identity.rowid)
    let .integer key := rowid | throw "invalid transactional schema rowid"
    let values ← [Value.text kind,.text name,.text owner,.integer 0,.text text].mapM SQLSurface.value
    pure ({ rowid := key, values := values++[rowid] } : Core.Row)
  return (retained++programs).mergeSort (fun left right => left.rowid.value ≤ right.rowid.value)

theorem currentRecords_durable (state : Core.State) (records : List Core.Row)
    (unchanged : state.catalog.changed = false) : currentRecords state records = .ok records := by
  simp [currentRecords,unchanged,pure,Except.pure]

def execute (state : Core.State) (query : Select) (records : List Core.Row) :
    Except String (Core.State × List Core.Result) := do
  let records ← currentRecords state records
  let tables ← ["sqlite_schema", "sqlite_master"].mapM fun name => Core.Table.rebuild (schema name) [] records
  let database ← Core.Database.rebuild (state.database.tables ++ tables)
  let (_, results) ← CoreDerivedSQL.executeStatement { state with database } (.select (normalize query.compoundHeight query)) ""
  return (state, results)

theorem execute_preserves_state (state next : Core.State) (query : Select)
    (records : List Core.Row) (results : List Core.Result)
    (success : execute state query records = .ok (next,results)) : next = state := by
  unfold execute at success
  cases actual : currentRecords state records with
  | error message => simp [actual,bind,Except.bind] at success
  | ok rows =>
    simp only [actual,bind,Except.bind] at success
    split at success <;> try contradiction
    split at success <;> try contradiction
    split at success <;> try contradiction
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
    exact success.1.symm

end SQLeanite.CoreSchemaRead
