import SQLeanite.CorePartialIndex
import SQLeanite.CoreWithoutRowidData

/-! Private ordinal normalization is performed only at an outer statement
boundary. SQL values and physical records contain the actual declared columns. -/
namespace SQLeanite.CoreWithoutRowidTable

def orderedRows (table : Core.Table) : Except String (List Core.Row) := do
  let some layout := CoreWithoutRowidData.layout table.catalogSQL | throw "missing WITHOUT ROWID layout"
  let collations ← layout.keys.mapM fun key => do
    let some kind := SQLite.Collation.named? key.collation | throw s!"no such collation sequence: {key.collation}"
    pure (kind,key.descending)
  let keyed ← table.rows.mapM fun row => do
    let some keys := CoreWithoutRowidData.keyValues layout row.values | throw "missing primary key values"
    return (row, keys)
  return (keyed.mergeSort (fun a b => CoreIndexKey.compareDirected collations a.2 b.2 != .gt)).map Prod.fst

def physicalRows (table : Core.Table) : Option (List (List Core.Value)) := do
  let layout ← CoreWithoutRowidData.layout table.catalogSQL
  let rows ← (orderedRows table).toOption
  rows.mapM (fun row => CoreWithoutRowidData.physicalValues layout row.values)

/-- Runtime lookup uses the real declared PK after trigger programs. A
private ordinal cannot identify a deleted/reinserted or rekeyed SQL row. -/
def findPrimary (table : Core.Table) (values : List Core.Value) : Except String (Option Core.Row) := do
  let some layout := CoreWithoutRowidData.layout table.catalogSQL | throw "missing primary lookup layout"
  let some wanted := CoreWithoutRowidData.keyValues layout values | throw "missing primary lookup values"
  let collations ← layout.keys.mapM fun key => do
    let some kind := SQLite.Collation.named? key.collation | throw s!"no such collation sequence: {key.collation}"
    pure kind
  for row in table.rows do
    let some actual := CoreWithoutRowidData.keyValues layout row.values | throw "missing stored primary values"
    if CoreIndexKey.compareValues collations actual wanted == .eq then return some row
  return none

def normalizeTable (table : Core.Table) : Except String Core.Table := do
  if !table.withoutRowid then return table
  let ordered ← orderedRows table
  let rows ← ordered.zipIdx.mapM fun (row, position) => do
    let ordinal ← SQLSurface.value (.integer (position+1))
    Core.Row.create table.schema (row.values.set table.schema.primaryKey ordinal)
  Core.Table.rebuildFromCatalog table.schema table.indexes rows table.catalogSQL

def normalize (state : Core.State) : Except String Core.State := do
  if !state.database.tables.any (·.withoutRowid) then return state
  let tables ← state.database.tables.mapM normalizeTable
  let database ← Core.Database.rebuild tables
  return { state with database }

end SQLeanite.CoreWithoutRowidTable
