import SQLeanite.CoreWithoutRowidIndex
import SQLeanite.CoreWithoutRowidData

/-! A full covering secondary record can be scanned without looking up the
primary table. Read materialization retains the same declared values and source;
only its private ordinal describes the actual selected scan order. -/
namespace SQLeanite.CoreWithoutRowidRead

def prepare (state : Core.State) (query : Select) : Except String Core.State := do
  if state.internalReturning || !query.where_.isNone || !query.orderBy.isEmpty ||
      !query.groupBy.isEmpty || !query.having.isNone || !query.compounds.isEmpty || query.distinct then return state
  let [source] := query.sources.toList | return state
  let some table := CoreNames.table? state.database source.name | return state
  if !table.withoutRowid then return state
  let some layout := CoreWithoutRowidData.layout table.catalogSQL | return state
  let mut selected : Option (CorePartialIndex.Prepared × Nat) := none
  for index in state.catalog.current.filteredIndexes.reverse do
    if index.primaryRoot || index.definition.partialIndex || index.owner != table.schema.name then continue
    let compiled ← CorePartialIndex.prepare state.database index
    let fields ← CoreWithoutRowidIndex.keys compiled
    let some positions := fields.mapM (·.column) | continue
    if !table.schema.visibleColumnIndices.all positions.contains || positions.length > layout.storagePositions.length then continue
    if selected.any (fun previous => previous.2 ≤ positions.length) then continue
    selected := some (compiled,positions.length)
  let some (compiled,_) := selected | return state
  let entries ← CoreWithoutRowidIndex.orderedEntries compiled
  let rows ← entries.zipIdx.mapM fun ((row,_),position) => do
    let ordinal ← SQLSurface.value (.integer (position+1))
    Core.Row.create table.schema (row.values.set table.schema.primaryKey ordinal)
  let ordered ← Core.Table.rebuildFromCatalog table.schema table.indexes rows table.catalogSQL
  let database ← state.database.updateTable ordered
  return { state with database }

end SQLeanite.CoreWithoutRowidRead
