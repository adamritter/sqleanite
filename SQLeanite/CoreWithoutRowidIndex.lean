import SQLeanite.CorePartialIndex

/-! WITHOUT ROWID secondary records end in the missing primary-key columns.
A column already present with the same collation is stored only once. -/
namespace SQLeanite.CoreWithoutRowidIndex

def suffix (prepared : CorePartialIndex.Prepared) : Except String (List CorePartialIndex.Key) := do
  let sources ← CorePartialIndex.automaticSources prepared.table
  let some primary := sources.find? (·.primaryRoot) | throw "missing WITHOUT ROWID primary key"
  let database ← Core.Database.rebuild [prepared.table]
  let compiled ← CorePartialIndex.prepare database primary
  return compiled.keys.filter (fun key => !prepared.keys.any (fun other =>
    other.column == key.column && other.collation == key.collation))

def keys (prepared : CorePartialIndex.Prepared) : Except String (List CorePartialIndex.Key) := do
  return prepared.keys ++ (← suffix prepared)

def orderedEntries (prepared : CorePartialIndex.Prepared) : Except String (List (Core.Row × List Core.Value)) := do
  discard <| CorePartialIndex.sortedKeys prepared
  let fields ← keys prepared
  let rows ← CorePartialIndex.rows prepared
  let values ← rows.mapM fun row => do
    let values ← fields.mapM fun field => do
      SQLSurface.value (← CoreIndexExpression.eval prepared.context row.values field.expression)
    return (row,values)
  return values.mergeSort (fun a b => CoreIndexKey.compareDirected (fields.map (fun key => (key.collation,key.descending))) a.2 b.2 != .gt)

def records (prepared : CorePartialIndex.Prepared) : Except String (List (List Core.Value)) := do
  return (← orderedEntries prepared).map Prod.snd

end SQLeanite.CoreWithoutRowidIndex
