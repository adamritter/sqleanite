import SQLeanite.CoreSchemaSQL
import SQLeanite.CoreAutoIndexSpec

/-! Actual primary-key and record-column layout derived from a retained
WITHOUT ROWID declaration. No table executor or planner is imported. -/
namespace SQLeanite.CoreWithoutRowidData

structure Layout where
  name : String
  columns : Array ColumnDef
  keys : List CoreAutoIndexSpec.Key
  primaryPositions : List Nat
  storagePositions : List Nat

def layout (sql : String) : Option Layout := do
  let parsed ← CoreSchemaSQL.statements sql
  let [.createWithoutRowidTable name columns constraints _ _] := parsed.toList | none
  let specification ← (CoreAutoIndexSpec.collectWithoutRowid name columns constraints).find? (·.primary)
  let primaryPositions ← specification.keys.mapM (fun key =>
    columns.toList.findIdx? (fun column => column.name.toLower == key.column.toLower))
  let storagePositions := primaryPositions ++ (List.range columns.size).filter (fun position => !primaryPositions.contains position)
  return { name, columns, keys := specification.keys, primaryPositions, storagePositions }

def logicalValues (schema : Core.Schema) (layout : Layout) (physical : List Core.Value) :
    Option (List Core.Value) := do
  unless physical.length == layout.storagePositions.length && schema.catalogColumns.length == layout.columns.size do none
  let logical ← (List.range layout.columns.size).mapM (fun position => do
    let physicalPosition ← layout.storagePositions.findIdx? (· == position)
    let column ← schema.catalogColumns[position]?
    return SQLite.PhysicalAffinity.read column.affinity (← physical[physicalPosition]?))
  for (position,value) in layout.storagePositions.zip physical do
    let column ← schema.catalogColumns[position]?
    unless logical[position]? == some (SQLite.PhysicalAffinity.read column.affinity value) do none
  return logical

def physicalValues (layout : Layout) (logical : List Core.Value) : Option (List Core.Value) :=
  layout.storagePositions.mapM (fun position => logical[position]?)

def keyValues (layout : Layout) (logical : List Core.Value) : Option (List Core.Value) :=
  layout.primaryPositions.mapM (fun position => logical[position]?)

end SQLeanite.CoreWithoutRowidData
