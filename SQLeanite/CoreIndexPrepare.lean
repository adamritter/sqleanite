import SQLeanite.CoreEngine.ChooseExtremeEqLeftOrRight
import SQLeanite.CoreNames

/-! Index catalog admission shared by SQL execution and physical decoding. -/
namespace SQLeanite.CoreIndexPrepare

/-- CREATE INDEX cannot name an implicit rowid alias. A real column with
that spelling is still permitted. -/
def indexColumn (schema : Core.Schema) (name : String) : Except String Nat :=
  match schema.catalogColumns.findIdx? (fun column => String.toLower column.name == String.toLower name) with
  | some index => .ok index
  | none => .error s!"no such column: {name}"

def indexNameExists (state : Core.State) (name : String) : Bool :=
  (state.database.tables.any fun table => table.indexes.any fun index => String.toLower index.name == String.toLower name) ||
    state.catalog.current.filteredIndexes.any (fun index => index.definition.name.toLower == name.toLower)

/-- The target table must already have been resolved before checking the
index name. Existing indexes skip expression binding under IF NOT EXISTS. -/
def prepareCreateIndex (state : Core.State) (name : String) (ifNotExists : Bool)
    (table : String := "") : Except String Bool := do
  if (String.toLower table).startsWith "sqlite_" then throw s!"table {table} may not be indexed"
  if (String.toLower name).startsWith "sqlite_" then throw s!"object name reserved for internal use: {name}"
  if (CoreNames.table? state.database name).isSome then
    throw s!"there is already a table named {name}"
  if indexNameExists state name then
    if ifNotExists then return false else throw s!"index already exists: {name}"
  return true

end SQLeanite.CoreIndexPrepare
