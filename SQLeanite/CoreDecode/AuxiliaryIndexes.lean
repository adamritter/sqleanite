import SQLeanite.CorePartialIndex
import SQLeanite.CoreDecode.IndexRecords

/-! Independently compare every physical key component and actual rowid to
source-program results. Collation never hides differing stored key bytes. -/
namespace SQLeanite.CoreDecode

def filteredIndexMetadata (database : Core.Database) (entry : CatalogEntry) :
    Option CorePartialIndex.Prepared := do
  unless entry.kind == "index" && entry.rootPage > 0 do none
  let sql ← entry.sql
  let compiled ← (CoreCatalogData.filteredIndexAtOwner sql entry.table).toOption
  unless compiled.definition.name.toLower == entry.name.toLower do none
  let available ← (CoreIndexPrepare.prepareCreateIndex { database } entry.name false entry.table).toOption
  unless available do none
  let prepared ← (CorePartialIndex.prepare database compiled).toOption
  unless CorePartialIndex.required prepared do none
  return prepared

def keyValuesMatch (table : Core.Table) :
    List CorePartialIndex.Key → List Core.Value → List Core.Value → Bool
  | [], [], [] => true
  | key :: keys, actual :: physical, wanted :: expected =>
      let same := match key.column with
        | none => PhysicalQuery.compareValue actual wanted == .eq
        | some position => match table.schema.columns[position]? with
          | none => false
          | some column => SQLite.PhysicalAffinity.read column.affinity actual == wanted
      same && keyValuesMatch table keys physical expected
  | _, _, _ => false

def checkedFilteredIndex (prepared : CorePartialIndex.Prepared) (physical : List CoreIndexKey.Entry) : Bool :=
  match CorePartialIndex.sortedKeys prepared with
  | .error _ => false
  | .ok expected => physical.length == expected.length &&
      (physical.zip expected).all (fun (actual,wanted) =>
        actual.rowid == wanted.rowid && keyValuesMatch prepared.table prepared.keys actual.values wanted.values)

end SQLeanite.CoreDecode
