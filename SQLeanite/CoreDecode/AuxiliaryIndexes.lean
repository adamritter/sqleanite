import SQLeanite.CorePartialIndex
import SQLeanite.CoreWithoutRowidIndex
import SQLeanite.CoreDecode.IndexRecords

/-! Independently compare every physical key component and actual rowid to
source-program results. Collation never hides differing stored key bytes. -/
namespace SQLeanite.CoreDecode

def filteredIndexMetadata (database : Core.Database) (entry : CatalogEntry) :
    Option CorePartialIndex.Prepared := do
  unless entry.kind == "index" && entry.rootPage > 0 do none
  let some table := CoreNames.table? database entry.table | none
  let compiled ← match entry.sql with
    | none => do
        let sources ← (CorePartialIndex.automaticSources table).toOption
        sources.find? (fun source => source.definition.name.toLower == entry.name.toLower)
    | some sql => (CoreCatalogData.filteredIndexAtOwner sql entry.table).toOption
  unless compiled.definition.name.toLower == entry.name.toLower do none
  if compiled.automaticTable?.isSome then
    unless !(CoreIndexPrepare.indexNameExists { database } entry.name) &&
        (CoreNames.table? database entry.name).isNone do none
  else
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

/-- Every actual record field is checked, including the primary-key locator. -/
def checkedWithoutRowidIndex (prepared : CorePartialIndex.Prepared) (physical : List (List Core.Value)) : Bool :=
  match CoreWithoutRowidIndex.records prepared, CoreWithoutRowidIndex.keys prepared with
  | .ok expected, .ok keys => physical.length == expected.length &&
      (physical.zip expected).all (fun (actual,wanted) => keyValuesMatch prepared.table keys actual wanted)
  | _, _ => false

end SQLeanite.CoreDecode
