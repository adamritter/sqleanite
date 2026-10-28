import SQLeanite.CoreDecode.IndexRecords
import SQLeanite.CoreWithoutRowidData
import SQLeanite.SQLSurface

/-! A WITHOUT ROWID table stores all visible values in primary-key-first
index records. Its logical ordinal is private and absent from physical bytes. -/
namespace SQLeanite.CoreDecode.WithoutRowid

private def privateInteger (ordinal : Nat) : Option Core.Integer := do
  let value ← (SQLSurface.value (.integer ordinal)).toOption
  let .integer integer := value | none
  return integer

def rows (schema : Core.Schema) (layout : CoreWithoutRowidData.Layout)
    (physical : List (List Core.Value)) : Option (List Core.Row) := do
  physical.zipIdx.mapM (fun (record,position) => do
    let values ← CoreWithoutRowidData.logicalValues schema layout record
    let ordinal ← privateInteger (position+1)
    (Core.Row.create schema (values ++ [.integer ordinal])).toOption)

def ordered (layout : CoreWithoutRowidData.Layout) : List Core.Row → Bool
  | left :: right :: rest =>
      match CoreWithoutRowidData.keyValues layout left.values,
          CoreWithoutRowidData.keyValues layout right.values,
          layout.keys.mapM (fun key => (SQLite.Collation.named? key.collation).map (fun kind => (kind,key.descending))) with
      | some a,some b,some collations =>
          CoreIndexKey.compareDirected collations a b == .lt && ordered layout (right :: rest)
      | _,_,_ => false
  | _ => true

def table (schema : Core.Schema) (sql : String) (physical : List (List Core.Value)) : Option Core.Table := do
  let layout ← CoreWithoutRowidData.layout sql
  let logical ← rows schema layout physical
  unless ordered layout logical do none
  (Core.Table.rebuildFromCatalog schema [] logical sql).toOption

def tableFrom (source : PageSource) (schema : Core.Schema) (sql : String) (root : Nat) : Option Core.Table := do
  table schema sql (← IndexRecords.valuesFrom source (source.pageCount+1) root)

def tableIOFrom (source : IOPageSource) (schema : Core.Schema) (sql : String) (root : Nat) : IO (Option Core.Table) := do
  unless source.textEncoding == 1 do return none
  let some physical ← IndexRecords.valuesIOFrom source (source.pageCount+1) root | return none
  return table schema sql physical

end SQLeanite.CoreDecode.WithoutRowid
