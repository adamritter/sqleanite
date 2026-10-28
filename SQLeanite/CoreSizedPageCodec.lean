import SQLeanite.CoreAutomaticIndex
import SQLeanite.CoreCatalogData
import SQLeanite.CoreOverflow.ResolvePlansNextPage

/-! Page-size-preserving bulk encoding. Record encoding and balanced tree
construction are shared with the existing core. Geometry is a parameter of
every materialized page, including overflow pages and sqlite_schema. -/
namespace SQLeanite.CoreSizedPageCodec

open FileFormat RecursivePageBTree

abbrev Page (size : Nat) := Storage.Page size

def page? (size : Nat) (bytes : Array UInt8) : Option (Page size) :=
  if h : bytes.size = size then some ⟨bytes, h⟩ else none

def number (width value : Nat) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat (value / 256 ^ (width - i - 1) % 256)

/-- Pagination depends only on physical cell lengths and retains their order. -/
def pack (size : Nat) (current : List (List UInt8)) (used : Nat) :
    List (List UInt8) → List (List (List UInt8))
  | [] => [current.reverse]
  | cell :: rest =>
      if 8 + 2 * (current.length + 1) + used + cell.length ≤ size then
        pack size (cell :: current) (used + cell.length) rest
      else current.reverse :: pack size [cell] cell.length rest

theorem flatten_pack (size : Nat) (current : List (List UInt8)) (used : Nat) :
    (rest : List (List UInt8)) →
      (pack size current used rest).flatten = current.reverse ++ rest
  | [] => by simp [pack]
  | cell :: rest => by
      unfold pack
      split
      · rw [flatten_pack size (cell :: current) (used + cell.length) rest]
        simp
      · rw [List.flatten_cons, flatten_pack size [cell] cell.length rest]
        simp

def paginate (size : Nat) (cells : List (List UInt8)) := pack size [] 0 cells

theorem flatten_paginate (size : Nat) (cells : List (List UInt8)) :
    (paginate size cells).flatten = cells := by
  simpa [paginate] using flatten_pack size [] 0 cells

def tablePlan? (size : Nat) (cells : List (List UInt8)) : Option Plan :=
  build (paginate size cells)

theorem tablePlan?_contents {size : Nat} {cells : List (List UInt8)} {plan : Plan}
    (built : tablePlan? size cells = some plan) : plan.toCells = cells := by
  exact (build_toCells built).trans (flatten_paginate size cells)

def indexPlan? (size : Nat) (cells : List (List UInt8)) : Option IndexPlan :=
  buildIndex (paginate size cells)

theorem indexPlan?_contents {size : Nat} {cells : List (List UInt8)} {plan : IndexPlan}
    (built : indexPlan? size cells = some plan) : plan.toCells = cells := by
  exact (buildIndex_toCells built).trans (flatten_paginate size cells)

theorem indexPlan?_balanced {size : Nat} {cells : List (List UInt8)} {plan : IndexPlan}
    (built : indexPlan? size cells = some plan) : plan.Balanced :=
  buildIndex_balanced built

/-- Cell pointers are absolute page offsets. Zero is the SQLite encoding of
the empty content boundary at 65536, not a zero-byte page. -/
def btreePage? (size kind : Nat) (cells : List (List UInt8))
    (rightmost : Option Nat := none) (fileHeader : List UInt8 := []) : Option (Page size) := do
  let payload := cells.flatten
  let start := size - payload.length
  let headerSize := if rightmost.isSome then 12 else 8
  if fileHeader.length + headerSize + 2 * cells.length + payload.length > size ||
      cells.length ≥ 65536 || size > 65536 then none
  else do
    let mut cursor := start
    let mut pointers := #[]
    for cell in cells do
      pointers := pointers ++ (number 2 cursor).toArray
      cursor := cursor + cell.length
    let header := [UInt8.ofNat kind, 0, 0] ++ number 2 cells.length ++
      number 2 start ++ [0] ++ (rightmost.map (number 4) |>.getD [])
    let leading := fileHeader.toArray ++ header.toArray ++ pointers
    page? size (leading ++ Array.replicate (start - leading.size) 0 ++ payload.toArray)

def localSize (usable : UsablePageSize) (plan : CoreOverflow.CellPlan) : Nat :=
  match plan.kind with
  | .table => tableLeafLocalPayloadSize usable plan.payload.length
  | .index => indexLocalPayloadSize usable plan.payload.length

theorem local_overflow_reassembles (usable : UsablePageSize) (plan : CoreOverflow.CellPlan) :
    plan.payload.take (localSize usable plan) ++
      plan.payload.drop (localSize usable plan) = plan.payload :=
  List.take_append_drop _ _

def cell? (usable : UsablePageSize) (plan : CoreOverflow.CellPlan) (next : Nat) :
    Option (List UInt8) := do
  let localCount := localSize usable plan
  let tail := plan.payload.drop localCount
  let pointer ← if tail.isEmpty then some [] else
    (boundedU32? next).map encodeU32Bytes
  return plan.cellPrefix ++ plan.payload.take localCount ++ pointer

def overflowPages? (usable : UsablePageSize) (first : Nat) (payload : List UInt8) :
    Option (List (Page usable.val)) := do
  let capacity := usable.val - 4
  let chunks := payload.toArray
  let count := (chunks.size + capacity - 1) / capacity
  (List.range count).mapM fun i => do
    let next ← boundedU32? (if i + 1 < count then first + i + 1 else 0)
    let data := chunks.extract (i * capacity) ((i + 1) * capacity)
    page? usable.val ((encodeU32Bytes next).toArray ++ data ++
      Array.replicate (capacity - data.size) 0)

structure Resolved (size : Nat) where
  cells : List (List UInt8)
  overflow : List (Page size)

def resolve (usable : UsablePageSize) (first : Nat)
    (plans : List CoreOverflow.CellPlan) : Option (Resolved usable.val) := do
  let mut next := first
  let mut cells := []
  let mut pages := []
  for plan in plans do
    let encoded ← cell? usable plan next
    let overflow ← overflowPages? usable next (plan.payload.drop (localSize usable plan))
    cells := encoded :: cells
    pages := overflow.foldl (fun acc page => page :: acc) pages
    next := next + overflow.length
  return ⟨cells.reverse, pages.reverse⟩

def tablePages? (size start : Nat) : Plan → Option (List (Page size))
  | .leaf cells => do return [← btreePage? size 13 cells]
  | .branch2 left right => do
      let leftRoot := start + 1
      let rightRoot := leftRoot + left.pageCount
      let cell ← interiorCell? leftRoot (← separatorKey? left)
      let root ← btreePage? size 5 [cell] (some rightRoot)
      return root :: ((← tablePages? size leftRoot left) ++
        (← tablePages? size rightRoot right))
  | .branch3 left middle right => do
      let leftRoot := start + 1
      let middleRoot := leftRoot + left.pageCount
      let rightRoot := middleRoot + middle.pageCount
      let first ← interiorCell? leftRoot (← separatorKey? left)
      let second ← interiorCell? middleRoot (← separatorKey? middle)
      let root ← btreePage? size 5 [first, second] (some rightRoot)
      return root :: ((← tablePages? size leftRoot left) ++
        (← tablePages? size middleRoot middle) ++ (← tablePages? size rightRoot right))

def indexPages? (size start : Nat) : IndexPlan → Option (List (Page size))
  | .leaf cells => do return [← btreePage? size 10 cells]
  | .branch2 left separator right => do
      let leftRoot ← boundedU32? (start + 1)
      let rightRoot := leftRoot.val + left.pageCount
      let root ← btreePage? size 2 [encodeU32Bytes leftRoot ++ separator] (some rightRoot)
      return root :: ((← indexPages? size leftRoot.val left) ++
        (← indexPages? size rightRoot right))
  | .branch3 left first middle second right => do
      let leftRoot ← boundedU32? (start + 1)
      let middleRoot ← boundedU32? (leftRoot.val + left.pageCount)
      let rightRoot := middleRoot.val + middle.pageCount
      let root ← btreePage? size 2 [encodeU32Bytes leftRoot ++ first,
        encodeU32Bytes middleRoot ++ second] (some rightRoot)
      return root :: ((← indexPages? size leftRoot.val left) ++
        (← indexPages? size middleRoot.val middle) ++ (← indexPages? size rightRoot right))

def encodeTable? (usable : UsablePageSize) (start : Nat)
    (plans : List CoreOverflow.CellPlan) : Option (List (Page usable.val)) := do
  let provisional ← plans.mapM (fun plan => cell? usable plan 1)
  let topology ← tablePlan? usable.val provisional
  let resolved ← resolve usable (start + topology.pageCount) plans
  let finalPlan ← topology.withCells? resolved.cells
  return (← tablePages? usable.val start finalPlan) ++ resolved.overflow

def encodeIndex? (usable : UsablePageSize) (start : Nat)
    (plans : List CoreOverflow.CellPlan) : Option (List (Page usable.val)) := do
  let provisional ← plans.mapM (fun plan => cell? usable plan 1)
  let topology ← indexPlan? usable.val provisional
  let resolved ← resolve usable (start + topology.pageCount) plans
  let finalPlan ← topology.withCells? resolved.cells
  return (← indexPages? usable.val start finalPlan) ++ resolved.overflow

/-- Reuse the canonical sqlite_schema record serializer, then apply exactly
the same local/overflow split as any other rowid table. -/
def catalogPlan? (rowid : Nat) (entry : CoreFile.CatalogEntry) : Option CoreOverflow.CellPlan := do
  let encoded ← CoreFile.catalogCell? rowid entry
  let (_, rest) ← decodeVarint encoded
  let (_, payload) ← decodeVarint rest
  return ⟨.table, encoded.take (encoded.length - payload.length), payload⟩

/-- Catalog records retain their physical rowids across a bulk rewrite.
The default remains the original consecutive canonical catalog. -/
def catalogRows (entries : List CoreFile.CatalogEntry) (identities : List CoreCatalogData.Identity) :
    Option (List (Nat × CoreFile.CatalogEntry)) := do
  let rows ← entries.zipIdx.mapM fun (entry,position) => do
    let rowid ← if identities.isEmpty then some (position + 1) else do
      let identity ← identities.find? (fun identity => identity.kind == entry.kind &&
        identity.name.toLower == entry.name.toLower)
      some identity.rowid
    unless 0 < rowid && rowid < 2^63 do none
    some (rowid,entry)
  let ordered := rows.mergeSort (fun left right => left.1 ≤ right.1)
  unless ordered.Pairwise (fun left right => left.1 < right.1) do none
  unless identities.isEmpty || identities.length == entries.length do none
  return ordered

def encode? (usable : UsablePageSize) (database : Core.Database)
    (baseHeader : DatabaseHeader)
    (indexSQL : Core.Table → Core.Index → String := CoreFile.indexSQL)
    (additionalCatalog : List CoreFile.CatalogEntry := [])
    (identities : List CoreCatalogData.Identity := []) :
    Option (Array (Array UInt8)) := do
  unless ValidSQLitePageSize usable.val do none
  let mut pages : Array (Page usable.val) := #[]
  let mut entries : Array CoreFile.CatalogEntry := #[]
  for table in database.tables do
    let start := 2 + pages.size
    let plans ← table.rows.mapM (CoreOverflow.tableCellPlan? table.schema)
    let encoded ← encodeTable? usable start plans
    entries := entries.push {
      kind := "table", name := table.schema.name, table := table.schema.name,
      rootPage := start, sql := CoreFile.tableSQL table }
    pages := pages ++ encoded.toArray
  for table in database.tables do
    for index in table.indexes do
      let start := 2 + pages.size
      let plans ← CoreOverflow.indexPlans table index
      let encoded ← encodeIndex? usable start plans
      entries := entries.push {
        kind := "index", name := index.name, table := table.schema.name,
        rootPage := start, sql := indexSQL table index,
        sqlIsNull := CoreAutomaticIndex.contains table index }
      pages := pages ++ encoded.toArray
  let rows ← catalogRows (entries.toList ++ additionalCatalog) identities
  let plans ← rows.mapM fun (rowid,entry) => catalogPlan? rowid entry
  let firstOverflow := 2 + pages.size
  let resolved ← resolve usable firstOverflow plans
  -- Page one has a 100-byte database header. If its cells do not fit, its
  -- zero-cell interior root points to a normal balanced catalog tree.
  let inlineCatalog := btreePage? usable.val 13 resolved.cells none (List.replicate 100 0)
  let (first, extra) ← match inlineCatalog with
    | some page => some (page, resolved.overflow)
    | none => do
        let catalog ← encodeTable? usable firstOverflow plans
        let first ← btreePage? usable.val 5 [] (some firstOverflow) (List.replicate 100 0)
        some (first, catalog)
  pages := pages ++ extra.toArray
  let count ← boundedU32? (1 + pages.size)
  let sizeField : U16Value := ⟨(if usable.val = 65536 then 1 else usable.val) % 65536,
    Nat.mod_lt _ (by decide)⟩
  let header : DatabaseHeader := {
    baseHeader with
    headerPrefix := {
      baseHeader.headerPrefix with
      pageSizeField := sizeField
      readVersion := 2
      writeVersion := 2
      reservedSpace := 0 }
    databaseSizePages := count }
  let first ← page? usable.val ((encodeDatabaseHeader header).toArray ++ first.bytes.extract 100 usable.val)
  return (#[first] ++ pages).map (·.bytes)

end SQLeanite.CoreSizedPageCodec
