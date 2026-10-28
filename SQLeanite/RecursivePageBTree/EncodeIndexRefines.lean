import SQLeanite.RecursivePageBTree.IndexStore

namespace SQLeanite
namespace RecursivePageBTree

theorem encodeIndex_refines {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {encoding : IndexEncoding}
    (encoded : encodeIndex rootPage table index = some encoding) :
    ∃ cells leaves,
      CoreFile.indexCells table index = some cells ∧
      CoreFile.indexLeaves table index = some leaves ∧
      encoding.plan.toCells = cells := by
  unfold encodeIndex at encoded
  cases leavesResult : CoreFile.indexLeaves table index with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : buildIndex leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        unfold CoreFile.indexLeaves at leavesResult
        cases cellsResult : CoreFile.indexCells table index with
        | none => simp [cellsResult] at leavesResult
        | some cells =>
          simp only [cellsResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at leavesResult
          subst leaves
          refine ⟨cells, CellPagination.paginateCells cells, rfl, ?_, ?_⟩
          · simp [CoreFile.indexLeaves, cellsResult]
          · rw [buildIndex_toCells planResult]
            exact CellPagination.flatten_paginateCells cells

def encodeIndexes : Nat → List (Core.Table × Core.Index) →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, indexed :: indexes => do
      let encoded ← encodeIndex nextPage indexed.1 indexed.2
      let remaining ← encodeIndexes (nextPage + encoded.plan.pageCount) indexes
      some (encoded :: remaining)

def indexPagesOf (encodings : List IndexEncoding) : List CoreFile.Page :=
  encodings.flatMap (fun encoding => encoding.pages)

def IndexEncoding.catalogEntry (encoding : IndexEncoding) : CoreFile.CatalogEntry := {
  kind := "index"
  name := encoding.index.name
  table := encoding.table.schema.name
  rootPage := encoding.rootPage
  sql := CoreFile.indexSQL encoding.table encoding.index
  sqlIsNull := encoding.index.isImplicitPrimary encoding.table.schema }

def indexEntriesOf (encodings : List IndexEncoding) : List CoreFile.CatalogEntry :=
  encodings.map IndexEncoding.catalogEntry

theorem encodeIndex_pages_length {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {encoding : IndexEncoding}
    (encoded : encodeIndex rootPage table index = some encoding) :
    encoding.pages.length = encoding.plan.pageCount := by
  unfold encodeIndex at encoded
  cases leavesResult : CoreFile.indexLeaves table index with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : buildIndex leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        exact plan.encodePagesFrom_length pagesResult

/-- General Core image encoder with recursive table and index trees. -/
def encode (database : Core.Database) : Option CoreFile.Image := do
  let tableEncodings ← encodeTables 2 database.tables
  let tablePages := tablePagesOf tableEncodings
  let indexEncodings ← encodeIndexes (2 + tablePages.length)
    (CoreFile.indexedIndexes database)
  let entries := tableEntriesOf tableEncodings ++
    indexEntriesOf indexEncodings
  let remaining := tablePages ++ indexPagesOf indexEncodings
  let total := 1 + remaining.length
  if countBound : total < 2 ^ 32 then
    let count : FileFormat.U32Value := ⟨total, by simpa using countBound⟩
    let schema ← CoreFile.schemaPageForEntries? entries count
    some ⟨database, schema :: remaining⟩
  else none

theorem encode_tables_aligned {database : Core.Database} {image : CoreFile.Image}
    (encoded : encode database = some image) :
    ∃ tableEncodings,
      encodeTables 2 database.tables = some tableEncodings ∧
      tableEncodings.map (fun encoding => encoding.table) = database.tables := by
  unfold encode at encoded
  cases tableResult : encodeTables 2 database.tables with
  | none => simp [tableResult] at encoded
  | some tableEncodings =>
    refine ⟨tableEncodings, rfl,
      encodeTables_tables 2 database.tables tableEncodings tableResult⟩

end RecursivePageBTree

end SQLeanite
