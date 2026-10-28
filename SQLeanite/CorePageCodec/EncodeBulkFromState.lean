import SQLeanite.CoreChunkPageState.TableStateBuildTable
import SQLeanite.CorePageCodec.LookupTableRangeFromEncodeChunkNodeWithOverflowExact

namespace SQLeanite
namespace CorePageCodec

/-- Encode from a persistent table state already proved to represent the input
database.  Keeping this phase separate lets the live commit retain the exact
state whose page identities the encoder serialized. -/
def encodeBulkFromState (database : Core.Database)
    (state : CoreChunkPageState.State) : Option CoreFile.Image := do
  let tableEncoding ← encodeChunkTablesWithOverflow state.nextPage state.tables
  let indexEncodings ← CoreOverflow.encodeIndexTableGroups
    tableEncoding.nextPage database.tables
  let entries := state.tables.map chunkTableCatalogEntry ++
    CoreOverflow.indexEntriesOf indexEncodings
  -- `State.build?` assigns page identities in preorder, and
  -- `encodeChunkTables_pageNumbers` proves this list is already the contiguous
  -- allocation interval.  No runtime sort is needed to recover file order.
  let remaining := tableEncoding.treePages.map NumberedPage.page ++
    tableEncoding.overflowPages ++
    CoreOverflow.indexPagesOf indexEncodings
  let total := 1 + remaining.length
  if countBound : total + 1 < 2 ^ 32 then
    let count : FileFormat.U32Value := ⟨total, by omega⟩
    let schema ← CoreFile.schemaPageForEntries? entries count
    some ⟨database, schema :: remaining⟩
  else none

/-- Bulk encoder for the new representation.  Table page identities come from
`CorePageState`; physical index B-trees are appended using the existing
overflow-aware index encoder until stable identified index pages land. -/
def encodeBulk (database : Core.Database) : Option CoreFile.Image := do
  let state ← CoreChunkPageState.State.build? database
  encodeBulkFromState database state

/-- The live writer's bulk result retains the persistent state used by the
encoder, avoiding a second construction pass after the bytes are committed. -/
def encodeBulkWithState (database : Core.Database) :
    Option (CoreFile.Image × CoreChunkPageState.State) := do
  let state ← CoreChunkPageState.State.build? database
  let image ← encodeBulkFromState database state
  some (image, state)

theorem encodeBulkWithState_image {database : Core.Database}
    {result : CoreFile.Image × CoreChunkPageState.State}
    (encoded : encodeBulkWithState database = some result) :
    encodeBulk database = some result.1 := by
  unfold encodeBulkWithState at encoded
  rcases Option.bind_eq_some_iff.mp encoded with ⟨state, stateResult, encoded⟩
  rcases Option.bind_eq_some_iff.mp encoded with ⟨image, imageResult, encoded⟩
  simp only [Option.some.injEq] at encoded
  subst result
  unfold encodeBulk
  rw [stateResult]
  exact imageResult

theorem encodeBulkWithState_represents {database : Core.Database}
    {result : CoreFile.Image × CoreChunkPageState.State}
    (encoded : encodeBulkWithState database = some result) :
    result.2.Represents database := by
  unfold encodeBulkWithState at encoded
  rcases Option.bind_eq_some_iff.mp encoded with ⟨state, stateResult, encoded⟩
  rcases Option.bind_eq_some_iff.mp encoded with ⟨image, imageResult, encoded⟩
  simp only [Option.some.injEq] at encoded
  subst result
  exact CoreChunkPageState.State.build?_represents stateResult

theorem encodeBulk_database {database : Core.Database} {image : CoreFile.Image}
    (encoded : encodeBulk database = some image) : image.database = database := by
  unfold encodeBulk encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
      simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
      cases tableResult : encodeChunkTablesWithOverflow state.nextPage
          state.tables with
      | none => simp [tableResult] at encoded
      | some tableEncoding =>
          simp only [tableResult] at encoded
          cases indexResult : CoreOverflow.encodeIndexTableGroups
              tableEncoding.nextPage database.tables with
          | none => simp [indexResult] at encoded
          | some indexes =>
              simp only [indexResult] at encoded
              split at encoded
              next bound =>
                let entries := state.tables.map chunkTableCatalogEntry ++
                  CoreOverflow.indexEntriesOf indexes
                let remaining := tableEncoding.treePages.map NumberedPage.page ++
                  tableEncoding.overflowPages ++
                  CoreOverflow.indexPagesOf indexes
                let count : FileFormat.U32Value :=
                  ⟨1 + remaining.length, by
                    change 1 + remaining.length < 2 ^ 32
                    simp only [remaining]
                    omega⟩
                change (do
                  let schema ← CoreFile.schemaPageForEntries? entries count
                  some ⟨database, schema :: remaining⟩) = some image at encoded
                cases schemaResult : CoreFile.schemaPageForEntries? entries count with
                | none => simp [schemaResult] at encoded
                | some schema =>
                    rw [schemaResult] at encoded
                    simp only [Option.bind_eq_bind, Option.bind,
                      Option.some.injEq] at encoded
                    subst image
                    rfl
              next => contradiction

theorem encodeBulk_header {database : Core.Database} {image : CoreFile.Image}
    (encoded : encodeBulk database = some image) :
    ∃ (count : FileFormat.U32Value) (schema : CoreFile.Page)
      (remaining : List CoreFile.Page) (body : List UInt8),
      image.pages = schema :: remaining ∧
      image.pageCount = count.val ∧
      schema.bytes = FileFormat.encodeDatabaseHeader
        (CoreFile.databaseHeader count) ++ body := by
  unfold encodeBulk encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
      simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
      cases tableResult : encodeChunkTablesWithOverflow state.nextPage
          state.tables with
      | none => simp [tableResult] at encoded
      | some tableEncoding =>
        simp only [tableResult] at encoded
        cases indexResult : CoreOverflow.encodeIndexTableGroups
            tableEncoding.nextPage database.tables with
        | none => simp [indexResult] at encoded
        | some indexEncodings =>
          simp only [indexResult] at encoded
          split at encoded
          next countBound =>
            let entries := state.tables.map chunkTableCatalogEntry ++
              CoreOverflow.indexEntriesOf indexEncodings
            let remaining := tableEncoding.treePages.map NumberedPage.page ++
              tableEncoding.overflowPages ++
              CoreOverflow.indexPagesOf indexEncodings
            let count : FileFormat.U32Value := ⟨1 + remaining.length, by
              simp only [remaining, List.length_append, List.length_map]
              simp only [List.length_append, List.length_map] at countBound
              omega⟩
            change (do
              let schema ← CoreFile.schemaPageForEntries? entries count
              some ⟨database, schema :: remaining⟩) = some image at encoded
            cases schemaResult : CoreFile.schemaPageForEntries? entries count with
            | none => simp [schemaResult] at encoded
            | some schema =>
              rw [schemaResult] at encoded
              simp only [Option.bind_eq_bind, Option.bind,
                Option.some.injEq] at encoded
              subst image
              rcases CoreFile.schemaPageForEntries_header schemaResult with
                ⟨body, header⟩
              refine ⟨count, schema, remaining, body, rfl, ?_, header⟩
              simp [CoreFile.Image.pageCount, count, remaining, Nat.add_comm]
          next => contradiction

/-- The generated schema B-tree has the same meaning after replacing only its
100-byte database header.  This is the catalog bridge used by SQLite freelist
images, whose size/freelist fields differ from the canonical bulk image. -/
theorem decodeCatalogForOpen_encodeBulk_replaceHeader
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image)
    (first : CoreFile.Page) (remainingPages : List CoreFile.Page)
    (pagesEqual : image.pages = first :: remainingPages)
    (headerBytes : List UInt8) (headerLength : headerBytes.length = 100) :
    CoreDecode.decodeCatalogForOpen (headerBytes ++ first.bytes.drop 100) =
      CoreDecode.decodeCatalogForOpen first.bytes := by
  unfold encodeBulk encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
      simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
      cases tableResult : encodeChunkTablesWithOverflow state.nextPage
          state.tables with
      | none => simp [tableResult] at encoded
      | some tableEncoding =>
          simp only [tableResult] at encoded
          cases indexResult : CoreOverflow.encodeIndexTableGroups
              tableEncoding.nextPage database.tables with
          | none => simp [indexResult] at encoded
          | some indexEncodings =>
              simp only [indexResult] at encoded
              split at encoded
              next countBound =>
                let entries := state.tables.map chunkTableCatalogEntry ++
                  CoreOverflow.indexEntriesOf indexEncodings
                let pages := tableEncoding.treePages.map NumberedPage.page ++
                  tableEncoding.overflowPages ++
                  CoreOverflow.indexPagesOf indexEncodings
                let count : FileFormat.U32Value := ⟨1 + pages.length, by
                  simp only [pages, List.length_append, List.length_map]
                  simp only [List.length_append, List.length_map] at countBound
                  omega⟩
                change (do
                  let schema ← CoreFile.schemaPageForEntries? entries count
                  some ⟨database, schema :: pages⟩) = some image at encoded
                cases schemaResult : CoreFile.schemaPageForEntries? entries count with
                | none => simp [schemaResult] at encoded
                | some schema =>
                    rw [schemaResult] at encoded
                    simp only [Option.bind_eq_bind, Option.bind,
                      Option.some.injEq] at encoded
                    subst image
                    simp only at pagesEqual
                    injection pagesEqual with firstEqual
                    subst first
                    have safe : ∀ entry ∈ entries,
                        CoreDecode.CatalogTextRoundtrips entry := by
                      intro entry _
                      exact ⟨utf8 entry.kind, utf8 entry.name,
                        utf8 entry.table, utf8 entry.sql⟩
                    exact
                      (CoreDecode.decodeCatalogForOpen_schemaPageForEntries_withHeader
                        entries count headerBytes headerLength safe
                        schemaResult).trans
                      (CoreDecode.decodeCatalogForOpen_schemaPageForEntries
                        entries count safe schemaResult).symm
              next => contradiction

end CorePageCodec

end SQLeanite
