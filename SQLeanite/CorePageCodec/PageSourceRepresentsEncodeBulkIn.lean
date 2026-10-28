import SQLeanite.CoreDecode.DecodeCanonicalPageBytesEncode
import SQLeanite.CorePageCodec.EncodeBulkFromState

namespace SQLeanite
namespace CorePageCodec

/-- The live store-owned bulk image is a left inverse of the general page
decoder, up to the intentional canonical rebuilding of proof-carrying row
trees.  Every table and promoted index entry is decoded from its actual page
interval; no re-encoding comparison appears in the statement or proof. -/
theorem pageSourceRepresents_encodeBulk_in
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image)
    (source : CoreDecode.PageSource)
    (catalogRead :
      source.readPage 1 >>= CoreDecode.decodeCatalogForOpen =
        (CoreDecode.PageSource.ofList
          (image.pages.map CoreFile.Page.bytes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen)
    (activeTailReads : CoreDecode.ReadsPagesFrom source 2 image.pages.tail)
    (enoughPages : image.pageCount ≤ source.pageCount) :
    CoreDecode.PageSourceRepresents source database := by
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
            let tableEntries := state.tables.map chunkTableCatalogEntry
            let indexEntries := CoreOverflow.indexEntriesOf indexEncodings
            let entries := tableEntries ++ indexEntries
            let treePages :=
              tableEncoding.treePages.map NumberedPage.page
            let indexPages := CoreOverflow.indexPagesOf indexEncodings
            let remaining := treePages ++ tableEncoding.overflowPages ++
              indexPages
            let count : FileFormat.U32Value := ⟨1 + remaining.length, by
              change 1 + remaining.length < 2 ^ 32
              simp only [remaining, treePages, indexPages]
              omega⟩
            change (do
              let schema ← CoreFile.schemaPageForEntries? entries count
              some ⟨database, schema :: remaining⟩) = some image at encoded
            cases schemaResult : CoreFile.schemaPageForEntries? entries count with
            | none =>
                simp [schemaResult] at encoded
            | some schemaPage =>
              rw [schemaResult] at encoded
              simp only [Option.bind_eq_bind, Option.bind,
                Option.some.injEq] at encoded
              subst image
              obtain ⟨tablePageCount, stateNext, statePages⟩ :=
                CoreChunkPageState.State.build?_interval stateResult
              have treeNumbers := encodeChunkTablesWithOverflow_pageNumbers
                state.nextPage state.tables tableEncoding tableResult
              rw [statePages] at treeNumbers
              have treeLength : treePages.length = tablePageCount := by
                have lengths := congrArg List.length treeNumbers
                simpa [treePages] using lengths
              have tableNext := encodeChunkTablesWithOverflow_nextPage
                state.nextPage state.tables tableEncoding tableResult
              have sourceCountLower : 1 + remaining.length ≤ source.pageCount := by
                simpa [CoreFile.Image.pageCount, Nat.add_comm] using enoughPages
              have remainingReads : CoreDecode.ReadsPagesFrom source 2
                  remaining := by
                simpa using activeTailReads
              have treeReads : CoreDecode.ReadsPagesFrom source 2 treePages := by
                apply CoreDecode.ReadsPagesFrom.left
                  (right := tableEncoding.overflowPages ++ indexPages)
                simpa [remaining, List.append_assoc] using remainingReads
              have treeContains : PageSourceContains source
                  tableEncoding.treePages := by
                apply PageSourceContains.ofReadsRange source 2
                · have numberedLength : tableEncoding.treePages.length =
                      tablePageCount := by
                    simpa [treePages] using treeLength
                  rw [numberedLength]
                  exact treeNumbers
                · exact treeReads
              have overflowReads : CoreDecode.ReadsPagesFrom source
                  state.nextPage tableEncoding.overflowPages := by
                have afterTree := CoreDecode.ReadsPagesFrom.right
                  (left := treePages)
                  (right := tableEncoding.overflowPages ++ indexPages)
                  (by simpa [remaining, List.append_assoc] using remainingReads)
                have overflow := CoreDecode.ReadsPagesFrom.left afterTree
                simpa [stateNext, treeLength, Nat.add_comm, Nat.add_left_comm,
                  Nat.add_assoc] using overflow
              have indexReads : CoreDecode.ReadsPagesFrom source
                  tableEncoding.nextPage indexPages := by
                have afterTree := CoreDecode.ReadsPagesFrom.right
                  (left := treePages)
                  (right := tableEncoding.overflowPages ++ indexPages)
                  (by simpa [remaining, List.append_assoc] using remainingReads)
                have afterOverflow := CoreDecode.ReadsPagesFrom.right
                  (left := tableEncoding.overflowPages) (right := indexPages)
                  afterTree
                simpa [tableNext, stateNext, treeLength, Nat.add_comm,
                  Nat.add_left_comm, Nat.add_assoc] using afterOverflow
              have individualIndexReads : ∀ encoding ∈ indexEncodings,
                  CoreDecode.ReadsPagesFrom source encoding.rootPage
                    encoding.pages :=
                CoreDecode.ReadsPagesFrom.encodeOverflowIndexTableGroups source
                  tableEncoding.nextPage database.tables indexEncodings
                  indexResult indexReads
              have indexRange : ∀ encoding ∈ indexEncodings,
                  tableEncoding.nextPage ≤ encoding.rootPage ∧
                  encoding.rootPage + encoding.pages.length ≤
                    tableEncoding.nextPage + indexPages.length := by
                simpa [indexPages] using
                  CoreOverflow.encodeIndexTableGroups_member_range
                    tableEncoding.nextPage database.tables indexEncodings
                    indexResult
              have tableNextPositive : 0 < tableEncoding.nextPage := by
                rw [tableNext, stateNext]
                omega
              have indexPositive : ∀ encoding ∈ indexEncodings,
                  0 < encoding.rootPage := by
                intro encoding member
                have range := indexRange encoding member
                omega
              have endBound : tableEncoding.nextPage + indexPages.length =
                  remaining.length + 2 := by
                simp only [remaining, List.length_append]
                rw [tableNext, stateNext, treeLength]
                omega
              have indexPageBound : ∀ encoding ∈ indexEncodings,
                  encoding.rootPage + encoding.pages.length < 2 ^ 32 := by
                intro encoding member
                have range := indexRange encoding member
                rw [endBound] at range
                change 1 + remaining.length + 1 < 2 ^ 32 at countBound
                omega
              have indexSourceBound : ∀ encoding ∈ indexEncodings,
                  encoding.rootPage + encoding.pages.length ≤
                    source.pageCount + 1 := by
                intro encoding member
                have range := indexRange encoding member
                rw [endBound] at range
                omega
              have tableHeights : ∀ table ∈ state.tables,
                  table.tree.root.erase.height < source.pageCount + 1 := by
                intro table member
                have height :=
                  RecursiveBPlusTree.Node.height_lt_pageCount
                    table.tree.root.erase
                have pageCount := PersistentPageTree.Node.pageIds_length
                  table.tree.root
                have included :=
                  CoreChunkPageState.TableState.pageIds_length_le_tablePageIds
                    member
                unfold CoreChunkPageState.TableState.pageIds at included
                rw [statePages] at included
                simp only [List.length_range'] at included
                omega
              have tablesDecoded :=
                decodeTablesFrom_encodeChunkTablesWithOverflow source
                  state.nextPage state.tables tableEncoding tableResult
                  treeContains overflowReads (by rw [stateNext]; omega)
                  (by
                    rw [stateNext]
                    change 1 + remaining.length + 1 < 2 ^ 32 at countBound
                    simp only [remaining, List.length_append, List.length_map]
                      at countBound
                    omega)
                  (by omega) tableHeights
              have safe : ∀ entry ∈ entries,
                  CoreDecode.CatalogTextRoundtrips entry := by
                intro entry _
                exact ⟨utf8 entry.kind, utf8 entry.name,
                  utf8 entry.table, utf8 entry.sql⟩
              have catalogDecoded :=
                CoreDecode.decodeCatalogForOpen_schemaPageForEntries
                  entries count safe schemaResult
              have tableFilter :
                  ((entries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "table")) =
                    tableEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                rw [show entries.map CoreDecode.CatalogEntry.ofEncoded =
                    tableEntries.map CoreDecode.CatalogEntry.ofEncoded ++
                      indexEntries.map CoreDecode.CatalogEntry.ofEncoded by
                  simp [entries]]
                rw [List.filter_append]
                have tablesKept :
                    (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                      (fun entry => entry.kind == "table") =
                        tableEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                  apply List.filter_eq_self.mpr
                  intro entry member
                  rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember,
                    rfl⟩
                  rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
                  rfl
                have indexesRemoved :
                    (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                      (fun entry => entry.kind == "table") = [] := by
                  apply List.filter_eq_nil_iff.mpr
                  intro entry member
                  rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember,
                    rfl⟩
                  rcases List.mem_map.mp encodedMember with ⟨encoding, _, rfl⟩
                  simp [CoreOverflow.IndexEncoding.catalogEntry,
                    CoreDecode.CatalogEntry.ofEncoded]
                rw [tablesKept, indexesRemoved, List.append_nil]
              have indexFilter :
                  ((entries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "index")) =
                    indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                rw [show entries.map CoreDecode.CatalogEntry.ofEncoded =
                    tableEntries.map CoreDecode.CatalogEntry.ofEncoded ++
                      indexEntries.map CoreDecode.CatalogEntry.ofEncoded by
                  simp [entries]]
                rw [List.filter_append]
                have tablesRemoved :
                    (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                      (fun entry => entry.kind == "index") = [] := by
                  apply List.filter_eq_nil_iff.mpr
                  intro entry member
                  rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember,
                    rfl⟩
                  rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
                  simp [chunkTableCatalogEntry,
                    CoreDecode.CatalogEntry.ofEncoded]
                have indexesKept :
                    (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                      (fun entry => entry.kind == "index") =
                        indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                  apply List.filter_eq_self.mpr
                  intro entry member
                  rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember,
                    rfl⟩
                  rcases List.mem_map.mp encodedMember with ⟨encoding, _, rfl⟩
                  rfl
                rw [tablesRemoved, indexesKept, List.nil_append]
              have tableList :
                  state.tables.map (fun table => table.table.withoutIndexes) =
                    database.tables.map Core.Table.withoutIndexes := by
                have stateTables :=
                  (CoreChunkPageState.State.build?_represents stateResult).2.1
                rw [← stateTables]
                simp [List.map_map, Function.comp_def]
              have tablesDecoded' :
                  (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).mapM
                      (CoreDecode.decodeTableFrom source) =
                    some (database.tables.map Core.Table.withoutIndexes) := by
                unfold tableEntries
                simpa [List.map_map, Function.comp_def, tableList]
                  using tablesDecoded
              have indexesApplied :=
                CoreDecode.applyIndexesForOpen_overflowEncoded source database
                  tableEncoding.nextPage indexEncodings indexResult
                  individualIndexReads indexPositive indexPageBound
                  indexSourceBound
              have indexesApplied' :
                  CoreDecode.applyIndexesForOpen source database.withoutIndexes
                    (indexEntries.map CoreDecode.CatalogEntry.ofEncoded) =
                      some database.canonicalize := by
                simpa [indexEntries, CoreOverflow.indexEntriesOf,
                  List.map_map, Function.comp_def] using indexesApplied
              have canonicalFirstRead :
                  (CoreDecode.PageSource.ofList
                    ((schemaPage :: remaining).map CoreFile.Page.bytes)).readPage
                      1 = some schemaPage.bytes := by
                simp [CoreDecode.PageSource.ofList, CoreDecode.page?]
              refine .intro (entries.map CoreDecode.CatalogEntry.ofEncoded)
                ?_ ?_ ?_
              · rw [catalogRead, canonicalFirstRead]
                simp only [Option.bind_eq_bind, Option.bind]
                exact catalogDecoded
              · rw [tableFilter]
                exact tablesDecoded'
              · rw [indexFilter]
                exact indexesApplied'
          next => contradiction

theorem decodeFromPageSource_encodeBulk_in (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image)
    (source : CoreDecode.PageSource)
    (catalogRead :
      source.readPage 1 >>= CoreDecode.decodeCatalogForOpen =
        (CoreDecode.PageSource.ofList
          (image.pages.map CoreFile.Page.bytes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen)
    (activeTailReads : CoreDecode.ReadsPagesFrom source 2 image.pages.tail)
    (enoughPages : image.pageCount ≤ source.pageCount) :
    CoreDecode.decodeFromPageSource source = some database.canonicalize :=
  (pageSourceRepresents_encodeBulk_in utf8 database image encoded source
    catalogRead activeTailReads enoughPages).decode

theorem decodeFromPageSource_encodeBulk (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image) :
    CoreDecode.decodeFromPageSource
      (.ofList (image.pages.map CoreFile.Page.bytes)) =
        some database.canonicalize := by
  apply decodeFromPageSource_encodeBulk_in utf8 database image encoded
  · rfl
  · exact CoreDecode.ReadsPagesFrom.ofList_tail image.pages
  · simp [CoreDecode.PageSource.ofList, CoreFile.Image.pageCount]

/-- The live bulk encoder persists the generated-image provenance stamp in
the bytes that a cold reader actually parses. -/
theorem encodeBulk_generatedHeader {database : Core.Database}
    {image : CoreFile.Image} (encoded : encodeBulk database = some image) :
    ∃ header suffix,
      FileFormat.decodeDatabaseHeader image.fileBytes = some (header, suffix) ∧
      CoreFile.GeneratedImageHeader header := by
  rcases encodeBulk_header encoded with
    ⟨count, schema, remaining, body, pagesEqual, _, headerEqual⟩
  refine ⟨CoreFile.databaseHeader count,
    body ++ remaining.flatMap CoreFile.Page.bytes, ?_,
    CoreFile.databaseHeader_generatedImage count⟩
  unfold CoreFile.Image.fileBytes
  rw [pagesEqual]
  simp only [List.flatMap_cons]
  rw [headerEqual]
  simpa [List.append_assoc] using
    FileFormat.decodeDatabaseHeader_encode (CoreFile.databaseHeader count)
      (body ++ remaining.flatMap CoreFile.Page.bytes)

theorem decode_encodeBulk (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : encodeBulk database = some image) :
    CoreDecode.decode image.fileBytes = some database.canonicalize := by
  rcases encodeBulk_header encoded with
    ⟨count, schema, remaining, body, pagesEqual, countEqual, headerEqual⟩
  have bytesLayout : image.fileBytes =
      FileFormat.encodeDatabaseHeader (CoreFile.databaseHeader count) ++
        (body ++ remaining.flatMap CoreFile.Page.bytes) := by
    unfold CoreFile.Image.fileBytes
    rw [pagesEqual]
    simp only [List.flatMap_cons]
    rw [headerEqual]
    simp [List.append_assoc]
  have fileLength : image.fileBytes.length =
      count.val * PhysicalCodec.pageSize := by
    rw [CoreFile.Image.fileBytes_length, countEqual, Nat.mul_comm]
  have splitPages : CoreDecode.pages count.val image.fileBytes =
      image.pages.map CoreFile.Page.bytes := by
    rw [← countEqual]
    exact CoreDecode.pages_image image
  unfold CoreDecode.decode
  rw [bytesLayout, FileFormat.decodeDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show (CoreFile.databaseHeader count).databaseSizePages.val = count.val
    from rfl]
  rw [dif_pos (by rfl), dif_pos (by rfl), dif_pos (by rfl)]
  rw [← bytesLayout]
  rw [dif_pos fileLength, splitPages]
  exact decodeFromPageSource_encodeBulk utf8 database image encoded

/-- Compatibility name retained for adapters.  The former runtime decode and
whole-database comparison has been discharged by `decode_encodeBulk`; emitted
bytes now come directly from the proved bulk encoder. -/
def encodeChecked (database : Core.Database) : Option CoreFile.Image :=
  encodeBulk database

theorem decode_encodeChecked (utf8 : CoreDecode.UTF8Roundtrips)
    {database : Core.Database} {image : CoreFile.Image}
    (encoded : encodeChecked database = some image) :
    ∃ decoded, CoreDecode.decode image.fileBytes = some decoded ∧
      decoded.Equiv database := by
  unfold encodeChecked at encoded
  exact ⟨database.canonicalize,
    decode_encodeBulk utf8 database image encoded,
    database.canonicalize_equiv⟩

end CorePageCodec

end SQLeanite
