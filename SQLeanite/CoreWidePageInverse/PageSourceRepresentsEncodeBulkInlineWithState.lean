import SQLeanite.CoreDecode.DecodeCanonicalPageBytesEncode
import SQLeanite.CoreWideIndex.DecodeCanonicalIndexesForTableEncodeIndexes
import SQLeanite.CoreWidePageInverse.DecodeSubtreeRowsFromEncodeChunkNode

namespace SQLeanite
namespace CoreWidePageInverse

/-- The complete inline high-fanout image has the logical meaning carried by
its proof-owned state.  Tables are decoded by arbitrary-fanout traversal;
secondary indexes reuse the established promoted-key inverse. -/
theorem pageSourceRepresents_encodeBulkInlineWithState
    (utf8 : CoreDecode.UTF8Roundtrips) (database : Core.Database)
    (image : CoreFile.Image) (wideState : CoreWidePageState.State)
    (encoded : CoreWidePageCodec.encodeBulkInlineWithState database =
      some (image, wideState)) :
    CoreDecode.PageSourceRepresents
      (.ofList (image.pages.map CoreFile.Page.bytes)) database := by
  unfold CoreWidePageCodec.encodeBulkInlineWithState at encoded
  rcases Option.bind_eq_some_iff.mp encoded with ⟨state, stateResult, encoded⟩
  split at encoded
  next inlineResult =>
    rcases Option.bind_eq_some_iff.mp encoded with
      ⟨numbered, numberedResult, encoded⟩
    let ordered := CorePageCodec.orderNumberedPages
      (CoreWidePageCodec.includePendingBytePlaceholder state.nextPage numbered)
    dsimp only at encoded
    split at encoded
    next numbers =>
      rcases Option.bind_eq_some_iff.mp encoded with
        ⟨indexEncodings, indexResult, encoded⟩
      split at encoded
      next countBound =>
        let tableEntries := state.tables.map CoreWidePageCodec.tableCatalogEntry
        let indexEntries := CoreWideIndex.indexEntriesOf indexEncodings
        let entries := tableEntries ++ indexEntries
        let indexPages := CoreWideIndex.indexPagesOf indexEncodings
        let remaining := ordered.map CorePageCodec.NumberedPage.page ++ indexPages
        let count : FileFormat.U32Value := ⟨1 + remaining.length, by
          change 1 + remaining.length < 2 ^ 32
          have stronger : 1 + remaining.length + 1 < 2 ^ 32 := by
            simpa [remaining, ordered, indexPages] using countBound
          omega⟩
        change (do
          let schema ← CoreFile.schemaPageForEntries? entries count
          some (⟨database, schema :: remaining⟩, state)) =
            some (image, wideState) at encoded
        cases schemaResult : CoreFile.schemaPageForEntries? entries count with
        | none => simp [schemaResult] at encoded
        | some schemaPage =>
          rw [schemaResult] at encoded
          simp only [Option.bind_eq_bind, Option.bind, Option.some.injEq,
            Prod.mk.injEq] at encoded
          rcases encoded with ⟨imageEqual, stateEqual⟩
          subst image
          subst wideState
          let source : CoreDecode.PageSource := .ofList
            ((schemaPage :: remaining).map CoreFile.Page.bytes)
          have stateNextLower : 2 ≤ state.nextPage :=
            CoreWidePageState.State.build?_nextPage_ge stateResult
          have orderedCount : ordered.length = state.nextPage - 2 := by
            have lengths := congrArg List.length numbers
            simpa using lengths
          have startEqual : 2 + ordered.length = state.nextPage := by
            rw [orderedCount]
            omega
          have orderedNumbers : ordered.map
              CorePageCodec.NumberedPage.pageNumber =
                List.range' 2 ordered.length := by
            simpa [orderedCount] using numbers
          have remainingReads : CoreDecode.ReadsPagesFrom source 2 remaining := by
            simpa [source] using CoreDecode.ReadsPagesFrom.ofList_append
              [schemaPage.bytes] remaining []
          have orderedReads : CoreDecode.ReadsPagesFrom source 2
              (ordered.map CorePageCodec.NumberedPage.page) := by
            exact CoreDecode.ReadsPagesFrom.left
              (right := indexPages) (by simpa [remaining] using remainingReads)
          have orderedContains : CorePageCodec.PageSourceContains source ordered :=
            CorePageCodec.PageSourceContains.ofReadsRange source 2 ordered
              orderedNumbers orderedReads
          have numberedContains :
              CorePageCodec.PageSourceContains source numbered := by
            intro page member
            apply orderedContains page
            apply List.mem_mergeSort.mpr
            unfold CoreWidePageCodec.includePendingBytePlaceholder
            split <;> simp_all
          have numberedLengthLe : numbered.length ≤ ordered.length := by
            simp [ordered, CorePageCodec.orderNumberedPages,
              CoreWidePageCodec.includePendingBytePlaceholder]
            split <;> simp
          have sourceCount : source.pageCount = 1 + remaining.length := by
            simp [source, CoreDecode.PageSource.ofList, Nat.add_comm]
          have tablesDecoded := decodeTablesFrom_encodeTables source state.tables
            numbered numberedResult numberedContains (by
              rw [sourceCount]
              simp only [remaining, List.length_append, List.length_map]
              omega)
            (fun table member =>
              CoreWidePageCodec.rowsInline_spec inlineResult table member)
          have tableList :
              state.tables.map (fun table => table.table.withoutIndexes) =
                database.tables.map Core.Table.withoutIndexes := by
            calc
              _ = (state.tables.map (fun table => table.table)).map
                    Core.Table.withoutIndexes := by
                  simp [List.map_map, Function.comp_def]
              _ = database.tables.map Core.Table.withoutIndexes := by
                  rw [state.tables_eq,
                    (CoreWidePageState.State.build?_represents stateResult).1]
          have tablesDecoded' :
              (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).mapM
                  (CoreDecode.decodeTableFrom source) =
                some (database.tables.map Core.Table.withoutIndexes) := by
            unfold tableEntries
            simpa [List.map_map, Function.comp_def, tableList]
              using tablesDecoded
          have indexReads : CoreDecode.ReadsPagesFrom source state.nextPage
              indexPages := by
            have afterTables := CoreDecode.ReadsPagesFrom.right
              (left := ordered.map CorePageCodec.NumberedPage.page)
              (right := indexPages)
              (by simpa [remaining] using remainingReads)
            simpa [startEqual] using afterTables
          let indexNumbered := CoreWideIndex.numberedPagesOf indexEncodings
          have indexNumbers : indexNumbered.map
                CorePageCodec.NumberedPage.pageNumber =
              List.range' state.nextPage indexPages.length := by
            simpa [indexNumbered, indexPages] using
              CoreWideIndex.encodeIndexTableGroups_numbers state.nextPage
                database.tables indexEncodings indexResult
          have indexPageMap : indexNumbered.map
                CorePageCodec.NumberedPage.page = indexPages := by
            simpa [indexNumbered, indexPages] using
              (CoreWideIndex.indexPagesOf_eq_map indexEncodings).symm
          have indexNumberedLength : indexNumbered.length =
              indexPages.length := by
            have equal := congrArg List.length indexPageMap
            simpa using equal
          have indexNumbers' : indexNumbered.map
                CorePageCodec.NumberedPage.pageNumber =
              List.range' state.nextPage indexNumbered.length := by
            simpa [indexNumberedLength] using indexNumbers
          have indexNumberedReads : CoreDecode.ReadsPagesFrom source
              state.nextPage
              (indexNumbered.map CorePageCodec.NumberedPage.page) := by
            simpa [indexPageMap] using indexReads
          have allIndexesContain : CorePageCodec.PageSourceContains source
              indexNumbered :=
            CorePageCodec.PageSourceContains.ofReadsRange source
              state.nextPage indexNumbered indexNumbers' indexNumberedReads
          have individualIndexContains : ∀ encoding ∈ indexEncodings,
              CorePageCodec.PageSourceContains source
                encoding.numberedPages := by
            intro encoding member page pageMember
            apply allIndexesContain page
            unfold indexNumbered CoreWideIndex.numberedPagesOf
            simp only [List.mem_flatMap]
            exact ⟨encoding, member, List.mem_mergeSort.mpr pageMember⟩
          have individualIndexBound : ∀ encoding ∈ indexEncodings,
              encoding.numberedPages.length < source.pageCount + 1 := by
            intro encoding member
            have lengthBound :=
              CoreWideIndex.numberedPages_length_le_of_mem member
            unfold indexNumbered at indexNumberedLength
            rw [indexNumberedLength] at lengthBound
            have indexWithinRemaining : indexPages.length ≤
                remaining.length := by
              simp [remaining]
            rw [sourceCount]
            omega
          have indexesApplied :=
            CoreWideIndex.applyIndexesForOpen_encoded source database
              state.nextPage indexEncodings indexResult
              individualIndexContains individualIndexBound
          have indexesApplied' :
              CoreDecode.applyIndexesForOpen source database.withoutIndexes
                (indexEntries.map CoreDecode.CatalogEntry.ofEncoded) =
                  some database.canonicalize := by
            simpa [indexEntries, CoreWideIndex.indexEntriesOf, List.map_map,
              Function.comp_def] using indexesApplied
          have safe : ∀ entry ∈ entries,
              CoreDecode.CatalogTextRoundtrips entry := by
            intro entry _
            exact ⟨utf8 entry.kind, utf8 entry.name,
              utf8 entry.table, utf8 entry.sql⟩
          have catalogDecoded :=
            CoreDecode.decodeCatalogForOpen_schemaPageForEntries entries count
              safe schemaResult
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
              rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
              rfl
            have indexesRemoved :
                (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                  (fun entry => entry.kind == "table") = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro entry member
              rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp encodedMember with ⟨encoding, _, rfl⟩
              simp [CoreWideIndex.IndexEncoding.catalogEntry,
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
              rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
              simp [CoreWidePageCodec.tableCatalogEntry,
                CoreDecode.CatalogEntry.ofEncoded]
            have indexesKept :
                (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                  (fun entry => entry.kind == "index") =
                    indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
              apply List.filter_eq_self.mpr
              intro entry member
              rcases List.mem_map.mp member with ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp encodedMember with ⟨encoding, _, rfl⟩
              rfl
            rw [tablesRemoved, indexesKept, List.nil_append]
          have firstRead : source.readPage 1 = some schemaPage.bytes := by
            simp [source, CoreDecode.PageSource.ofList, CoreDecode.page?]
          refine .intro (entries.map CoreDecode.CatalogEntry.ofEncoded) ?_ ?_ ?_
          · rw [firstRead]
            simp only [Option.bind_eq_bind, Option.bind]
            exact catalogDecoded
          · rw [tableFilter]
            exact tablesDecoded'
          · rw [indexFilter]
            exact indexesApplied'
      next => contradiction
    next => contradiction
  next => contradiction

theorem pageSourceRepresents_encodeBulkInline
    (utf8 : CoreDecode.UTF8Roundtrips) (database : Core.Database)
    (image : CoreFile.Image)
    (encoded : CoreWidePageCodec.encodeBulkInline database = some image) :
    CoreDecode.PageSourceRepresents
      (.ofList (image.pages.map CoreFile.Page.bytes)) database := by
  unfold CoreWidePageCodec.encodeBulkInline at encoded
  cases resultEq : CoreWidePageCodec.encodeBulkInlineWithState database with
  | none => simp [resultEq] at encoded
  | some result =>
      rcases result with ⟨builtImage, state⟩
      simp only [resultEq, Option.map, Option.some.injEq] at encoded
      subst image
      exact pageSourceRepresents_encodeBulkInlineWithState utf8 database
        builtImage state resultEq

theorem decodeFromPageSource_encodeBulkInline
    (utf8 : CoreDecode.UTF8Roundtrips) (database : Core.Database)
    (image : CoreFile.Image)
    (encoded : CoreWidePageCodec.encodeBulkInline database = some image) :
    CoreDecode.decodeFromPageSource
      (.ofList (image.pages.map CoreFile.Page.bytes)) =
        some database.canonicalize :=
  (pageSourceRepresents_encodeBulkInline utf8 database image encoded).decode

theorem encodeBulkInline_header {database : Core.Database}
    {image : CoreFile.Image}
    (encoded : CoreWidePageCodec.encodeBulkInline database = some image) :
    ∃ (count : FileFormat.U32Value) (schema : CoreFile.Page)
      (remaining : List CoreFile.Page) (body : List UInt8),
      image.pages = schema :: remaining ∧
      image.pageCount = count.val ∧
      schema.bytes = FileFormat.encodeDatabaseHeader
        (CoreFile.databaseHeader count) ++ body := by
  unfold CoreWidePageCodec.encodeBulkInline at encoded
  cases resultEq : CoreWidePageCodec.encodeBulkInlineWithState database with
  | none => simp [resultEq] at encoded
  | some result =>
    rcases result with ⟨builtImage, builtState⟩
    simp only [resultEq, Option.map, Option.some.injEq] at encoded
    subst image
    unfold CoreWidePageCodec.encodeBulkInlineWithState at resultEq
    rcases Option.bind_eq_some_iff.mp resultEq with ⟨state, stateResult, resultEq⟩
    split at resultEq
    next =>
      rcases Option.bind_eq_some_iff.mp resultEq with
        ⟨numbered, numberedResult, resultEq⟩
      dsimp only at resultEq
      split at resultEq
      next =>
        rcases Option.bind_eq_some_iff.mp resultEq with
          ⟨indexEncodings, indexResult, resultEq⟩
        split at resultEq
        next countBound =>
          let ordered := CorePageCodec.orderNumberedPages
            (CoreWidePageCodec.includePendingBytePlaceholder state.nextPage
              numbered)
          let entries := state.tables.map CoreWidePageCodec.tableCatalogEntry ++
            CoreWideIndex.indexEntriesOf indexEncodings
          let remaining := ordered.map CorePageCodec.NumberedPage.page ++
            CoreWideIndex.indexPagesOf indexEncodings
          let count : FileFormat.U32Value := ⟨1 + remaining.length, by
            have stronger : 1 + remaining.length + 1 < 2 ^ 32 := by
              simpa [remaining, ordered] using countBound
            omega⟩
          change (do
            let schema ← CoreFile.schemaPageForEntries? entries count
            some (⟨database, schema :: remaining⟩, state)) =
              some (builtImage, builtState) at resultEq
          cases schemaResult : CoreFile.schemaPageForEntries? entries count with
          | none => simp [schemaResult] at resultEq
          | some schema =>
            rw [schemaResult] at resultEq
            simp only [Option.bind_eq_bind, Option.bind, Option.some.injEq,
              Prod.mk.injEq] at resultEq
            rcases resultEq with ⟨imageEqual, stateEqual⟩
            subst builtImage
            rcases CoreFile.schemaPageForEntries_header schemaResult with
              ⟨body, header⟩
            refine ⟨count, schema, remaining, body, rfl, ?_, header⟩
            simp [CoreFile.Image.pageCount, count, Nat.add_comm]
        next => contradiction
      next => contradiction
    next => contradiction

/-- Whole-file left inverse for the high-fanout inline encoder. -/
theorem decode_encodeBulkInline (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CoreWidePageCodec.encodeBulkInline database = some image) :
    CoreDecode.decode image.fileBytes = some database.canonicalize := by
  rcases encodeBulkInline_header encoded with
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
  exact decodeFromPageSource_encodeBulkInline utf8 database image encoded

end CoreWidePageInverse

end SQLeanite
