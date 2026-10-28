import SQLeanite.CoreLocalizedRepresentation.IndexGroupCertificatesEncodeIndexTableGroups

namespace SQLeanite
namespace CoreLocalizedRepresentation

/-- The canonical bulk encoder establishes the complete physical state
invariant over any source which contains its emitted tail and reads its schema
page.  Unlike `PageSourceRepresents`, the result retains table-page ownership,
overflow intervals, and the exact promoted index groups needed by subsequent
localized-write proofs. -/
theorem exists_databaseOnSource_encodeBulk_in
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image)
    (source : CoreDecode.PageSource)
    (catalogRead :
      source.readPage 1 >>= CoreDecode.decodeCatalogForOpen =
        (CoreDecode.PageSource.ofList
          (image.pages.map CoreFile.Page.bytes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen)
    (activeTailReads : CoreDecode.ReadsPagesFrom source 2 image.pages.tail)
    (enoughPages : image.pageCount ≤ source.pageCount) :
    ∃ state : CoreChunkPageState.State,
      CoreChunkPageState.State.build? database = some state ∧
      DatabaseOnSource source state := by
  obtain ⟨baseState, baseBuilt, baseTables⟩ :=
    exists_tablesOnSource_encodeBulk_in database image encoded source
      activeTailReads enoughPages
  unfold CorePageCodec.encodeBulk CorePageCodec.encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
    simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
    have stateEq : baseState = state := by
      rw [stateResult] at baseBuilt
      exact (Option.some.inj baseBuilt).symm
    subst baseState
    cases tableResult : CorePageCodec.encodeChunkTablesWithOverflow
        state.nextPage state.tables with
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
          let tableEntries := state.tables.map
            CorePageCodec.chunkTableCatalogEntry
          let indexEntries := CoreOverflow.indexEntriesOf indexEncodings
          let entries := tableEntries ++ indexEntries
          let treePages := tableEncoding.treePages.map
            CorePageCodec.NumberedPage.page
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
          | none => simp [schemaResult] at encoded
          | some schemaPage =>
            rw [schemaResult] at encoded
            simp only [Option.bind_eq_bind, Option.bind,
              Option.some.injEq] at encoded
            subst image
            obtain ⟨tablePageCount, stateNext, statePages⟩ :=
              CoreChunkPageState.State.build?_interval stateResult
            have treeNumbers :=
              CorePageCodec.encodeChunkTablesWithOverflow_pageNumbers
                state.nextPage state.tables tableEncoding tableResult
            rw [statePages] at treeNumbers
            have treeLength : treePages.length = tablePageCount := by
              have lengths := congrArg List.length treeNumbers
              simpa [treePages] using lengths
            have tableNext :=
              CorePageCodec.encodeChunkTablesWithOverflow_nextPage
                state.nextPage state.tables tableEncoding tableResult
            have sourceCountLower :
                1 + remaining.length ≤ source.pageCount := by
              simpa [CoreFile.Image.pageCount, Nat.add_comm] using enoughPages
            have remainingReads : CoreDecode.ReadsPagesFrom source 2
                remaining := by
              simpa using activeTailReads
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
            have endBound : tableEncoding.nextPage + indexPages.length =
                remaining.length + 2 := by
              simp only [remaining, List.length_append]
              rw [tableNext, stateNext, treeLength]
              omega
            have indexPositive : ∀ encoding ∈ indexEncodings,
                0 < encoding.rootPage := by
              intro encoding member
              have range := indexRange encoding member
              rw [tableNext, stateNext] at range
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
            have indexCertificates :=
              indexGroupCertificates_encodeIndexTableGroups source
                tableEncoding.nextPage database.tables indexEncodings
                database.tablesWellFormed indexResult individualIndexReads
                indexPositive indexPageBound indexSourceBound
            have safe : ∀ entry ∈ entries,
                CoreDecode.CatalogTextRoundtrips entry := by
              intro entry _
              exact ⟨utf8 entry.kind, utf8 entry.name,
                utf8 entry.table, utf8 entry.sql⟩
            have catalogDecoded :=
              CoreDecode.decodeCatalogForOpen_schemaPageForEntries
                entries count safe schemaResult
            have canonicalFirstRead :
                (CoreDecode.PageSource.ofList
                  ((schemaPage :: remaining).map CoreFile.Page.bytes)).readPage
                    1 = some schemaPage.bytes := by
              simp [CoreDecode.PageSource.ofList, CoreDecode.page?]
            have expectedCatalogRead :
                source.readPage 1 >>= CoreDecode.decodeCatalogForOpen =
                  some (entries.map CoreDecode.CatalogEntry.ofEncoded) := by
              rw [catalogRead, canonicalFirstRead]
              simp only [Option.bind_eq_bind, Option.bind]
              exact catalogDecoded
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
                rcases List.mem_map.mp member with
                  ⟨encodedEntry, encodedMember, rfl⟩
                rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
                rfl
              have indexesRemoved :
                  (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "table") = [] := by
                apply List.filter_eq_nil_iff.mpr
                intro entry member
                rcases List.mem_map.mp member with
                  ⟨encodedEntry, encodedMember, rfl⟩
                rcases List.mem_map.mp encodedMember with
                  ⟨encoding, _, rfl⟩
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
                rcases List.mem_map.mp member with
                  ⟨encodedEntry, encodedMember, rfl⟩
                rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
                simp [CorePageCodec.chunkTableCatalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded]
              have indexesKept :
                  (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "index") =
                      indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                apply List.filter_eq_self.mpr
                intro entry member
                rcases List.mem_map.mp member with
                  ⟨encodedEntry, encodedMember, rfl⟩
                rcases List.mem_map.mp encodedMember with
                  ⟨encoding, _, rfl⟩
                rfl
              rw [tablesRemoved, indexesKept, List.nil_append]
            have stateDatabase :=
              (CoreChunkPageState.State.build?_represents stateResult).1
            refine ⟨state, rfl, ⟨?_⟩⟩
            refine ⟨entries.map CoreDecode.CatalogEntry.ofEncoded,
              tableEntries.map CoreDecode.CatalogEntry.ofEncoded,
              indexEntries.map CoreDecode.CatalogEntry.ofEncoded,
              expectedCatalogRead, tableFilter, indexFilter, ?_, ?_, ?_, ?_⟩
            · simpa [tableEntries, Function.comp_def] using baseTables
            · rw [stateDatabase]
              simpa [indexEntries, CoreOverflow.indexEntriesOf,
                List.map_map, Function.comp_def] using indexCertificates.2.2
            · rw [stateDatabase]
              simpa [indexEntries, CoreOverflow.indexEntriesOf,
                List.map_map, Function.comp_def] using indexCertificates.2.1
            · unfold TablePagesBeforeIndexRoots
              intro pageId pageMember entry entryMember
              rw [statePages] at pageMember
              simp only [List.mem_range'_1] at pageMember
              rcases List.mem_map.mp entryMember with
                ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp (by
                simpa [indexEntries, CoreOverflow.indexEntriesOf] using
                  encodedMember) with ⟨encoding, encodingMember, rfl⟩
              have range := indexRange encoding encodingMember
              rw [tableNext, stateNext] at range
              change pageId < encoding.rootPage
              omega
        next => contradiction

/-- Every encoded page covered by one member of a distinct write set is
present in the page source obtained after applying that write set. -/
theorem pageSourceContains_applyWrites_of_covered
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pages : List CorePageCodec.NumberedPage)
    (covered : ∀ numbered ∈ pages,
      ∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) pages := by
  intro numbered member
  rcases covered numbered member with
    ⟨write, writeMember, pageNumber, bytes⟩
  rw [← pageNumber]
  rw [CorePageSource.readPage_applyWrites_of_mem image distinct writeMember]
  exact congrArg some bytes

/-- A contiguous encoded page run is readable from the post-write source when
every byte page in the run is supplied by its exact numbered write.  This is
the physical bridge used by rebuilt index and overflow runs. -/
theorem readsPagesFrom_applyWrites_of_covered
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (start : Nat) (pages : List CoreFile.Page)
    (covered : ∀ (offset : Nat) (inBounds : offset < pages.length),
      ∃ write ∈ writes,
        write.pageId + 1 = start + offset ∧
        write.page.bytes.toList =
          (pages.get ⟨offset, inBounds⟩).bytes) :
    CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) start pages := by
  intro offset inBounds
  rcases covered offset inBounds with
    ⟨write, writeMember, pageNumber, bytes⟩
  rw [← pageNumber]
  rw [CorePageSource.readPage_applyWrites_of_mem image distinct writeMember]
  exact congrArg some bytes

/-- A contiguous encoded run may mix freshly written pages with exact old
pages omitted from the delta.  This is the index/overflow analogue of
`pageSourceContains_applyWrites`. -/
theorem readsPagesFrom_applyWrites
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (start : Nat) (pages : List CoreFile.Page)
    (accounted : ∀ (offset : Nat) (inBounds : offset < pages.length),
      (∃ write ∈ writes,
        write.pageId + 1 = start + offset ∧
        write.page.bytes.toList =
          (pages.get ⟨offset, inBounds⟩).bytes) ∨
      (0 < start + offset ∧ start + offset ≤ image.pageCount ∧
        (CorePageSource.ofStorageImage image).readPage (start + offset) =
          some (pages.get ⟨offset, inBounds⟩).bytes ∧
        ∀ write ∈ writes, write.pageId + 1 ≠ start + offset)) :
    CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) start pages := by
  intro offset inBounds
  rcases accounted offset inBounds with written | unchanged
  · rcases written with ⟨write, member, pageNumber, bytes⟩
    rw [← pageNumber]
    rw [CorePageSource.readPage_applyWrites_of_mem image distinct member]
    exact congrArg some bytes
  · let pageId := start + offset - 1
    have pageNumber : pageId + 1 = start + offset := by
      simp only [pageId]
      omega
    have oldBound : pageId < image.pageCount := by
      simp only [pageId]
      omega
    have newBound :
        pageId < (GrowableStorage.applyWrites image writes).pageCount := by
      have growth := CorePageSource.applyWrites_pageCount_ge image writes
      omega
    rw [← pageNumber]
    rw [CorePageSource.readPage_applyWrites_of_not_written image writes pageId
      newBound oldBound]
    · simpa [pageNumber] using unchanged.2.2.1
    · intro write member equal
      exact unchanged.2.2.2 write member (by omega)

/-- Writes strictly below an owned index root cannot alter any page in that
index's contiguous tree/overflow run.  The old exact bytes therefore transport
to the actual post-write storage image without decoding the index again. -/
def IndexOnSource.applyWritesBelow
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {table : Core.Table} {entry : CoreDecode.CatalogEntry}
    {index : Core.Index}
    (owned : IndexOnSource (CorePageSource.ofStorageImage image)
      table entry index)
    (below : ∀ write ∈ writes, write.pageId + 1 < entry.rootPage) :
    IndexOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) table entry index := by
  rcases owned with ⟨reference, encoding, sameTable, sameRoot, metadata,
    member, encoded, reads, rootPositive, pageBound, withinSource, logical⟩
  refine ⟨reference, encoding, sameTable, sameRoot, metadata, member, encoded,
    ?_, rootPositive, pageBound, ?_, logical⟩
  · apply readsPagesFrom_applyWrites image writes distinct
      encoding.rootPage encoding.pages
    intro offset inBounds
    refine .inr ⟨by omega, by
      simp only [CorePageSource.ofStorageImage_pageCount] at withinSource
      omega, reads offset inBounds, ?_⟩
    intro write member equal
    have strictlyBelow := below write member
    rw [sameRoot] at strictlyBelow
    omega
  · simp only [CorePageSource.ofStorageImage_pageCount]
    have growth := CorePageSource.applyWrites_pageCount_ge image writes
    simp only [CorePageSource.ofStorageImage_pageCount] at withinSource
    omega

def IndexesOnSource.applyWritesBelow
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {table : Core.Table} {entries : List CoreDecode.CatalogEntry}
    (owned : IndexesOnSource (CorePageSource.ofStorageImage image)
      table entries)
    (below : ∀ entry ∈ entries, ∀ write ∈ writes,
      write.pageId + 1 < entry.rootPage) :
    IndexesOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) table entries := by
  induction owned with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (head.applyWritesBelow image writes distinct
          (below _ (by simp)))
        (induction (fun entry member => below entry (by simp [member])))

def IndexGroupsOnSource.applyWritesBelow
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {tables : List Core.Table} {entries : List CoreDecode.CatalogEntry}
    (owned : IndexGroupsOnSource (CorePageSource.ofStorageImage image)
      tables entries)
    (below : ∀ entry ∈ entries, ∀ write ∈ writes,
      write.pageId + 1 < entry.rootPage) :
    IndexGroupsOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) tables entries := by
  induction owned with
  | nil => exact .nil
  | cons current boundary tail induction =>
      exact .cons
        (current.applyWritesBelow image writes distinct
          (fun entry member => below entry (by simp [member])))
        boundary
        (induction (fun entry member => below entry (by simp [member])))

end CoreLocalizedRepresentation

end SQLeanite
