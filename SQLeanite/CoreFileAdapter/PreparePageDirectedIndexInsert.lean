import SQLeanite.CoreFileAdapter.MutationPageWrites

namespace SQLeanite
namespace CoreFileAdapter

/-- Insert one row into the one tail-owned generated secondary index by
rewriting only its routed leaf.  This intentionally has no split case: a full
leaf returns `none` and retains the certified rebuild path.  A successful byte
mutation is not trusted by itself; `certifyDecodedIndex?` below proves that the
complete resulting physical index is exactly the logical post-state. -/
def preparePageDirectedIndexInsert? (validated : ValidatedOpenState)
    (input : ByteArray) (delta : CoreChunkPageDelta.StateDelta)
    (candidate : CoreChunkPageDelta.updateStateCandidate? delta.before
      delta.after.database = some delta) :
    Option (LocalizedLastIndexDelta delta) := do
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPageBytes
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noExistingFree : header.freelistPageCount.val = 0 then
      if _length : input.size = count * PhysicalCodec.pageSize then
        let source := byteArrayPageSource input count
        let firstPage ← source.readPage 1
        let catalog ← CoreDecode.decodeCatalogForOpen firstPage
        let before := delta.table.before.table
        let after := delta.table.after.table
        if _grew : before.rows.length < after.rows.length then
          if _oneRow : after.rows.length = before.rows.length + 1 then
            if _sameDatabase : validated.state.database.Equiv
                delta.before.database then
              if _sameSchema : before.schema = after.schema then
                if _sameIndexes : before.indexes = after.indexes then
                  match before.indexes with
                  | [index] => do
                      let row ← CoreChunkPageDelta.firstInserted
                        before.rows after.rows
                      let entry ← catalog.find? fun entry =>
                        entry.kind == "index" && entry.name == index.name &&
                          entry.table == after.schema.name
                      if _lastRoot : catalog.all fun candidate =>
                          candidate.rootPage ≤ entry.rootPage then
                        if _rootRange : 1 < entry.rootPage ∧
                            entry.rootPage ≤ count then
                          let mutated ← insertIndexRowIntoPages?
                            entry.rootPage index row source
                          let indexDelta ← mutationPageWrites? mutated
                          let tableBeforeResult ← exactOptionResult?
                            (CoreChunkPageDelta.beforeWrites delta.table)
                          let tableBefore := tableBeforeResult.value
                          let tableWritesResult ← exactOptionResult?
                            (CoreChunkPageDelta.writes delta.table)
                          let tableWrites := tableWritesResult.value
                          let expectedBefore := tableBefore ++ indexDelta.1
                          let writes := tableWrites ++ indexDelta.2
                          let certified ← certifyDecodedIndexAt? entry.rootPage
                            after index (CorePageSource.applyWrites source writes)
                          if _tableBeforeIndex :
                                delta.table.before.tree.root.pageIds.all
                                    (fun pageId => pageId < entry.rootPage) &&
                              delta.table.after.tree.root.pageIds.all
                                    (fun pageId => pageId < entry.rootPage) then
                            if writesBounded : ∀ write ∈ writes,
                                write.pageId < count then
                              if distinct : writes.Pairwise
                                  (fun left right => left.pageId ≠ right.pageId) then
                                if allocation : delta.after.AllocationWellFormed then
                                  let entryTable ← decideProof? (entry.table =
                                    delta.table.after.table.schema.name)
                                  let entryMetadata ← decideProof?
                                    (CoreDecode.decodeCanonicalIndex
                                      delta.table.after.table.schema
                                      delta.table.after.table.schema.name entry =
                                        some index)
                                  some {
                                    candidate
                                    state := delta.after
                                    index
                                    rootPage := entry.rootPage
                                    entry
                                    entryTable := entryTable.down
                                    entryRoot := rfl
                                    entryMetadata := entryMetadata.down
                                    tableExpectedBefore := tableBefore
                                    tableWrites
                                    tableExpectedBeforeEq := tableBeforeResult.exact
                                    tableWritesEq := tableWritesResult.exact
                                    certificate := .decoded certified.certificate
                                    expectedBefore
                                    writes
                                    storage := by
                                      let oldImage := byteArrayStorageImage input
                                        count _length
                                      refine ⟨oldImage,
                                        certified.sourceExact.trans ?_⟩
                                      dsimp only [source, oldImage]
                                      rw [byteArrayPageSource_eq_storageImage
                                        input count _length]
                                      apply CorePageSource.applyWrites_ofStorageImage
                                      intro write member
                                      simpa [oldImage, byteArrayStorageImage] using
                                        writesBounded write member
                                    writesDistinct := distinct
                                    allocation
                                    validated := ⟨delta.after, ()⟩ }
                                else none
                              else none
                            else none
                          else none
                        else none
                      else none
                  | _ => none
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

/-- Delete a set of rows from the one tail-owned generated secondary index by
descending only through pages that contain those entries. No index sort,
pagination, or whole-index encoding occurs. A promoted interior entry is
replaced by the greatest entry of its left subtree, so SQLite's promoted-key
semantics are preserved without duplication. Any overflow, page-fit, routing,
or allocation miss returns `none` and retains the certified rebuild path. -/
def preparePageDirectedIndexDelete? (validated : ValidatedOpenState)
    (input : ByteArray) (delta : CoreChunkPageDelta.StateDelta)
    (candidate : CoreChunkPageDelta.updateStateCandidate? delta.before
      delta.after.database = some delta) :
    Option (LocalizedLastIndexDelta delta) := do
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPageBytes
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noExistingFree : header.freelistPageCount.val = 0 then
      if _length : input.size = count * PhysicalCodec.pageSize then
        let source := byteArrayPageSource input count
        let firstPage ← source.readPage 1
        let catalog ← CoreDecode.decodeCatalogForOpen firstPage
        let before := delta.table.before.table
        let after := delta.table.after.table
        if _shrunk : after.rows.length < before.rows.length then
          if _sameDatabase : validated.state.database.Equiv
              delta.before.database then
            if _sameSchema : before.schema = after.schema then
              if _sameIndexes : before.indexes = after.indexes then
                match before.indexes with
                | [index] => do
                    let entry ← catalog.find? fun entry =>
                      entry.kind == "index" && entry.name == index.name &&
                        entry.table == after.schema.name
                    if _lastRoot : catalog.all fun candidate =>
                        candidate.rootPage ≤ entry.rootPage then
                      if _rootRange : 1 < entry.rootPage ∧ entry.rootPage ≤ count then
                        let removed ← deletedRows? before after
                        let mutated ← deleteIndexRowsFromPages?
                          entry.rootPage index removed source
                        let indexDelta ← mutationPageWrites? mutated
                        let tableBeforeResult ← exactOptionResult?
                          (CoreChunkPageDelta.beforeWrites delta.table)
                        let tableBefore := tableBeforeResult.value
                        let tableWritesResult ← exactOptionResult?
                          (CoreChunkPageDelta.writes delta.table)
                        let tableWrites := tableWritesResult.value
                        let expectedBefore := tableBefore ++ indexDelta.1
                        let writes := tableWrites ++ indexDelta.2
                        let certified ← certifyDecodedIndexAt? entry.rootPage
                          after index (CorePageSource.applyWrites source writes)
                        if _tableBeforeIndex :
                              delta.table.before.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) &&
                            delta.table.after.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) then
                          if writesBounded : ∀ write ∈ writes,
                              write.pageId < count then
                            if distinct : writes.Pairwise
                                (fun left right => left.pageId ≠ right.pageId) then
                              if allocation : delta.after.AllocationWellFormed then
                                let entryTable ← decideProof? (entry.table =
                                  delta.table.after.table.schema.name)
                                let entryMetadata ← decideProof?
                                  (CoreDecode.decodeCanonicalIndex
                                    delta.table.after.table.schema
                                    delta.table.after.table.schema.name entry =
                                      some index)
                                some {
                                  candidate
                                  state := delta.after
                                  index
                                  rootPage := entry.rootPage
                                  entry
                                  entryTable := entryTable.down
                                  entryRoot := rfl
                                  entryMetadata := entryMetadata.down
                                  tableExpectedBefore := tableBefore
                                  tableWrites
                                  tableExpectedBeforeEq := tableBeforeResult.exact
                                  tableWritesEq := tableWritesResult.exact
                                  certificate := .decoded certified.certificate
                                  expectedBefore
                                  writes
                                  storage := by
                                    let oldImage := byteArrayStorageImage input
                                      count _length
                                    refine ⟨oldImage,
                                      certified.sourceExact.trans ?_⟩
                                    dsimp only [source, oldImage]
                                    rw [byteArrayPageSource_eq_storageImage
                                      input count _length]
                                    apply CorePageSource.applyWrites_ofStorageImage
                                    intro write member
                                    simpa [oldImage, byteArrayStorageImage] using
                                      writesBounded write member
                                  writesDistinct := distinct
                                  allocation
                                  validated := ⟨delta.after, ()⟩ }
                              else none
                            else none
                          else none
                        else none
                      else none
                    else none
                | _ => none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

/-- Tail replacement is safe only when the old canonical index occupies
exactly that physical interval. A last catalog root can still have children
below it, notably after a wide-tree root split. Such layouts must be rebuilt. -/
def pageWriteContents (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    List (Nat × Array UInt8) := writes.map (fun write => (write.pageId, write.page.bytes))

def indexTailMatches (source : CoreDecode.PageSource) (rootPage : Nat)
    (pages : List CoreFile.Page) : Bool :=
  pages.length == source.pageCount + 1 - rootPage &&
    (readPageWrites? source rootPage pages.length).map pageWriteContents ==
      some (pageWriteContents (indexPageWrites rootPage pages))

theorem indexTailMatches_exact {source : CoreDecode.PageSource} {rootPage : Nat}
    {pages : List CoreFile.Page} (accepted : indexTailMatches source rootPage pages = true) :
    pages.length = source.pageCount + 1 - rootPage ∧
      (readPageWrites? source rootPage pages.length).map pageWriteContents =
        some (pageWriteContents (indexPageWrites rootPage pages)) := by
  simpa [indexTailMatches, Bool.and_eq_true] using accepted

/-- Localize one changed generated index when it owns the final file interval.
The validating-open capability records that the old index matched the logical
pre-state; the replacement is the ordinary proved index encoder rooted at the
same page. Every page after the shorter replacement becomes freelist space.
General files, multiple changed indexes, non-tail ownership, or replacement
indexes that exceed the old tail return `none` and keep the full compatibility
commit. -/
def prepareLocalizedLastIndex? (validated : ValidatedOpenState)
    (input : List UInt8)
    (delta : CoreChunkPageDelta.StateDelta)
    (candidate : CoreChunkPageDelta.updateStateCandidate? delta.before
      delta.after.database = some delta) :
    Option (LocalizedLastIndexDelta delta) := do
  let (header, _) ← FileFormat.decodeDatabaseHeader input
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noExistingFree : header.freelistPageCount.val = 0 then
      if _length : input.length = count * PhysicalCodec.pageSize then
        let inputBytes := ByteArray.mk input.toArray
        have inputBytesSize : inputBytes.size =
            count * PhysicalCodec.pageSize := by
          simpa only [inputBytes, ByteArray.size, List.size_toArray] using _length
        let source := byteArrayPageSource inputBytes count
        let firstPage ← source.readPage 1
        let catalog ← CoreDecode.decodeCatalogForOpen firstPage
        let before := delta.table.before.table
        let after := delta.table.after.table
        if _sameDatabase : validated.state.database.Equiv
            delta.before.database then
          if _sameSchema : before.schema = after.schema then
            if _sameIndexes : before.indexes = after.indexes then
              -- Every index entry carries the rowid, so insertion/deletion
              -- necessarily changes every index. Avoid constructing two full
              -- source images merely to rediscover the cardinality change.
              let changed :=
                if before.rows.length == after.rows.length then
                  before.indexes.filter fun index =>
                    before.rows.map
                        (CoreChunkPageDelta.indexEntryOfRow index) !=
                      after.rows.map
                        (CoreChunkPageDelta.indexEntryOfRow index)
                else before.indexes
              match changed with
              | [index] => do
                  let entry ← catalog.find? fun entry =>
                    entry.kind == "index" &&
                      entry.name == index.name &&
                      entry.table == after.schema.name
                  if _lastRoot : catalog.all fun candidate =>
                      candidate.rootPage ≤ entry.rootPage then
                    if _rootRange : 1 < entry.rootPage ∧ entry.rootPage ≤ count then
                      let prior ← certifyIndexEncoding? entry.rootPage before index
                      unless indexTailMatches source entry.rootPage prior.value.pages do none
                      let certified ← certifyIndexEncoding?
                          entry.rootPage after index
                      let encoding := certified.value
                      let oldCount := count + 1 - entry.rootPage
                      if _fits : 0 < encoding.pages.length ∧
                            encoding.pages.length ≤ oldCount then
                        if _tableBeforeIndex :
                              delta.table.before.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) &&
                                delta.table.after.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) then
                          let tableBeforeResult ← exactOptionResult?
                            (CoreChunkPageDelta.beforeWrites delta.table)
                          let tableBefore := tableBeforeResult.value
                          let tableWritesResult ← exactOptionResult?
                            (CoreChunkPageDelta.writes delta.table)
                          let tableWrites := tableWritesResult.value
                          if tableWritesBounded : ∀ write ∈ tableWrites,
                              write.pageId + 1 < entry.rootPage then
                            let oldTailRun ← readPageWritesCertified? source
                              entry.rootPage oldCount
                            let oldTail := oldTailRun.writes
                            let indexWrites := changedPageWrites oldTail
                                (indexPageWrites entry.rootPage encoding.pages)
                            let writes := tableWrites ++ indexWrites
                            let expectedBefore := tableBefore ++ oldTail
                            let released := List.range'
                                (entry.rootPage + encoding.pages.length)
                                (oldCount - encoding.pages.length)
                            let freePages := CoreChunkPageDelta.addFreePages
                                delta.after.freePages released
                            let state := { delta.after with freePages }
                            if decodeBound : entry.rootPage +
                                encoding.pages.length < 2 ^ 32 then
                              if distinct : writes.Pairwise
                                  (fun left right => left.pageId ≠ right.pageId) then
                                if allocation : state.AllocationWellFormed then
                                  let entryTable ← decideProof? (entry.table =
                                    delta.table.after.table.schema.name)
                                  let entryMetadata ← decideProof?
                                    (CoreDecode.decodeCanonicalIndex
                                      delta.table.after.table.schema
                                      delta.table.after.table.schema.name entry =
                                        some index)
                                  some {
                                  candidate
                                  state
                                  index
                                  rootPage := entry.rootPage
                                  entry
                                  entryTable := entryTable.down
                                  entryRoot := rfl
                                  entryMetadata := entryMetadata.down
                                  tableExpectedBefore := tableBefore
                                  tableWrites
                                  tableExpectedBeforeEq := tableBeforeResult.exact
                                  tableWritesEq := tableWritesResult.exact
                                  certificate := .encoded certified
                                  expectedBefore
                                  writes
                                  storage := by
                                    let oldImage := byteArrayStorageImage inputBytes
                                      count inputBytesSize
                                    refine ⟨oldImage, ?_, by omega, decodeBound, ?_⟩
                                    · apply CoreLocalizedRepresentation.readsPagesFrom_applyWrites
                                        oldImage writes distinct entry.rootPage
                                        encoding.pages
                                      intro offset inBounds
                                      rcases indexPageWrites_covers entry.rootPage
                                          encoding.pages (by omega) offset inBounds with
                                        ⟨candidate, candidateMember, candidatePage,
                                          candidateBytes⟩
                                      by_cases changed : candidate ∈ indexWrites
                                      · exact .inl ⟨candidate, by simp [writes, changed],
                                          candidatePage, candidateBytes⟩
                                      · rcases omitted_changedPageWrites_matches
                                            candidateMember changed with
                                          ⟨old, oldMember, oldSameId, oldSamePage⟩
                                        refine .inr ⟨by omega, ?_, ?_, ?_⟩
                                        · change entry.rootPage + offset ≤ count
                                          omega
                                        · have oldRead := readPageWrites?_reads source
                                              (by omega) oldTailRun.exact old oldMember
                                          have sourceRead : source.readPage
                                              (entry.rootPage + offset) =
                                                some (encoding.pages.get
                                                  ⟨offset, inBounds⟩).bytes := by
                                            rw [← candidatePage, ← oldSameId, oldRead,
                                              oldSamePage, candidateBytes]
                                          rw [← byteArrayPageSource_eq_storageImage
                                            inputBytes count inputBytesSize]
                                          exact sourceRead
                                        · intro write writeMember samePage
                                          rcases List.mem_append.mp writeMember with
                                            tableMember | indexMember
                                          · have beforeRoot := tableWritesBounded write
                                                tableMember
                                            omega
                                          · have fullMember : write ∈
                                                indexPageWrites entry.rootPage
                                                  encoding.pages :=
                                              (changedPageWrites_sublist oldTail
                                                (indexPageWrites entry.rootPage
                                                  encoding.pages)).subset indexMember
                                            have sameId : write.pageId =
                                                candidate.pageId := by omega
                                            have equal := indexPageWrites_eq_of_pageId_eq
                                              entry.rootPage encoding.pages
                                                (by omega) fullMember
                                                candidateMember sameId
                                            exact changed (by simpa [equal] using indexMember)
                                    · have growth :=
                                          CorePageSource.applyWrites_pageCount_ge
                                            oldImage writes
                                      have oldCountExact : oldImage.pageCount = count := rfl
                                      rw [oldCountExact] at growth
                                      change entry.rootPage + encoding.pages.length ≤
                                        (GrowableStorage.applyWrites oldImage writes).pageCount + 1
                                      omega
                                  writesDistinct := distinct
                                  allocation
                                  validated := ⟨state, ()⟩ }
                                else none
                              else none
                            else none
                          else none
                        else none
                      else none
                    else none
                  else none
              | _ => none
            else none
          else none
        else none
      else none
    else none
  else none

structure IndexLookup where
  candidates : List Core.Row
  pagesRead : Nat

structure PrimaryLookup where
  schema : Core.Schema
  row : Core.Row
  pagesRead : Nat

inductive PrimaryLookupOutcome where
  | found (row : Core.Row)
  | generatedMissing

/-- A page-directed lookup which preserves the distinction between a decoded
row and a complete miss in a stamped Lean-generated image.  Malformed bytes
and misses in general SQLite files remain `none`. -/
structure PrimaryLookupDecision where
  schema : Core.Schema
  outcome : PrimaryLookupOutcome
  pagesRead : Nat

end CoreFileAdapter

end SQLeanite
