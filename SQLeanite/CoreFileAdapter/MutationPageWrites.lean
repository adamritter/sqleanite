import SQLeanite.CoreFileAdapter.IOIndexPageMutationsPageSource
import SQLeanite.CoreLocalizedRepresentation.ExistsDatabaseOnSourceEncodeBulkIn
import SQLeanite.CoreWidePageDelta

namespace SQLeanite
namespace CoreFileAdapter

def mutationPageWrites? (mutated : IndexPageMutations) :
    Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize) ×
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) := do
  let pairs ← mutated.changed.mapM fun changed => do
      let pageNumber := changed.1
      let oldBytes ← mutated.source.readPage pageNumber
      let newBytes := changed.2
      let oldPage ← storagePage? oldBytes
      let newPage ← storagePage? newBytes
      some ((⟨pageNumber - 1, oldPage⟩ :
        GrowableStorage.PageWrite PhysicalCodec.pageSize),
        (⟨pageNumber - 1, newPage⟩ :
          GrowableStorage.PageWrite PhysicalCodec.pageSize))
  some (pairs.map (fun pair => pair.1), pairs.map (fun pair => pair.2))

def mutationPageWritesIO? (mutated : IOIndexPageMutations) :
    IO (Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize) ×
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))) := do
  let mut oldWrites := []
  let mut newWrites := []
  for changed in mutated.changed do
    let pageNumber := changed.1
    let newBytes := changed.2
    let some newPage := storagePage? newBytes | return none
    if pageNumber ≤ mutated.source.pageCount then
      let some oldBytes ← mutated.source.readPage pageNumber | return none
      let some oldPage := storagePage? oldBytes | return none
      oldWrites := (⟨pageNumber - 1, oldPage⟩ :
        GrowableStorage.PageWrite PhysicalCodec.pageSize) :: oldWrites
    newWrites := (⟨pageNumber - 1, newPage⟩ :
      GrowableStorage.PageWrite PhysicalCodec.pageSize) :: newWrites
  return some (oldWrites.reverse, newWrites.reverse)

private def currentWritesFor? (source : CoreDecode.PageSource) (count : Nat) :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize) →
      Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
  | [] => some []
  | write :: writes => do
      let tail ← currentWritesFor? source count writes
      if write.pageId < count then
        let bytes ← source.readPage (write.pageId + 1)
        let page ← storagePage? bytes
        some (⟨write.pageId, page⟩ :: tail)
      else some tail

private def currentWritesForIO? (source : CoreDecode.IOPageSource)
    (count : Nat) : List (GrowableStorage.PageWrite PhysicalCodec.pageSize) →
      IO (Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)))
  | [] => pure (some [])
  | write :: writes => do
      let some tail ← currentWritesForIO? source count writes | return none
      if write.pageId < count then
        let some bytes ← source.readPage (write.pageId + 1) | return none
        let some page := storagePage? bytes | return none
        return some (⟨write.pageId, page⟩ :: tail)
      else return some tail

structure PreparedWideAppend {state : CoreWidePageState.State}
    {snapshot : Option Core.Database} {tableName : String}
    {values : List Core.Value}
    (executed : CoreWidePageDelta.ExecutedInsert state snapshot tableName values) where
  state : CoreWidePageState.State
  textState : state.SingleIndexValuesText
  expectedBefore : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  index : Core.Index
  rootPage : Nat
  logicalIndexExact : CoreDecode.expectedIndexEntries
      executed.append.mutation.after.table index =
    CoreChunkPageDelta.insertIndexEntry
      (CoreChunkPageDelta.indexEntryOfRow index executed.row)
      (CoreDecode.expectedIndexEntries executed.append.table.table index)
  writesDistinct : writes.Pairwise (fun left right => left.pageId ≠ right.pageId)

/-- Prepare the live one-row wide append.  Table pages come only from the
changed right spine; the generated TEXT-primary index follows one routed path.
Any page-fit or index-split miss returns `none` to the proved bulk fallback. -/
def prepareWideAppend? {state : CoreWidePageState.State}
    {snapshot : Option Core.Database} {tableName : String}
    {values : List Core.Value}
    (input : ByteArray)
    (executed : CoreWidePageDelta.ExecutedInsert state snapshot tableName values) :
    Option (PreparedWideAppend executed) := do
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPageBytes
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noFree : header.freelistPageCount.val = 0 then
      if _length : input.size = count * PhysicalCodec.pageSize then
        let source := byteArrayPageSource input count
        let firstPage ← source.readPage 1
        let catalog ← CoreDecode.decodeCatalogForOpen firstPage
        let before := executed.append.table
        let after := executed.append.mutation.after
        if _sameSchema : before.table.schema = after.table.schema then
          if _sameIndexes : before.table.indexes = after.table.indexes then
            match afterIndexes : after.table.indexes with
            | [index] => do
                if beforeText : CoreFile.indexValuesText before.table index = true then
                  match rowValue : executed.row.value index.column with
                  | .text _ => do
                      let entry ← catalog.find? fun entry =>
                        entry.kind == "index" && entry.name == index.name &&
                          entry.table == after.table.schema.name
                      if _rootRange :
                          1 < entry.rootPage ∧ entry.rootPage ≤ count then
                        let tablePages ←
                          match executed.append.mutation.mode with
                          | .extendedTerminalChunk =>
                              CoreWidePageCodec.encodeTerminalReplacement
                                after.table.schema after.tree
                          | .appendedChunk =>
                              CoreWidePageCodec.encodeTerminalAppend
                                after.table.schema before.tree after.tree
                        let tableWrites ← tablePages.mapM
                          CoreChunkPageDelta.numberedWrite?
                        let tableBefore ← currentWritesFor? source count tableWrites
                        let mutated ← insertIndexRowIntoPages? entry.rootPage index
                          executed.row source
                        let indexDelta ← mutationPageWrites? mutated
                        let expectedBefore := tableBefore ++ indexDelta.1
                        let writes := tableWrites ++ indexDelta.2
                        if distinct : writes.Pairwise
                            (fun left right => left.pageId ≠ right.pageId) then
                          have rowsEq : after.table.rows =
                              before.table.rows ++ [executed.row] := by
                            rw [← after.represents,
                              executed.append.mutation.logicalRows]
                          have logicalIndexExact :=
                            CoreChunkPageDelta.expectedIndexEntries_append_text
                              before.table after.table index executed.row rowsEq
                              beforeText rowValue
                          have afterText :=
                            CoreChunkPageDelta.indexValuesText_append_text
                              before.table after.table index executed.row rowsEq
                              beforeText rowValue
                          have textState :
                              executed.append.after.SingleIndexValuesText :=
                            CoreWidePageState.State.singleIndexValuesText_of_exact
                              executed.append.after_tables afterIndexes afterText
                          some {
                            state := executed.append.after
                            textState
                            expectedBefore
                            writes
                            index
                            rootPage := entry.rootPage
                            logicalIndexExact
                            writesDistinct := distinct }
                        else none
                      else none
                  | _ => none
                else none
            | _ => none
          else none
        else none
      else none
    else none
  else none

/-- File-backed preparation for the same proof-carrying append.  Only the
catalog page, the changed table spine, and one routed index path are read.  In
particular this function performs no `readBinFile`, so an autocommit insert is
independent of the total database byte size when no split is required. -/
def prepareWideAppendIO? {state : CoreWidePageState.State}
    {snapshot : Option Core.Database} {tableName : String}
    {values : List Core.Value}
    (path : System.FilePath)
    (executed : CoreWidePageDelta.ExecutedInsert state snapshot tableName values)
    (stateText : state.SingleIndexValuesText) :
    IO (Option (PreparedWideAppend executed)) := do
  let firstBytes ← SyscallVFS.preadBytes path.toString 0
    (USize.ofNat PhysicalCodec.pageSize)
  unless firstBytes.size = PhysicalCodec.pageSize do return none
  let firstPage := firstBytes.toList
  let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
    return none
  let count := header.databaseSizePages.val
  let metadata ← path.metadata
  unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
      metadata.byteSize.toNat = count * PhysicalCodec.pageSize do return none
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noFree : header.freelistPageCount.val = 0 then
      -- The index mutator decodes each routed page and the write preparation
      -- subsequently asks for that page's old pre-image.  Retain the handful
      -- of pages touched by this one statement so the latter request neither
      -- issues another syscall nor converts the same 4 KiB array to a list a
      -- second time.  Page one is already in hand for the header.
      let base := preadPageSource path count
      let cache ← IO.mkRef [(1, firstPage)]
      let source : CoreDecode.IOPageSource := {
        usable := base.usable
        pageCount := base.pageCount
        readPage := fun pageNumber => do
          let retained ← cache.get
          match retained.find? (fun entry => entry.1 == pageNumber) with
          | some entry => return some entry.2
          | none =>
              let read ← base.readPage pageNumber
              match read with
              | some bytes =>
                  cache.modify ((pageNumber, bytes) :: ·)
                  return some bytes
              | none => return none }
      let some catalog := CoreDecode.decodeCatalogForOpen firstPage | return none
      let before := executed.append.table
      let after := executed.append.mutation.after
      if _sameSchema : before.table.schema = after.table.schema then
        if _sameIndexes : before.table.indexes = after.table.indexes then
          match afterIndexes : after.table.indexes with
          | [index] =>
              have beforeIndexes : before.table.indexes = [index] := by
                rw [_sameIndexes]
                exact afterIndexes
              have beforeText :=
                CoreWidePageState.State.singleIndexValuesText_exact stateText
                  executed.append.before_eq beforeIndexes
              match rowValue : executed.row.value index.column with
              | .text _ => do
                  let some entry := catalog.find? fun entry =>
                    entry.kind == "index" && entry.name == index.name &&
                      entry.table == after.table.schema.name | return none
                  if _rootRange :
                      1 < entry.rootPage ∧ entry.rootPage ≤ count then
                    let some tablePages :=
                      (match executed.append.mutation.mode with
                      | .extendedTerminalChunk =>
                          CoreWidePageCodec.encodeTerminalReplacement
                            after.table.schema after.tree
                      | .appendedChunk =>
                          CoreWidePageCodec.encodeTerminalAppend
                            after.table.schema before.tree after.tree) |
                      return none
                    let some tableWrites := tablePages.mapM
                      CoreChunkPageDelta.numberedWrite? | return none
                    let some tableBefore ←
                      currentWritesForIO? source count tableWrites | return none
                    let indexNextPage := targetPageCount count tableWrites + 1
                    let some mutated ← insertIndexRowIntoPagesIO?
                      entry.rootPage index executed.row source indexNextPage |
                        return none
                    let some indexDelta ← mutationPageWritesIO? mutated |
                      return none
                    let expectedBefore := tableBefore ++ indexDelta.1
                    let writes := tableWrites ++ indexDelta.2
                    if distinct : writes.Pairwise
                        (fun left right => left.pageId ≠ right.pageId) then
                      have rowsEq : after.table.rows =
                          before.table.rows ++ [executed.row] := by
                        rw [← after.represents,
                          executed.append.mutation.logicalRows]
                      have logicalIndexExact :=
                        CoreChunkPageDelta.expectedIndexEntries_append_text
                          before.table after.table index executed.row rowsEq
                          beforeText rowValue
                      have afterText :=
                        CoreChunkPageDelta.indexValuesText_append_text
                          before.table after.table index executed.row rowsEq
                          beforeText rowValue
                      let nextState := executed.append.after.reserveThrough
                        mutated.nextPage
                      have nextTables : nextState.tables =
                          [executed.append.mutation.after.withNextPage
                            mutated.nextPage] := by
                        simp [nextState, CoreWidePageState.State.reserveThrough,
                          executed.append.after_tables]
                      have nextIndexes :
                          (executed.append.mutation.after.withNextPage
                            mutated.nextPage).table.indexes = [index] := by
                        exact afterIndexes
                      have textState : nextState.SingleIndexValuesText :=
                        CoreWidePageState.State.singleIndexValuesText_of_exact
                          nextTables nextIndexes afterText
                      return some {
                        state := nextState
                        textState
                        expectedBefore
                        writes
                        index
                        rootPage := entry.rootPage
                        logicalIndexExact
                        writesDistinct := distinct }
                    else return none
                  else return none
              | _ => return none
          | _ => return none
        else return none
      else return none
    else return none
  else return none

def physicalCatalogEntry? (entry : CoreDecode.CatalogEntry) :
    Option CoreFile.CatalogEntry := do
  let sql ← entry.sql
  some {
    kind := entry.kind
    name := entry.name
    table := entry.table
    rootPage := entry.rootPage
    sql }

/-- Append a newly-created secondary index without re-encoding any table.
The old catalog comes from the validating open; the added index is the ordinary
proved encoder rooted immediately after the current file. -/
def prepareAppendedIndex? (validated : ValidatedOpenState)
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
        if _sameDatabase : validated.state.database.Equiv delta.before.database then
          let before := delta.table.before.table
          let after := delta.table.after.table
          if _sameSchema : before.schema = after.schema then
            if _sameRows : before.rows = after.rows then
              match afterIndexes : after.indexes with
              | index :: previous =>
                  if _oneAdded : previous = before.indexes then
                    let tableBeforeResult ← exactOptionResult?
                      (CoreChunkPageDelta.beforeWrites delta.table)
                    let tableBefore := tableBeforeResult.value
                    let tableWritesResult ← exactOptionResult?
                      (CoreChunkPageDelta.writes delta.table)
                    let tableWrites := tableWritesResult.value
                    let source := byteArrayPageSource input count
                    let firstPage ← source.readPage 1
                    let catalog ← CoreDecode.decodeCatalogForOpen firstPage
                    let entries ← catalog.mapM physicalCatalogEntry?
                    let rootPage := count + 1
                    let certified ← certifyIndexEncoding? rootPage after index
                    let encoding := certified.value
                    let newCount := count + encoding.pages.length
                    if _nonempty : 0 < encoding.pages.length then
                      if countBound : newCount < 2 ^ 32 then
                        let pageCount : FileFormat.U32Value :=
                          ⟨newCount, countBound⟩
                        let schemaPage ← CoreFile.schemaPageForEntries?
                          (entries ++ [encoding.catalogEntry]) pageCount
                        let oldPage ← storagePage? firstPageBytes
                        let indexWrites :=
                          (⟨0, schemaPage.storage⟩ :
                            GrowableStorage.PageWrite PhysicalCodec.pageSize) ::
                          indexPageWrites rootPage encoding.pages
                        let writes := tableWrites ++ indexWrites
                        let expectedBefore := tableBefore ++ [⟨0, oldPage⟩]
                        let state := { delta.after with
                          nextPage := newCount + 1 }
                        if distinct : writes.Pairwise
                            (fun left right => left.pageId ≠ right.pageId) then
                          if allocation : state.AllocationWellFormed then
                            if decodeBound :
                                rootPage + encoding.pages.length < 2 ^ 32 then
                              some {
                                candidate
                                state
                                index
                                rootPage
                                entry := CoreDecode.CatalogEntry.ofEncoded
                                  encoding.catalogEntry
                                entryTable := by
                                  have identity := CoreOverflow.encodeIndex_identity
                                    certified.encoded
                                  change encoding.table.schema.name =
                                    after.schema.name
                                  dsimp only [encoding]
                                  rw [identity.1]
                                entryRoot := by
                                  have identity := CoreOverflow.encodeIndex_identity
                                    certified.encoded
                                  change encoding.rootPage = rootPage
                                  dsimp only [encoding]
                                  exact identity.2.2
                                entryMetadata := by
                                  have member : index ∈ after.indexes := by
                                    rw [afterIndexes]
                                    simp
                                  have decoded := CoreDecode.decodeCanonicalIndex_encoded
                                    after index member rootPage
                                  have identity := CoreOverflow.encodeIndex_identity
                                    certified.encoded
                                  have tableEq : encoding.table = after := by
                                    simpa only [encoding] using identity.1
                                  have indexEq : encoding.index = index := by
                                    simpa only [encoding] using identity.2.1
                                  have rootEq : encoding.rootPage = rootPage := by
                                    simpa only [encoding] using identity.2.2
                                  have encodingMember :
                                      encoding.index ∈ encoding.table.indexes := by
                                    rw [tableEq, indexEq]
                                    exact member
                                  have encodingDecoded :=
                                    CoreDecode.decodeCanonicalIndex_encoded
                                      encoding.table encoding.index encodingMember
                                      encoding.rootPage
                                  change CoreDecode.decodeCanonicalIndex
                                    after.schema after.schema.name
                                    (CoreDecode.CatalogEntry.ofEncoded
                                      encoding.catalogEntry) = some index
                                  simpa [CoreOverflow.IndexEncoding.catalogEntry,
                                    tableEq, indexEq, rootEq] using encodingDecoded
                                tableExpectedBefore := tableBefore
                                tableWrites
                                tableExpectedBeforeEq := tableBeforeResult.exact
                                tableWritesEq := tableWritesResult.exact
                                certificate := .encoded certified
                                expectedBefore
                                writes
                                storage := by
                                  let oldImage := byteArrayStorageImage input
                                    count _length
                                  refine ⟨oldImage, ?_, by omega, decodeBound, ?_⟩
                                  · exact CoreLocalizedRepresentation.readsPagesFrom_applyWrites_of_covered
                                      oldImage writes distinct rootPage encoding.pages
                                      (by
                                        intro offset inBounds
                                        rcases indexPageWrites_covers rootPage
                                            encoding.pages (by omega) offset
                                            inBounds with
                                          ⟨write, member, pageNumber, bytes⟩
                                        exact ⟨write, List.mem_append.mpr (.inr
                                          (by simp [indexWrites, member])),
                                          pageNumber, bytes⟩)
                                  · have lastBound :
                                        encoding.pages.length - 1 <
                                          encoding.pages.length := by omega
                                    rcases indexPageWrites_covers rootPage
                                        encoding.pages (by omega)
                                        (encoding.pages.length - 1) lastBound with
                                      ⟨write, member, pageNumber, _⟩
                                    have present : write ∈ writes := by
                                      apply List.mem_append.mpr
                                      exact .inr (by simp [indexWrites, member])
                                    have writeBound :=
                                      CorePageSource.pageId_lt_applyWrites_of_mem
                                        oldImage present
                                    change rootPage + encoding.pages.length ≤
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
              | [] => none
            else none
          else none
        else none
      else none
    else none
  else none

end CoreFileAdapter

end SQLeanite
