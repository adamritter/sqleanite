import SQLeanite.CoreLocalizedRepresentation.DatabaseOnSourceUpdateStateApplyWritesBelowExtension

namespace SQLeanite
namespace CoreLocalizedRepresentation

/-- Live-state specialization for the exact final write list selected by the
header/freelist planner.  Unlike `pageSourceContains_updateStateTree`, the
table conversion equation names only `baseWrites`; proof-carrying membership
and noninterference facts connect it to `finalWrites`, which is the list the
journal and main-file writer actually consume. -/
theorem pageSourceContains_updateStateTree_extension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterPages, write.pageId + 1 ≠ page.pageNumber)
    (beforeEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some beforePages)
    (afterEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterPages)
    (oldContains : CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage image) beforePages)
    (oldBounds : ∀ page ∈ beforePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) afterPages := by
  apply pageSourceContains_tableDeltaComplete_extension image delta.table
    baseWrites finalWrites beforePages afterPages converted distinct baseMember
    addedUntouched
  · exact CoreChunkPageDelta.updateState?_treePagesAccounted updated
      beforePages afterPages beforeEncoded afterEncoded
  · exact CoreChunkPageDelta.updateState?_treePagesSelected updated afterPages
      afterEncoded
  · rw [CorePageCodec.encodeChunkNode_pageNumbers _ _ _ afterEncoded]
    exact (CoreChunkPageDelta.updateState?_identityWellFormed updated).1
  · exact oldContains
  · exact oldBounds

/-- Changed-index writers use the candidate before the unchanged-index check;
its table delta has the same exact page-accounting guarantees. -/
theorem pageSourceContains_updateStateCandidateTree
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (updated : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (beforeEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some beforePages)
    (afterEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterPages)
    (oldContains : CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage image) beforePages)
    (oldBounds : ∀ page ∈ beforePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) afterPages := by
  apply pageSourceContains_tableDeltaComplete image delta.table writes
    beforePages afterPages converted distinct
  · exact CoreChunkPageDelta.updateStateCandidate?_treePagesAccounted updated
      beforePages afterPages beforeEncoded afterEncoded
  · exact CoreChunkPageDelta.updateStateCandidate?_treePagesSelected updated
      afterPages afterEncoded
  · rw [CorePageCodec.encodeChunkNode_pageNumbers _ _ _ afterEncoded]
    exact (CoreChunkPageDelta.updateStateCandidate?_identityWellFormed updated).1
  · exact oldContains
  · exact oldBounds

/-- Changed-index counterpart of
`pageSourceContains_updateStateTree_extension`. -/
theorem pageSourceContains_updateStateCandidateTree_extension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (updated : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterPages, write.pageId + 1 ≠ page.pageNumber)
    (beforeEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some beforePages)
    (afterEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterPages)
    (oldContains : CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage image) beforePages)
    (oldBounds : ∀ page ∈ beforePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) afterPages := by
  apply pageSourceContains_tableDeltaComplete_extension image delta.table
    baseWrites finalWrites beforePages afterPages converted distinct baseMember
    addedUntouched
  · exact CoreChunkPageDelta.updateStateCandidate?_treePagesAccounted updated
      beforePages afterPages beforeEncoded afterEncoded
  · exact CoreChunkPageDelta.updateStateCandidate?_treePagesSelected updated
      afterPages afterEncoded
  · rw [CorePageCodec.encodeChunkNode_pageNumbers _ _ _ afterEncoded]
    exact (CoreChunkPageDelta.updateStateCandidate?_identityWellFormed updated).1
  · exact oldContains
  · exact oldBounds

/-- A successful ordinary state delta establishes the complete changed-table
certificate for inline records.  Both old and new tree lists are obtained from
the general encoder inverse; `pageSourceContains_updateStateTree` then proves
that the actual write overlay contains every post-state byte. -/
def TableOnSource.updateStateInline
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema)
    (before : TableOnSource (CorePageSource.ofStorageImage image)
      delta.table.before)
    (beforeInline : before.encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding)
    (afterInline : afterEncoding.overflowPages = [])
    (oldBounds : ∀ page ∈ before.encoding.treePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount)
    (heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)).pageCount + 1) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.table.after := by
  have beforeTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some before.encoding.treePages := by
    simpa [schemaSame] using before.inlineEncoded beforeInline
  have afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterEncoding.treePages :=
    CorePageCodec.encodeChunkNodeWithOverflow_noOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow afterEncoding afterEncoded afterInline
  have treeContains := pageSourceContains_updateStateTree image state database
    delta writes before.encoding.treePages afterEncoding.treePages updated
    converted distinct beforeTree afterTree before.treeContains oldBounds
  refine {
    nextOverflow := before.nextOverflow
    encoding := afterEncoding
    encoded := afterEncoded
    treeContains
    overflowContains := ?_
    heightBound
    nextPositive := before.nextPositive
    pageBound := ?_
    fuelBound := ?_ }
  · intro offset inBounds
    simp [afterInline] at inBounds
  · rw [afterInline]
    simpa [beforeInline] using before.pageBound
  · rw [afterInline]
    simp

/-- Final-write variant of `TableOnSource.updateStateInline`.  It constructs
the changed-table certificate directly over the header/freelist-augmented
write list used by the live journal, instead of first proving a certificate
for a smaller logical delta and transporting it afterward. -/
def TableOnSource.updateStateInlineExtension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema)
    (before : TableOnSource (CorePageSource.ofStorageImage image)
      delta.table.before)
    (beforeInline : before.encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterEncoding.treePages,
        write.pageId + 1 ≠ page.pageNumber)
    (afterInline : afterEncoding.overflowPages = [])
    (oldBounds : ∀ page ∈ before.encoding.treePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount)
    (heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)).pageCount + 1) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) delta.table.after := by
  have beforeTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some before.encoding.treePages := by
    simpa [schemaSame] using before.inlineEncoded beforeInline
  have afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterEncoding.treePages :=
    CorePageCodec.encodeChunkNodeWithOverflow_noOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow afterEncoding afterEncoded afterInline
  have treeContains := pageSourceContains_updateStateTree_extension image state
    database delta baseWrites finalWrites before.encoding.treePages
    afterEncoding.treePages updated converted distinct baseMember addedUntouched
    beforeTree afterTree before.treeContains oldBounds
  refine {
    nextOverflow := before.nextOverflow
    encoding := afterEncoding
    encoded := afterEncoded
    treeContains
    overflowContains := ?_
    heightBound
    nextPositive := before.nextPositive
    pageBound := ?_
    fuelBound := ?_ }
  · intro offset inBounds
    simp [afterInline] at inBounds
  · rw [afterInline]
    simpa [beforeInline] using before.pageBound
  · rw [afterInline]
    simp

/-- Changed-index counterpart of `updateStateInline`, using the exact candidate
consumed by the live index preparation paths. -/
def TableOnSource.updateStateCandidateInline
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (updated : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema)
    (before : TableOnSource (CorePageSource.ofStorageImage image)
      delta.table.before)
    (beforeInline : before.encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding)
    (afterInline : afterEncoding.overflowPages = [])
    (oldBounds : ∀ page ∈ before.encoding.treePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount)
    (heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)).pageCount + 1) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.table.after := by
  have beforeTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some before.encoding.treePages := by
    simpa [schemaSame] using before.inlineEncoded beforeInline
  have afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterEncoding.treePages :=
    CorePageCodec.encodeChunkNodeWithOverflow_noOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow afterEncoding afterEncoded afterInline
  have treeContains := pageSourceContains_updateStateCandidateTree image state
    database delta writes before.encoding.treePages afterEncoding.treePages
    updated converted distinct beforeTree afterTree before.treeContains oldBounds
  refine {
    nextOverflow := before.nextOverflow
    encoding := afterEncoding
    encoded := afterEncoded
    treeContains
    overflowContains := ?_
    heightBound
    nextPositive := before.nextPositive
    pageBound := ?_
    fuelBound := ?_ }
  · intro offset inBounds
    simp [afterInline] at inBounds
  · rw [afterInline]
    simpa [beforeInline] using before.pageBound
  · rw [afterInline]
    simp

/-- Final-write changed-index counterpart of
`TableOnSource.updateStateInlineExtension`. -/
def TableOnSource.updateStateCandidateInlineExtension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (updated : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema)
    (before : TableOnSource (CorePageSource.ofStorageImage image)
      delta.table.before)
    (beforeInline : before.encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterEncoding.treePages,
        write.pageId + 1 ≠ page.pageNumber)
    (afterInline : afterEncoding.overflowPages = [])
    (oldBounds : ∀ page ∈ before.encoding.treePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount)
    (heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)).pageCount + 1) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) delta.table.after := by
  have beforeTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some before.encoding.treePages := by
    simpa [schemaSame] using before.inlineEncoded beforeInline
  have afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterEncoding.treePages :=
    CorePageCodec.encodeChunkNodeWithOverflow_noOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow afterEncoding afterEncoded afterInline
  have treeContains := pageSourceContains_updateStateCandidateTree_extension
    image state database delta baseWrites finalWrites before.encoding.treePages
    afterEncoding.treePages updated converted distinct baseMember addedUntouched
    beforeTree afterTree before.treeContains oldBounds
  refine {
    nextOverflow := before.nextOverflow
    encoding := afterEncoding
    encoded := afterEncoded
    treeContains
    overflowContains := ?_
    heightBound
    nextPositive := before.nextPositive
    pageBound := ?_
    fuelBound := ?_ }
  · intro offset inBounds
    simp [afterInline] at inBounds
  · rw [afterInline]
    simpa [beforeInline] using before.pageBound
  · rw [afterInline]
    simp

/-- Decoding a canonical persistent table after a local page delta returns
exactly the logical table carried by the proof-carrying state.  Tree pages are
identified and may be sparse; overflow pages retain their separately allocated
contiguous interval. -/
theorem decodeTableFrom_of_pageSourceContains
    (source : CoreDecode.PageSource)
    (state : CoreChunkPageState.TableState)
    (nextOverflow : Nat) (encoding : CorePageCodec.OverflowEncoding)
    (encoded : CorePageCodec.encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (treeContains : CorePageCodec.PageSourceContains source
      encoding.treePages)
    (overflowContains : CoreDecode.ReadsPagesFrom source nextOverflow
      encoding.overflowPages)
    (heightBound : state.tree.root.erase.height < source.pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length < source.pageCount + 1) :
    CoreDecode.decodeTableFrom source
      (CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry state)) =
      some state.table.withoutIndexes := by
  exact CorePageCodec.decodeTableFrom_encodeChunkNodeWithOverflow source state
    nextOverflow encoding encoded treeContains overflowContains heightBound
    nextPositive pageBound fuelBound

/-- Direct storage-image specialization used by a localized table writer. -/
theorem decodeTableFrom_applyWrites
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (state : CoreChunkPageState.TableState)
    (nextOverflow : Nat) (encoding : CorePageCodec.OverflowEncoding)
    (encoded : CorePageCodec.encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (accounted : ∀ numbered ∈ encoding.treePages,
      (∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) ∨
      (0 < numbered.pageNumber ∧
        numbered.pageNumber ≤ image.pageCount ∧
        (CorePageSource.ofStorageImage image).readPage numbered.pageNumber =
          some numbered.page.bytes ∧
        ∀ write ∈ writes, write.pageId + 1 ≠ numbered.pageNumber))
    (overflowContains : CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      nextOverflow encoding.overflowPages)
    (heightBound : state.tree.root.erase.height <
      (GrowableStorage.applyWrites image writes).pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length <
      (GrowableStorage.applyWrites image writes).pageCount + 1) :
    CoreDecode.decodeTableFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      (CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry state)) =
      some state.table.withoutIndexes := by
  exact decodeTableFrom_of_pageSourceContains _ state nextOverflow encoding
    encoded
    (pageSourceContains_applyWrites image writes distinct encoding.treePages
      accounted)
    overflowContains (by simpa using heightBound) nextPositive pageBound
    (by simpa using fuelBound)

end CoreLocalizedRepresentation

end SQLeanite
