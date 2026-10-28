import SQLeanite.CoreChunkPageDelta.AlignTablesTablePageIdsChangedIndexed

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

theorem updateState?_freePages_eq_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.after.freePages = state.freePages := by
  rw [updateState?_freePages updated,
    updateState?_freedPageNumbers_eq_nil_of_indexed updated indexed]
  rfl

/-- Indexed ordinary updates are allocation-preserving by construction: the
active page IDs, database watermark, and freelist are all exactly unchanged.
This removes the need for a second runtime allocation scan when the final
header/freelist write plan is certified. -/
theorem updateState?_allocationWellFormed_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (allocation : state.AllocationWellFormed)
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.after.AllocationWellFormed := by
  unfold CoreChunkPageState.State.AllocationWellFormed at allocation ⊢
  rw [updateState?_activePageIds_eq_of_indexed updated indexed,
    updateState?_nextPage_eq_of_indexed updated indexed,
    updateState?_freePages_eq_of_indexed updated indexed]
  exact allocation

theorem updateState?_selected_mem
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.before ∈ state.tables ∧
      delta.table.after ∈ delta.after.tables := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, alignedTables, selected⟩
  have found := alignTables?_selected_mem alignment selected
  exact ⟨found.1, by simpa [alignedTables] using found.2⟩

def numberedWrite? (page : CorePageCodec.NumberedPage) :
    Option (GrowableStorage.PageWrite PhysicalCodec.pageSize) :=
  if _positive : 0 < page.pageNumber then
    some ⟨page.pageNumber - 1, page.page.storage⟩
  else none

theorem numberedWrite?_spec
    {page : CorePageCodec.NumberedPage}
    {write : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (converted : numberedWrite? page = some write) :
    write.pageId + 1 = page.pageNumber ∧
      write.page.bytes.toList = page.page.bytes := by
  unfold numberedWrite? at converted
  split at converted
  next positive =>
    have equal :
        (⟨page.pageNumber - 1, page.page.storage⟩ :
          GrowableStorage.PageWrite PhysicalCodec.pageSize) = write :=
      Option.some.inj converted
    subst write
    constructor
    · change (page.pageNumber - 1) + 1 = page.pageNumber
      exact Nat.sub_add_cancel positive
    · simp [CoreFile.Page.storage]
  next => contradiction

theorem mapM_numberedWrite?_covers :
    ∀ {pages : List CorePageCodec.NumberedPage}
      {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)},
      pages.mapM numberedWrite? = some writes →
      ∀ page ∈ pages,
        ∃ write ∈ writes,
          write.pageId + 1 = page.pageNumber ∧
          write.page.bytes.toList = page.page.bytes
  | [], writes, converted => by
      simp only [List.mapM_nil, pure, Option.pure_def,
        Option.some.injEq] at converted
      subst writes
      simp
  | page :: pages, writes, converted => by
      simp only [List.mapM_cons] at converted
      cases headResult : numberedWrite? page with
      | none => simp [headResult] at converted
      | some write =>
        simp only [headResult, Option.bind_eq_bind, Option.bind] at converted
        cases tailResult : pages.mapM numberedWrite? with
        | none => simp [tailResult] at converted
        | some remaining =>
          simp only [tailResult, Option.some.injEq] at converted
          have equal : write :: remaining = writes := by simpa using converted
          subst writes
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with equal | later
          · subst candidate
            exact ⟨write, by simp, numberedWrite?_spec headResult⟩
          · rcases mapM_numberedWrite?_covers tailResult candidate later with
              ⟨covered, coveredMember, specification⟩
            exact ⟨covered, by simp [coveredMember], specification⟩

/-- Conversely, every emitted write comes from one selected numbered page.
Together with `mapM_numberedWrite?_covers`, successful conversion is a
byte-preserving correspondence rather than a one-sided coverage check. -/
theorem mapM_numberedWrite?_sources :
    ∀ {pages : List CorePageCodec.NumberedPage}
      {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)},
      pages.mapM numberedWrite? = some writes →
      ∀ write ∈ writes,
        ∃ page ∈ pages,
          write.pageId + 1 = page.pageNumber ∧
          write.page.bytes.toList = page.page.bytes
  | [], writes, converted => by
      simp only [List.mapM_nil, pure, Option.pure_def,
        Option.some.injEq] at converted
      subst writes
      simp
  | page :: pages, writes, converted => by
      simp only [List.mapM_cons] at converted
      cases headResult : numberedWrite? page with
      | none => simp [headResult] at converted
      | some head =>
        simp only [headResult, Option.bind_eq_bind, Option.bind] at converted
        cases tailResult : pages.mapM numberedWrite? with
        | none => simp [tailResult] at converted
        | some tail =>
          simp only [tailResult, Option.some.injEq] at converted
          have equal : head :: tail = writes := by simpa using converted
          subst writes
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with rfl | later
          · exact ⟨page, by simp, numberedWrite?_spec headResult⟩
          · rcases mapM_numberedWrite?_sources tailResult candidate later with
              ⟨source, sourceMember, specification⟩
            exact ⟨source, by simp [sourceMember], specification⟩

def writes (delta : TableDelta) :
    Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :=
  delta.pages.mapM numberedWrite?

/-- Every numbered page selected by a table delta is present byte-for-byte in
its physical write list.  This is the changed-page half of the localized
decoder representation proof. -/
theorem writes_covers_pages {delta : TableDelta}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (converted : CoreChunkPageDelta.writes delta = some writes) :
    ∀ page ∈ delta.pages,
      ∃ write ∈ writes,
        write.pageId + 1 = page.pageNumber ∧
        write.page.bytes.toList = page.page.bytes := by
  exact mapM_numberedWrite?_covers converted

theorem writes_sources_pages {delta : TableDelta}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (converted : CoreChunkPageDelta.writes delta = some writes) :
    ∀ write ∈ writes,
      ∃ page ∈ delta.pages,
        write.pageId + 1 = page.pageNumber ∧
        write.page.bytes.toList = page.page.bytes := by
  exact mapM_numberedWrite?_sources converted

def beforeWrites (delta : TableDelta) :
    Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) := do
  let pages ← (match delta.beforePages? with
    | some pages => some pages
    | none => CorePageCodec.encodeChunkPath delta.before.table.schema
        delta.chunkKey delta.before.tree.root)
  pages.mapM numberedWrite?

end CoreChunkPageDelta

end SQLeanite
