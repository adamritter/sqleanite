import SQLeanite.CoreChunkPageDelta.ChunkTableCatalogEntryRetarget

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

theorem alignTables?_tablePageIds_changed_indexed :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.tablePagesSufficient = true →
      delta.before.table.indexes ≠ [] →
      CoreChunkPageState.tablePageIds aligned.tables =
        CoreChunkPageState.tablePageIds states
  | _, [], target, aligned, delta, success, selected, sufficient,
      indexed => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, old :: olds, target, aligned, delta, success, selected,
      sufficient, indexed => by
      cases target with
      | nil => simp [alignTables?] at success
      | cons replacement replacements =>
        unfold alignTables? at success
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          unfold CoreChunkPageState.tablePageIds
          simp only [List.flatMap_cons,
            CoreChunkPageState.TableState.retarget_tree]
          exact congrArg (old.tree.root.pageIds ++ ·)
            (alignTables?_tablePageIds_changed_indexed tailResult selected
              sufficient indexed)
        next =>
          split at success
          next => contradiction
          next head headResult =>
            split at success
            next => contradiction
            next tail tailResult =>
              split at success
              next =>
                injection success with equal
                subst aligned
                have headEqual : head = delta := Option.some.inj selected
                subst head
                have tailNone : tail.delta = none := by
                  cases tailDelta : tail.delta with
                  | none => rfl
                  | some value => simp [tailDelta] at *
                have sameLength :=
                  delta.tablePagesSufficient_rowsLength_of_indexed sufficient
                    indexed
                rw [replaceBetween?_before headResult,
                  replaceBetween?_table headResult] at sameLength
                have headPages := replaceBetween?_pageIds_of_length_eq
                  (state := old) (replacement := replacement)
                  (delta := delta) sameLength headResult
                have tailPages := alignTables?_tablePageIds_none tailResult
                  tailNone
                simp only [CoreChunkPageState.tablePageIds] at tailPages
                unfold CoreChunkPageState.tablePageIds
                simp only [List.flatMap_cons,
                  CoreChunkPageState.TableState.pageIds]
                rw [headPages, tailPages]
              next => contradiction

def addFreePages (existing added : List Nat) : List Nat :=
  added.foldl (fun pages page =>
    if pages.contains page then pages else pages ++ [page]) existing

/-- Build the table-page delta before deciding whether secondary index pages
can remain untouched.  Changed-index writers consume this candidate and attach
their own proved physical index delta; the ordinary path below additionally
requires an identical index image. -/
def updateStateCandidate? (state : CoreChunkPageState.State)
    (database : Core.Database) :
    Option StateDelta := do
  let aligned ← alignTables? state.nextPage state.tables database.tables
  let table ← aligned.delta
  if _identities : table.IdentityWellFormed then
    let after : CoreChunkPageState.State := {
      database
      tables := aligned.tables
      tables_eq := aligned.aligned
      nextPage := aligned.nextPage
      freePages := addFreePages state.freePages table.freedPageNumbers }
    some ⟨state, after, table⟩
  else none

theorem updateStateCandidate?_identityWellFormed
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.table.IdentityWellFormed := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next identities =>
    injection updated with equal
    subst delta
    exact identities
  next => contradiction

theorem updateStateCandidate?_endpoints
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.before = state ∧ delta.after.database = database := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next identities =>
    injection updated with equal
    subst delta
    exact ⟨rfl, rfl⟩
  next => contradiction

theorem updateStateCandidate?_freePages
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.after.freePages =
      addFreePages state.freePages delta.table.freedPageNumbers := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst delta
    rfl
  next => contradiction

/-- Expose the exact recursive table alignment retained inside a successful
state delta.  This proof-only witness lets physical representation proofs
transport unchanged tables in order and replace exactly the selected table. -/
theorem updateStateCandidate?_alignment
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    ∃ aligned : AlignedTables database.tables,
      alignTables? state.nextPage state.tables database.tables = some aligned ∧
      aligned.tables = delta.after.tables ∧
      aligned.delta = some delta.table := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst delta
    exact ⟨aligned, alignedResult, rfl, tableResult⟩
  next => contradiction

theorem updateStateCandidate?_treePagesAccounted
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.table.TreePagesAccounted := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst delta
    exact alignTables?_delta_treePagesAccounted alignedResult tableResult
  next => contradiction

theorem updateStateCandidate?_encodabilityPreserved
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.table.EncodabilityPreserved := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst delta
    exact alignTables?_delta_encodabilityPreserved alignedResult tableResult
  next => contradiction

theorem updateStateCandidate?_treePagesSelected
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.table.TreePagesSelected := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst delta
    exact alignTables?_delta_treePagesSelected alignedResult tableResult
  next => contradiction

def updateState? (state : CoreChunkPageState.State) (database : Core.Database) :
    Option StateDelta := do
  let delta ← updateStateCandidate? state database
  if _sufficient : delta.table.tablePagesSufficient then some delta else none

theorem updateState?_identityWellFormed {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.IdentityWellFormed := by
  unfold updateState? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_identityWellFormed candidateResult
  next => contradiction

theorem updateState?_tablePagesSufficient {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.tablePagesSufficient = true := by
  unfold updateState? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next sufficient =>
    injection updated with equal
    subst candidate
    exact sufficient
  next => contradiction

theorem updateState?_endpoints {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.before = state ∧ delta.after.database = database := by
  unfold updateState? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_endpoints candidateResult
  next => contradiction

theorem updateState?_freePages
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.after.freePages =
      addFreePages state.freePages delta.table.freedPageNumbers := by
  unfold updateState? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_freePages candidateResult
  next => contradiction

theorem updateState?_alignment {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    ∃ aligned : AlignedTables database.tables,
      alignTables? state.nextPage state.tables database.tables = some aligned ∧
      aligned.tables = delta.after.tables ∧
      aligned.delta = some delta.table := by
  unfold updateState? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_alignment candidateResult
  next => contradiction

/-- Ordinary localized table writes preserve every catalog-level table/index
declaration.  This is derived from the same successful alignment and
`tablePagesSufficient` check consumed by the live writer. -/
theorem updateState?_metadataAligned
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    TablesMetadataAligned (state.tables.map fun table => table.table)
      database.tables := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, _, selected⟩
  exact alignTables?_metadata_changed alignment selected
    (updateState?_tablePagesSufficient updated)

/-- The ordinary localized fast path leaves every table entry in page-zero's
catalog byte-for-byte unchanged, including root page numbers. -/
theorem updateState?_catalogEntries
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (allocation : state.AllocationWellFormed)
    (updated : updateState? state database = some delta) :
    delta.after.tables.map CorePageCodec.chunkTableCatalogEntry =
      state.tables.map CorePageCodec.chunkTableCatalogEntry := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, alignedTables, selected⟩
  rw [← alignedTables]
  apply alignTables?_catalogEntries_changed _ alignment selected
    (updateState?_tablePagesSufficient updated)
  intro table member
  apply allocation.2.1 table.tree.root.rootId
  unfold CoreChunkPageState.State.activePageIds
    CoreChunkPageState.tablePageIds
  exact List.mem_flatMap.mpr
    ⟨table, member, PersistentPageTree.Node.rootId_mem_pageIds table.tree.root⟩

theorem updateState?_treePagesAccounted
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.TreePagesAccounted := by
  unfold updateState? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_treePagesAccounted candidateResult
  next => contradiction

theorem updateState?_encodabilityPreserved
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.EncodabilityPreserved := by
  unfold updateState? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_encodabilityPreserved candidateResult
  next => contradiction

theorem updateState?_treePagesSelected
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.TreePagesSelected := by
  unfold updateState? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_treePagesSelected candidateResult
  next => contradiction

theorem updateState?_selectedPageIds_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.table.after.tree.root.pageIds =
      delta.table.before.tree.root.pageIds := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, _, selected⟩
  exact alignTables?_selectedPageIds_of_indexed alignment selected
    (updateState?_tablePagesSufficient updated) indexed

theorem updateState?_selectedHeight_eq_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.table.after.tree.root.erase.height =
      delta.table.before.tree.root.erase.height := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, _, selected⟩
  exact alignTables?_selectedHeight_of_indexed alignment selected
    (updateState?_tablePagesSufficient updated) indexed

theorem updateState?_activePageIds_eq_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.after.activePageIds = state.activePageIds := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, alignedTables, selected⟩
  unfold CoreChunkPageState.State.activePageIds
  rw [← alignedTables]
  exact alignTables?_tablePageIds_changed_indexed alignment selected
    (updateState?_tablePagesSufficient updated) indexed

theorem updateState?_nextPage_eq_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.after.nextPage = state.nextPage := by
  have alignment := updateState?_alignment updated
  rcases alignment with ⟨aligned, alignedResult, alignedTables, selected⟩
  have nextPage := alignTables?_nextPage_changed_indexed alignedResult selected
    (updateState?_tablePagesSufficient updated) indexed
  unfold updateState? at updated
  rcases Option.bind_eq_some_iff.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    unfold updateStateCandidate? at candidateResult
    rcases Option.bind_eq_some_iff.mp candidateResult with
      ⟨builtAligned, builtResult, candidateResult⟩
    rcases Option.bind_eq_some_iff.mp candidateResult with
      ⟨table, tableResult, candidateResult⟩
    split at candidateResult
    next =>
      injection candidateResult with equal
      subst delta
      have alignedEqual : builtAligned = aligned := by
        rw [builtResult] at alignedResult
        exact Option.some.inj alignedResult
      subst builtAligned
      simpa using nextPage
    next => contradiction
  next => contradiction

theorem updateState?_freedPageNumbers_eq_nil_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.table.freedPageNumbers = [] := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, alignedTables, selected⟩
  exact alignTables?_selectedFreedPages_of_indexed alignment selected
    (updateState?_tablePagesSufficient updated) indexed

end CoreChunkPageDelta

end SQLeanite
