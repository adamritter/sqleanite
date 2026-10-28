import SQLeanite.CoreChunkPageDelta.TableDelta

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

/-- If the completed replacement loop did not advance the allocation
watermark, every insertion in the loop was a no-allocation update and the
complete physical page-identity list is unchanged. -/
theorem replaceManyFold_pageIds_of_noAllocation :
    ∀ {entries : List (PagedBTree.Entry CoreChunkPageState.Chunk)}
      {store updated : PersistentPageTree.Store CoreChunkPageState.Chunk}
      {rows remaining : List Core.Row},
      replaceManyFold entries (store, rows) = some (updated, remaining) →
      updated.nextPage = store.nextPage →
      updated.root.pageIds = store.root.pageIds
  | [], store, updated, rows, remaining, success, noAllocation => by
      simp only [replaceManyFold, Option.some.injEq, Prod.mk.injEq] at success
      exact congrArg (fun tree => tree.root.pageIds) success.1.symm
  | entry :: entries, store, updated, rows, remaining, success,
      noAllocation => by
      unfold replaceManyFold at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨resolved, resolvedResult, success⟩
      split at success
      next same =>
        exact replaceManyFold_pageIds_of_noAllocation success noAllocation
      next changed =>
        let inserted := store.insert entry.1 resolved.1
        have stepBound : store.nextPage ≤ inserted.nextPage :=
          store.nextPage_le_insert entry.1 resolved.1
        have tailBound : inserted.nextPage ≤ updated.nextPage :=
          replaceManyFold_nextPage_le success
        have stepNoAllocation : inserted.nextPage = store.nextPage := by
          omega
        have tailNoAllocation : updated.nextPage = inserted.nextPage := by
          omega
        exact (replaceManyFold_pageIds_of_noAllocation success
          tailNoAllocation).trans
            (store.insert_pageIds_of_noAllocation entry.1 resolved.1
              stepNoAllocation)

/-- The same no-allocation replacement loop preserves the recursive decoder
height.  This is stronger than merely retaining the page-ID set and lets the
validated pre-state fuel bound frame the post-state directly. -/
theorem replaceManyFold_height_of_noAllocation :
    ∀ {entries : List (PagedBTree.Entry CoreChunkPageState.Chunk)}
      {store updated : PersistentPageTree.Store CoreChunkPageState.Chunk}
      {rows remaining : List Core.Row},
      replaceManyFold entries (store, rows) = some (updated, remaining) →
      updated.nextPage = store.nextPage →
      updated.root.erase.height = store.root.erase.height
  | [], store, updated, rows, remaining, success, noAllocation => by
      simp only [replaceManyFold, Option.some.injEq, Prod.mk.injEq] at success
      exact congrArg (fun tree => tree.root.erase.height) success.1.symm
  | entry :: entries, store, updated, rows, remaining, success,
      noAllocation => by
      unfold replaceManyFold at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨resolved, resolvedResult, success⟩
      split at success
      next => exact replaceManyFold_height_of_noAllocation success noAllocation
      next =>
        let inserted := store.insert entry.1 resolved.1
        have stepBound : store.nextPage ≤ inserted.nextPage :=
          store.nextPage_le_insert entry.1 resolved.1
        have tailBound : inserted.nextPage ≤ updated.nextPage :=
          replaceManyFold_nextPage_le success
        have stepNoAllocation : inserted.nextPage = store.nextPage := by omega
        have tailNoAllocation : updated.nextPage = inserted.nextPage := by omega
        exact (replaceManyFold_height_of_noAllocation success
          tailNoAllocation).trans
            (store.insert_height_of_noAllocation entry.1 resolved.1
              stepNoAllocation)

/-- Update all changed chunks without rebuilding table topology.  Stable page
identity selects the exact before/after paths for the rollback journal.  The
final representation equality is retained as the proof field of `TableState`,
so a primary-key change or missing row rejects this path and falls back. -/
def replaceMany? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (replacement : Core.Table) : Option TableDelta := do
  let row ← firstDifference state.table.rows replacement.rows
  let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
    { state.tree with nextPage }
  let updated ← replaceManyFold state.tree.root.erase.toList
    (allocating, replacement.rows)
  if _consumed : updated.2 = [] then
    let updatedTree := updated.1
    if _noAllocation : updatedTree.nextPage = nextPage then
      if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
        let changedPhysical := CorePageCodec.changedPhysicalChunkPagesFast
          state.tree.root updatedTree.root
        let changedIds := changedPhysical.map
          CorePageCodec.PhysicalChunkPage.pageNumber
        let beforePages ← encodeChunkNodesWithIds state.table.schema changedIds
          state.tree.root
        let pages ← changedPhysical.mapM
          (CorePageCodec.encodePhysicalChunkPage replacement.schema)
        let after : CoreChunkPageState.TableState := {
          table := replacement
          tree := updatedTree
          represents
          capacity := state.capacity
          capacity_pos := state.capacity_pos }
        some ⟨state, after, row.treeKey, pages, some beforePages, []⟩
      else none
    else none
  else none

theorem replace?_freedPageNumbers {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.freedPageNumbers = [] := by
  unfold replace? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨pages, pagesResult, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem replace?_after_nextPage {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.after.tree.nextPage = nextPage := by
  unfold replace? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨pages, pagesResult, success⟩
        injection success with equal
        subst delta
        exact noAllocation
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_freedPageNumbers
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.freedPageNumbers = [] := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨updated, updatedResult, success⟩
  dsimp only at success
  split at success
  next =>
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some_iff.mp success with
          ⟨pages, pagesResult, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_after_nextPage
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.tree.nextPage = nextPage := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨updated, updatedResult, success⟩
  dsimp only at success
  split at success
  next =>
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some_iff.mp success with
          ⟨pages, pagesResult, success⟩
        injection success with equal
        subst delta
        exact noAllocation
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.table = replacement := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some_iff.mp success with ⟨updated, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        have equal := Option.some.inj success
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  rw [delta.after.represents, replaceMany?_table success]

theorem replaceMany?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some_iff.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next represents =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        exact treePagesAccounted_of_changedPhysical replacement.schema
          state.tree.root _ pages pagesResult
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_encodabilityPreserved
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.EncodabilityPreserved := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some_iff.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next represents =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        exact encodabilityPreserved_of_changedPhysical replacement.schema
          state.tree.root _ pages pagesResult
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.TreePagesSelected := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some_iff.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        exact treePagesSelected_of_changedPhysical replacement.schema
          state.tree.root _ pages pagesResult
      next => contradiction
    next => contradiction
  next => contradiction

/-- Consume the replacement rows belonging to one old chunk.  Both inputs are
strictly rowid ordered; rows absent from the replacement are deletions, while a
replacement key not present in the old stream rejects the delete-only path. -/
def retainedChunk? : CoreChunkPageState.Chunk → List Core.Row →
    Option (CoreChunkPageState.Chunk × List Core.Row)
  | [], rows => some ([], rows)
  | _ :: olds, [] => retainedChunk? olds []
  | old :: olds, row :: rows =>
      if old.rowid = row.rowid then do
        let retained ← retainedChunk? olds rows
        some (row :: retained.1, retained.2)
      else if old.rowid.value < row.rowid.value then
        retainedChunk? olds (row :: rows)
      else none

/-- Delete many rows while retaining the existing chunk/page topology wherever
possible. Nonempty chunks keep their stable key and page identity; only chunks
made empty enter the proved borrow/merge deletion algorithm. -/
def retainMany? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (replacement : Core.Table) : Option TableDelta := do
  let row ← firstDeleted state.table.rows replacement.rows
  let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
    { state.tree with nextPage }
  let updated ← state.tree.root.erase.toList.foldlM (fun accumulator entry => do
    let resolved ← retainedChunk? entry.2 accumulator.2.1
    if resolved.1 = entry.2 then
      some (accumulator.1, resolved.2, accumulator.2.2)
    else if resolved.1.isEmpty then
      let deleted ← accumulator.1.delete? entry.1
      some (deleted.1, resolved.2, accumulator.2.2 ++ deleted.2)
    else
      some (accumulator.1.insert entry.1 resolved.1, resolved.2,
        accumulator.2.2)) (allocating, replacement.rows, [])
  if _consumed : updated.2.1 = [] then
    let updatedTree := updated.1
    if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
      let changedPhysical := CorePageCodec.changedPhysicalChunkPagesFast
        state.tree.root updatedTree.root
      let changedIds := changedPhysical.map
        CorePageCodec.PhysicalChunkPage.pageNumber
      let beforeIds := changedIds ++ updated.2.2
      let beforePages ← encodeChunkNodesWithIds state.table.schema beforeIds
        state.tree.root
      let pages ← changedPhysical.mapM
        (CorePageCodec.encodePhysicalChunkPage replacement.schema)
      let after : CoreChunkPageState.TableState := {
        table := replacement
        tree := updatedTree
        represents
        capacity := state.capacity
        capacity_pos := state.capacity_pos }
      some ⟨state, after, row.treeKey, pages, some beforePages,
        updated.2.2⟩
    else none
  else none

theorem retainMany?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.after.table = replacement := by
  unfold retainMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some_iff.mp success with ⟨updated, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
      have equal := Option.some.inj success
      subst delta
      rfl
    next => contradiction
  next => contradiction

theorem retainMany?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  rw [delta.after.represents, retainMany?_table success]

theorem retainMany?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold retainMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some_iff.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next represents =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨beforePages, beforeResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨pages, pagesResult, success⟩
      have equal := Option.some.inj success
      subst delta
      exact treePagesAccounted_of_changedPhysical replacement.schema
        state.tree.root _ pages pagesResult
    next => contradiction
  next => contradiction

theorem retainMany?_encodabilityPreserved
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.EncodabilityPreserved := by
  unfold retainMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some_iff.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next represents =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨beforePages, beforeResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨pages, pagesResult, success⟩
      have equal := Option.some.inj success
      subst delta
      exact encodabilityPreserved_of_changedPhysical replacement.schema
        state.tree.root _ pages pagesResult
    next => contradiction
  next => contradiction

theorem retainMany?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.TreePagesSelected := by
  unfold retainMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some_iff.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨beforePages, beforeResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨pages, pagesResult, success⟩
      have equal := Option.some.inj success
      subst delta
      exact treePagesSelected_of_changedPhysical replacement.schema
        state.tree.root _ pages pagesResult
    next => contradiction
  next => contradiction

end CoreChunkPageDelta

end SQLeanite
