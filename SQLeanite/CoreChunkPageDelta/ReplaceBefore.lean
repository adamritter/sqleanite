import SQLeanite.CoreChunkPageDelta.ReplaceManyFoldPageIdsOfNoAllocation

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

theorem replace?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold replace? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem insert?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold insert? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    split at success
    next =>
      dsimp only at success
      split at success
      next =>
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
          injection success with equal
          subst delta
          rfl
        next => contradiction
      next => contradiction
    next => contradiction
  next => contradiction

theorem splitInsert?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨leftKey, _, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨rightKey, _, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, _, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem delete?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold delete? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
          injection success with equal
          subst delta
          rfl
        next => contradiction
      next => contradiction
    next => contradiction
  next => contradiction

theorem mergeDelete?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, _, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem retainMany?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.before = state := by
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
      injection success with equal
      subst delta
      rfl
    next => contradiction
  next => contradiction

theorem replaceMany?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.before = state := by
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
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

private theorem replaceManyFold_rootId :
    ∀ (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk))
      (store : PersistentPageTree.Store CoreChunkPageState.Chunk)
      (rows : List Core.Row)
      (updated : PersistentPageTree.Store CoreChunkPageState.Chunk ×
        List Core.Row),
      replaceManyFold entries (store, rows) = some updated →
      updated.1.root.rootId = store.root.rootId
  | [], store, rows, updated, success => by
      simp only [replaceManyFold, Option.some.injEq] at success
      subst updated
      rfl
  | entry :: entries, store, rows, updated, success => by
      unfold replaceManyFold at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨resolved, resolvedResult, success⟩
      split at success
      next => exact replaceManyFold_rootId entries store resolved.2 updated success
      next =>
        have tail := replaceManyFold_rootId entries
          (store.insert entry.1 resolved.1) resolved.2 updated success
        exact tail.trans (store.insert_rootId entry.1 resolved.1)

theorem retainManyFold_rootId :
    ∀ (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk))
      (store : PersistentPageTree.Store CoreChunkPageState.Chunk)
      (rows : List Core.Row) (freed : List Nat)
      (updated : PersistentPageTree.Store CoreChunkPageState.Chunk ×
        List Core.Row × List Nat),
      entries.foldlM (fun accumulator entry => do
        let resolved ← retainedChunk? entry.2 accumulator.2.1
        if resolved.1 = entry.2 then
          some (accumulator.1, resolved.2, accumulator.2.2)
        else if resolved.1.isEmpty then
          let deleted ← accumulator.1.delete? entry.1
          some (deleted.1, resolved.2, accumulator.2.2 ++ deleted.2)
        else
          some (accumulator.1.insert entry.1 resolved.1, resolved.2,
            accumulator.2.2)) (store, rows, freed) = some updated →
      updated.1.root.rootId = store.root.rootId
  | [], store, rows, freed, updated, success => by
      simp only [List.foldlM_nil, pure, Option.pure_def,
        Option.some.injEq] at success
      subst updated
      rfl
  | entry :: entries, store, rows, freed, updated, success => by
      simp only [List.foldlM_cons] at success
      rcases Option.bind_eq_some_iff.mp success with ⟨next, stepResult, success⟩
      have stepRoot : next.1.root.rootId = store.root.rootId := by
        rcases Option.bind_eq_some_iff.mp stepResult with
          ⟨resolved, resolvedResult, stepResult⟩
        split at stepResult
        next =>
          injection stepResult with equal
          subst next
          rfl
        next =>
          split at stepResult
          next =>
            rcases Option.bind_eq_some_iff.mp stepResult with
              ⟨deleted, deletedResult, stepResult⟩
            injection stepResult with equal
            subst next
            exact store.delete?_rootId deletedResult
          next =>
            injection stepResult with equal
            subst next
            exact store.insert_rootId entry.1 resolved.1
      have tail := retainManyFold_rootId entries next.1 next.2.1 next.2.2
        updated success
      exact tail.trans stepRoot

theorem replace?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold replace? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        exact PersistentPageTree.Store.insert_rootId
          { state.tree with nextPage } entry.1 (replaceRow row entry.2)
      next => contradiction
    next => contradiction
  next => contradiction

theorem replace?_pageIds {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.after.tree.root.pageIds = state.tree.root.pageIds := by
  unfold replace? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        exact PersistentPageTree.Store.insert_pageIds_of_noAllocation
          { state.tree with nextPage } entry.1 (replaceRow row entry.2)
          noAllocation
      next => contradiction
    next => contradiction
  next => contradiction

theorem replace?_height {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.after.tree.root.erase.height = state.tree.root.erase.height := by
  unfold replace? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        exact PersistentPageTree.Store.insert_height_of_noAllocation
          { state.tree with nextPage } entry.1 (replaceRow row entry.2)
          noAllocation
      next => contradiction
    next => contradiction
  next => contradiction

theorem insert?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold insert? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    split at success
    next =>
      dsimp only at success
      split at success
      next =>
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
          injection success with equal
          subst delta
          exact PersistentPageTree.Store.insert_rootId
            { state.tree with nextPage } entry.1
              (Core.orderedUpsert row entry.2)
        next => contradiction
      next => contradiction
    next => contradiction
  next => contradiction

theorem delete?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold delete? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
          injection success with equal
          subst delta
          exact PersistentPageTree.Store.insert_rootId
            { state.tree with nextPage } entry.1
              (entry.2.filter fun old => old.rowid != row.rowid)
        next => contradiction
      next => contradiction
    next => contradiction
  next => contradiction

theorem mergeDelete?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨deleted, deletedResult, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        have root := PersistentPageTree.Store.delete?_rootId deletedResult
        simpa using root
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        have root := replaceManyFold_rootId state.tree.root.erase.toList
          { state.tree with nextPage } replacement.rows updated updatedResult
        simpa using root
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_pageIds
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.tree.root.pageIds = state.tree.root.pageIds := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        have pageIds : updated.1.root.pageIds = state.tree.root.pageIds := by
          have preserved := replaceManyFold_pageIds_of_noAllocation
            updatedResult (by simpa using noAllocation)
          simpa using preserved
        injection success with equal
        subst delta
        exact pageIds
      next => contradiction
    next => contradiction
  next => contradiction

end CoreChunkPageDelta

end SQLeanite
