import SQLeanite.CoreChunkPageDelta.ReplaceBetween

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

theorem delete?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold delete? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        split at success
        next =>
          split at success
          next noAllocation =>
            split at success
            next represents =>
              cases pageResult : CorePageCodec.encodeChunkPath
                  replacement.schema entry.1
                  ({ state.tree with nextPage }.insert entry.1
                    (entry.2.filter
                      (fun old => old.rowid != row.rowid))).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.TreePagesAccounted
                  dsimp only
                  let updatedChunk := entry.2.filter
                    (fun old => old.rowid != row.rowid)
                  have agrees :=
                    state.tree.root.insert_pathAgrees_of_noAllocation nextPage
                      entry.1 updatedChunk (by
                        simpa [updatedChunk, PersistentPageTree.Store.insert]
                          using noAllocation)
                  have accounted := treePagesAccounted_of_pathAgrees
                    replacement.schema entry.1 state.tree.root
                      (state.tree.root.insert nextPage entry.1
                        updatedChunk).1 pages agrees (by
                          simpa [updatedChunk,
                            PersistentPageTree.Store.insert] using pageResult)
                  simpa [updatedChunk, PersistentPageTree.Store.insert] using
                    accounted
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem delete?_encodabilityPreserved
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.EncodabilityPreserved := by
  unfold delete? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        split at success
        next =>
          split at success
          next noAllocation =>
            split at success
            next represents =>
              cases pageResult : CorePageCodec.encodeChunkPath
                  replacement.schema entry.1
                  ({ state.tree with nextPage }.insert entry.1
                    (entry.2.filter
                      (fun old => old.rowid != row.rowid))).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.EncodabilityPreserved
                  dsimp only
                  let updatedChunk := entry.2.filter
                    (fun old => old.rowid != row.rowid)
                  have agrees :=
                    state.tree.root.insert_pathAgrees_of_noAllocation nextPage
                      entry.1 updatedChunk (by
                        simpa [updatedChunk, PersistentPageTree.Store.insert]
                          using noAllocation)
                  have preserved := encodabilityPreserved_of_pathAgrees
                    replacement.schema entry.1 state.tree.root
                      (state.tree.root.insert nextPage entry.1
                        updatedChunk).1 pages agrees (by
                          simpa [updatedChunk,
                            PersistentPageTree.Store.insert] using pageResult)
                  simpa [updatedChunk, PersistentPageTree.Store.insert] using
                    preserved
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem delete?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold delete? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        split at success
        next =>
          split at success
          next =>
            split at success
            next =>
              cases pageResult : CorePageCodec.encodeChunkPath
                  replacement.schema entry.1
                  ({ state.tree with nextPage }.insert entry.1
                    (entry.2.filter
                      (fun old => old.rowid != row.rowid))).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.TreePagesSelected
                  dsimp only
                  let updatedChunk := entry.2.filter
                    (fun old => old.rowid != row.rowid)
                  simpa [updatedChunk, PersistentPageTree.Store.insert] using
                    treePagesSelected_of_path replacement.schema entry.1
                      (state.tree.root.insert nextPage entry.1
                        updatedChunk).1 pages (by
                          simpa [updatedChunk,
                            PersistentPageTree.Store.insert] using pageResult)
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem splitInsert?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.after.table = replacement := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next represents =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some_iff.mp success with
          ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem splitInsert?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  rw [delta.after.represents, splitInsert?_table success]

theorem splitInsert?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, deletedResult, success⟩
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

theorem splitInsert?_encodabilityPreserved
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.EncodabilityPreserved := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, deletedResult, success⟩
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

theorem splitInsert?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, deletedResult, success⟩
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

theorem mergeDelete?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.after.table = replacement := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next represents =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem mergeDelete?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  rw [delta.after.represents, mergeDelete?_table success]

theorem mergeDelete?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, deletedResult, success⟩
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

theorem mergeDelete?_encodabilityPreserved
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.EncodabilityPreserved := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, deletedResult, success⟩
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

theorem mergeDelete?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨deleted, deletedResult, success⟩
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

theorem replaceBetween?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.after.table = replacement := by
  unfold replaceBetween? at success
  split at success
  next =>
    injection success with equal
    subst delta
    rfl
  next =>
    split at success
    next =>
      cases inserted : firstInserted state.table.rows replacement.rows with
      | none => simp [inserted] at success
      | some row =>
          simp only [inserted, Option.bind_eq_bind, Option.bind] at success
          cases insertionResult : insert? state nextPage row replacement with
          | none =>
              rw [insertionResult] at success
              exact splitInsert?_table success
          | some candidate =>
              rw [insertionResult] at success
              simp only [Option.some.injEq] at success
              subst candidate
              exact insert?_table insertionResult
    next =>
      split at success
      next =>
        cases deleted : firstDeleted state.table.rows replacement.rows with
        | none => simp [deleted] at success
        | some row =>
            simp only [deleted, Option.bind_eq_bind, Option.bind] at success
            cases deletionResult : delete? state nextPage row replacement with
            | none =>
                rw [deletionResult] at success
                exact mergeDelete?_table success
            | some candidate =>
                rw [deletionResult] at success
                simp only [Option.some.injEq] at success
                subst candidate
                exact delete?_table deletionResult
      next =>
        split at success
        next => exact retainMany?_table success
        next =>
          cases difference : firstDifference state.table.rows replacement.rows with
          | none => simp [difference] at success
          | some row =>
              simp only [difference, Option.bind_eq_bind, Option.bind] at success
              cases replacementResult : replace? state nextPage row replacement with
              | some candidate =>
                  rw [replacementResult] at success
                  simp only [Option.some.injEq] at success
                  subst candidate
                  exact replace?_table replacementResult
              | none =>
                  rw [replacementResult] at success
                  exact replaceMany?_table success

end CoreChunkPageDelta

end SQLeanite
