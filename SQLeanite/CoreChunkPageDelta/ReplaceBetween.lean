import SQLeanite.CoreChunkPageDelta.ReplaceManyFoldPageIdsOfNoAllocation

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

def replaceBetween? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (replacement : Core.Table) : Option TableDelta :=
  if sameData : CoreChunkPageState.TableState.DataEquiv
      state.table replacement then
    let after := state.retargetData replacement sameData
    some ⟨state, after, 0, [], some [], []⟩
  else if replacement.rows.length = state.table.rows.length + 1 then do
    let row ← firstInserted state.table.rows replacement.rows
    match insert? state nextPage row replacement with
    | some delta => some delta
    | none => splitInsert? state nextPage row replacement
  else if state.table.rows.length = replacement.rows.length + 1 then do
    let row ← firstDeleted state.table.rows replacement.rows
    match delete? state nextPage row replacement with
    | some delta => some delta
    | none => mergeDelete? state nextPage row replacement
  else if replacement.rows.length < state.table.rows.length then
    retainMany? state nextPage replacement
  else do
      let row ← firstDifference state.table.rows replacement.rows
      match replace? state nextPage row replacement with
      | some delta => some delta
      | none => replaceMany? state nextPage replacement

/-- Secondary-index metadata does not alter table-page topology.  The delta
builder exposes that case explicitly, including empty tables where there is no
row available to use as a synthetic mutation witness. -/
theorem replaceBetween?_sameData (state : CoreChunkPageState.TableState)
    (nextPage : Nat) (replacement : Core.Table)
    (sameData : CoreChunkPageState.TableState.DataEquiv
      state.table replacement) :
    ∃ delta, replaceBetween? state nextPage replacement = some delta ∧
      delta.before = state ∧ delta.after.table = replacement ∧
      delta.after.tree = state.tree ∧ delta.pages = [] ∧
      delta.beforePages? = some [] ∧ delta.freedPageNumbers = [] := by
  let after := state.retargetData replacement sameData
  let delta : TableDelta := ⟨state, after, 0, [], some [], []⟩
  refine ⟨delta, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [replaceBetween?, sameData, delta, after]

theorem replace?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  unfold replace? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        split at success
        next =>
          split at success
          next represents =>
            cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                entry.1
                ({ state.tree with nextPage }.insert entry.1
                  (replaceRow row entry.2)).root with
            | none => simp [pageResult] at success
            | some pages =>
                simp only [pageResult, Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at success
                subst delta
                exact represents
          next => contradiction
        next => contradiction
      next => contradiction

theorem replace?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.after.table = replacement := by
  unfold replace? at success
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
            cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                entry.1 ({ state.tree with nextPage }.insert entry.1
                  (replaceRow row entry.2)).root with
            | none => simp [pageResult] at success
            | some pages =>
                simp only [pageResult, Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at success
                subst delta
                rfl
          next => contradiction
        next => contradiction
      next => contradiction

theorem replace?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold replace? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        split at success
        next noAllocation =>
          split at success
          next represents =>
            cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                entry.1 ({ state.tree with nextPage }.insert entry.1
                  (replaceRow row entry.2)).root with
            | none => simp [pageResult] at success
            | some pages =>
                simp only [pageResult, Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at success
                subst delta
                unfold TableDelta.TreePagesAccounted
                dsimp only
                have agrees :=
                  state.tree.root.insert_pathAgrees_of_noAllocation nextPage
                    entry.1 (replaceRow row entry.2) (by
                      simpa [PersistentPageTree.Store.insert] using
                        noAllocation)
                have accounted := treePagesAccounted_of_pathAgrees
                  replacement.schema entry.1 state.tree.root
                    (state.tree.root.insert nextPage entry.1
                      (replaceRow row entry.2)).1 pages agrees (by
                        simpa [PersistentPageTree.Store.insert] using
                          pageResult)
                simpa [PersistentPageTree.Store.insert] using accounted
          next => contradiction
        next => contradiction
      next => contradiction

theorem replace?_encodabilityPreserved
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.EncodabilityPreserved := by
  unfold replace? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        split at success
        next noAllocation =>
          split at success
          next represents =>
            cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                entry.1 ({ state.tree with nextPage }.insert entry.1
                  (replaceRow row entry.2)).root with
            | none => simp [pageResult] at success
            | some pages =>
                simp only [pageResult, Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at success
                subst delta
                unfold TableDelta.EncodabilityPreserved
                dsimp only
                have agrees :=
                  state.tree.root.insert_pathAgrees_of_noAllocation nextPage
                    entry.1 (replaceRow row entry.2) (by
                      simpa [PersistentPageTree.Store.insert] using
                        noAllocation)
                have preserved := encodabilityPreserved_of_pathAgrees
                  replacement.schema entry.1 state.tree.root
                    (state.tree.root.insert nextPage entry.1
                      (replaceRow row entry.2)).1 pages agrees (by
                        simpa [PersistentPageTree.Store.insert] using
                          pageResult)
                simpa [PersistentPageTree.Store.insert] using preserved
          next => contradiction
        next => contradiction
      next => contradiction

theorem replace?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold replace? at success
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
            cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                entry.1 ({ state.tree with nextPage }.insert entry.1
                  (replaceRow row entry.2)).root with
            | none => simp [pageResult] at success
            | some pages =>
                simp only [pageResult, Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at success
                subst delta
                unfold TableDelta.TreePagesSelected
                dsimp only
                simpa [PersistentPageTree.Store.insert] using
                  treePagesSelected_of_path replacement.schema entry.1
                    (state.tree.root.insert nextPage entry.1
                      (replaceRow row entry.2)).1 pages (by
                        simpa [PersistentPageTree.Store.insert] using
                          pageResult)
          next => contradiction
        next => contradiction
      next => contradiction

theorem insert?_correct {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows ∧
      delta.after.table = replacement := by
  unfold insert? at success
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
            next represents =>
              cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                  entry.1 ({ state.tree with nextPage }.insert entry.1
                    (Core.orderedUpsert row entry.2)).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  exact ⟨represents, rfl⟩
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem insert?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows :=
  (insert?_correct success).1

theorem insert?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.after.table = replacement :=
  (insert?_correct success).2

theorem insert?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold insert? at success
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
                    (Core.orderedUpsert row entry.2)).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.TreePagesAccounted
                  dsimp only
                  have agrees :=
                    state.tree.root.insert_pathAgrees_of_noAllocation nextPage
                      entry.1 (Core.orderedUpsert row entry.2) (by
                        simpa [PersistentPageTree.Store.insert] using
                          noAllocation)
                  have accounted := treePagesAccounted_of_pathAgrees
                    replacement.schema entry.1 state.tree.root
                      (state.tree.root.insert nextPage entry.1
                        (Core.orderedUpsert row entry.2)).1 pages agrees (by
                          simpa [PersistentPageTree.Store.insert] using
                            pageResult)
                  simpa [PersistentPageTree.Store.insert] using accounted
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem insert?_encodabilityPreserved
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.EncodabilityPreserved := by
  unfold insert? at success
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
                    (Core.orderedUpsert row entry.2)).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.EncodabilityPreserved
                  dsimp only
                  have agrees :=
                    state.tree.root.insert_pathAgrees_of_noAllocation nextPage
                      entry.1 (Core.orderedUpsert row entry.2) (by
                        simpa [PersistentPageTree.Store.insert] using
                          noAllocation)
                  have preserved := encodabilityPreserved_of_pathAgrees
                    replacement.schema entry.1 state.tree.root
                      (state.tree.root.insert nextPage entry.1
                        (Core.orderedUpsert row entry.2)).1 pages agrees (by
                          simpa [PersistentPageTree.Store.insert] using
                            pageResult)
                  simpa [PersistentPageTree.Store.insert] using preserved
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem insert?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold insert? at success
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
                    (Core.orderedUpsert row entry.2)).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.TreePagesSelected
                  dsimp only
                  simpa [PersistentPageTree.Store.insert] using
                    treePagesSelected_of_path replacement.schema entry.1
                      (state.tree.root.insert nextPage entry.1
                        (Core.orderedUpsert row entry.2)).1 pages (by
                          simpa [PersistentPageTree.Store.insert] using
                            pageResult)
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem delete?_correct {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows ∧
      delta.after.table = replacement := by
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
            next represents =>
              cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                  entry.1 ({ state.tree with nextPage }.insert entry.1
                    (entry.2.filter (fun old => old.rowid != row.rowid))).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  exact ⟨represents, rfl⟩
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem delete?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows :=
  (delete?_correct success).1

theorem delete?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.after.table = replacement :=
  (delete?_correct success).2

end CoreChunkPageDelta

end SQLeanite
