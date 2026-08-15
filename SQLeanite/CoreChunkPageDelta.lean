import SQLeanite.CorePageCodec

namespace SQLeanite
namespace CoreChunkPageDelta


structure TableDelta where
  before : CoreChunkPageState.TableState
  after : CoreChunkPageState.TableState
  chunkKey : Nat
  pages : List CorePageCodec.NumberedPage
  /-- Structural mutations may touch two old search paths.  Ordinary point
  mutations leave this absent and reconstruct their single old path. -/
  beforePages? : Option (List CorePageCodec.NumberedPage) := none
  freedPageNumbers : List Nat := []

def maximumTreeKey? (node : PersistentPageTree.Node
    CoreChunkPageState.Chunk) : Option Nat :=
  node.erase.toList.getLast?.map (fun entry => entry.1)

/-- Locate the chunk whose upper rowid bound contains `key`.  Unlike ordinary
tree lookup, routing uses the maximum key of each left child because keys
inside a packed chunk are not individual tree entries. -/
def findChunkFor? (key : Nat) :
    PersistentPageTree.Node CoreChunkPageState.Chunk →
      Option (PagedBTree.Entry CoreChunkPageState.Chunk)
  | .leaf _ entries =>
      match entries.find? (fun entry => key ≤ entry.1) with
      | some entry => some entry
      | none => entries.getLast?
  | .branch2 _ left _ right => do
      let leftMax ← maximumTreeKey? left
      if key ≤ leftMax then findChunkFor? key left else findChunkFor? key right
  | .branch3 _ left _ middle _ right => do
      let leftMax ← maximumTreeKey? left
      if key ≤ leftMax then findChunkFor? key left
      else
        let middleMax ← maximumTreeKey? middle
        if key ≤ middleMax then findChunkFor? key middle
        else findChunkFor? key right

def replaceRow (target : Core.Row) (chunk : CoreChunkPageState.Chunk) :
    CoreChunkPageState.Chunk :=
  chunk.map fun row => if row.rowid = target.rowid then target else row

def firstDifference : List Core.Row → List Core.Row → Option Core.Row
  | [], [] => none
  | [], row :: _ => some row
  | _ :: _, [] => none
  | old :: olds, row :: rows =>
      if old = row then firstDifference olds rows else some row

/-- First row present only on the right of two rowid-ordered streams.  The old
implementation nested `find?` and `any`, making a tail insertion quadratic. -/
def firstInserted : List Core.Row → List Core.Row → Option Core.Row
  | [], [] => none
  | [], row :: _ => some row
  | _ :: _, [] => none
  | old :: olds, row :: rows =>
      if old.rowid = row.rowid then firstInserted olds rows
      else if row.rowid.value < old.rowid.value then some row
      else firstInserted olds (row :: rows)

/-- First row present only on the left, by the symmetric linear merge. -/
def firstDeleted : List Core.Row → List Core.Row → Option Core.Row
  | [], _ => none
  | old :: _, [] => some old
  | old :: olds, row :: rows =>
      if old.rowid = row.rowid then firstDeleted olds rows
      else if old.rowid.value < row.rowid.value then some old
      else firstDeleted (old :: olds) rows

theorem firstInserted_mem_after {before after : List Core.Row} {row : Core.Row}
    (found : firstInserted before after = some row) : row ∈ after := by
  induction before generalizing after with
  | nil =>
      cases after <;> simp [firstInserted] at found ⊢
      exact .inl found.symm
  | cons old olds induction =>
      cases after with
      | nil => simp [firstInserted] at found
      | cons next rows =>
          simp only [firstInserted] at found
          split at found
          next => exact List.Mem.tail next (induction found)
          next =>
            split at found
            next => simp_all
            next => exact induction found

theorem firstDeleted_mem_before {before after : List Core.Row} {row : Core.Row}
    (found : firstDeleted before after = some row) : row ∈ before := by
  induction after generalizing before with
  | nil =>
      cases before <;> simp [firstDeleted] at found ⊢
      exact .inl found.symm
  | cons next rows induction =>
      cases before with
      | nil => simp [firstDeleted] at found
      | cons old olds =>
          simp only [firstDeleted] at found
          split at found
          next => exact List.Mem.tail old (induction found)
          next =>
            split at found
            next => simp_all
            next => exact induction found

private def insertNumberedPage (page : CorePageCodec.NumberedPage) :
    List CorePageCodec.NumberedPage → List CorePageCodec.NumberedPage
  | [] => [page]
  | existing :: pages =>
      if existing.pageNumber = page.pageNumber then page :: pages
      else existing :: insertNumberedPage page pages

private def mergeNumberedPages (left right : List CorePageCodec.NumberedPage) :
    List CorePageCodec.NumberedPage :=
  right.foldl (fun pages page => insertNumberedPage page pages) left

/-- Encode selected identified nodes.  This is used only when topology changes;
the selected IDs are the old search paths plus freshly allocated pages, so the
write set remains logarithmic even though this proof-oriented collector walks
the in-memory tree to locate them. -/
def encodeChunkNodesWithIds (schema : Core.Schema) (ids : List Nat) :
    PersistentPageTree.Node CoreChunkPageState.Chunk →
      Option (List CorePageCodec.NumberedPage) := fun node =>
  ((CorePageCodec.physicalChunkPagesFast node).filter fun page =>
      ids.contains page.pageNumber).mapM
    (CorePageCodec.encodePhysicalChunkPage schema)

def replace? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _present : entry.2.any (fun old => old.rowid = row.rowid) then
    let updatedChunk := replaceRow row entry.2
    let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
      { state.tree with nextPage }
    let updatedTree := allocating.insert entry.1 updatedChunk
    if _noAllocation : updatedTree.nextPage = nextPage then
      if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
        let after : CoreChunkPageState.TableState :=
          ⟨replacement, updatedTree, represents⟩
        let pages ← CorePageCodec.encodeChunkPath replacement.schema
          entry.1 updatedTree.root
        some ⟨state, after, entry.1, pages, none, []⟩
      else none
    else none
  else none

def insert? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _fresh : !entry.2.any (fun old => old.rowid = row.rowid) then
    if _room : entry.2.length < CoreChunkPageState.chunkCapacity then
      let updatedChunk := Core.orderedUpsert row entry.2
      let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
        { state.tree with nextPage }
      let updatedTree := allocating.insert entry.1 updatedChunk
      if _noAllocation : updatedTree.nextPage = nextPage then
        if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
          let after : CoreChunkPageState.TableState :=
            ⟨replacement, updatedTree, represents⟩
          let pages ← CorePageCodec.encodeChunkPath replacement.schema
            entry.1 updatedTree.root
          some ⟨state, after, entry.1, pages, none, []⟩
        else none
      else none
    else none
  else none

/-- Split one full logical chunk and propagate the new entry through the
identified 2-3 tree. Existing nodes retain their page IDs; `Store.insert`
allocates only pages introduced by leaf/interior/root splits. -/
def splitInsert? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _fresh : !entry.2.any (fun old => old.rowid = row.rowid) then
    let updated := Core.orderedUpsert row entry.2
    if _full : CoreChunkPageState.chunkCapacity < updated.length then
      let splitAt := updated.length / 2
      let left := updated.take splitAt
      let right := updated.drop splitAt
      let leftKey ← CoreChunkPageState.chunkKey? left
      let rightKey ← CoreChunkPageState.chunkKey? right
      let deleting : PersistentPageTree.Store CoreChunkPageState.Chunk :=
        { state.tree with nextPage }
      -- The key of a physical chunk is its current maximum row key.  Merely
      -- replacing `entry.1` is wrong when an append raises that maximum: it
      -- leaves a stale routing bound even though flattening the chunks still
      -- yields the right rows. Remove the old keyed entry and insert both
      -- newly bounded halves.
      let deleted ← deleting.delete? entry.1
      let first := deleted.1.insert leftKey left
      let allocatedTree := first.insert rightKey right
      -- Removing the old full chunk can release exactly the pages needed by
      -- split propagation. Recycle them before exposing the delta so a table
      -- below a tail-owned index stays below that index.
      -- Recycling is an optimization, not a precondition for a valid split.
      -- A root/interior split can allocate more identities than deleting the
      -- old chunk releases; in that case retain the ordinary fresh layout.
      let reused := (allocatedTree.reuseFresh? nextPage deleted.2).getD
        (allocatedTree, deleted.2)
      let updatedTree := reused.1
      if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
        let changedPhysical := CorePageCodec.changedPhysicalChunkPagesFast
          state.tree.root updatedTree.root
        let changedIds := changedPhysical.map
          CorePageCodec.PhysicalChunkPage.pageNumber
        let beforeIds := changedIds ++ deleted.2
        let beforePages ← encodeChunkNodesWithIds state.table.schema beforeIds
          state.tree.root
        let pages ← changedPhysical.mapM
          (CorePageCodec.encodePhysicalChunkPage replacement.schema)
        let after : CoreChunkPageState.TableState :=
          ⟨replacement, updatedTree, represents⟩
        some ⟨state, after, entry.1, pages, some beforePages, reused.2⟩
      else none
    else none
  else none

def delete? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _present : entry.2.any (fun old => old.rowid = row.rowid) then
    let updatedChunk := entry.2.filter (fun old => old.rowid != row.rowid)
    if _nonempty : !updatedChunk.isEmpty then
      let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
        { state.tree with nextPage }
      let updatedTree := allocating.insert entry.1 updatedChunk
      if _noAllocation : updatedTree.nextPage = nextPage then
        if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
          let after : CoreChunkPageState.TableState :=
            ⟨replacement, updatedTree, represents⟩
          let pages ← CorePageCodec.encodeChunkPath replacement.schema
            entry.1 updatedTree.root
          some ⟨state, after, entry.1, pages, none, []⟩
        else none
      else none
    else none
  else none

/-- Remove a now-empty chunk with the stable-identity borrow/merge algorithm.
Absorbed physical pages are returned for SQLite freelist encoding. -/
def mergeDelete? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _present : entry.2.any (fun old => old.rowid = row.rowid) then
    let updatedChunk := entry.2.filter (fun old => old.rowid != row.rowid)
    if _empty : updatedChunk.isEmpty then
      let deleting : PersistentPageTree.Store CoreChunkPageState.Chunk :=
        { state.tree with nextPage }
      let deleted ← deleting.delete? entry.1
      let updatedTree := deleted.1
      if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
        -- Borrow and merge can modify a sibling that is not on the deleted
        -- key's search path.  Select by stable identity from the exact
        -- before/after page difference so every changed sibling is written,
        -- and include every absorbed page in the preimage set used by the
        -- rollback journal.
        let changedPhysical := CorePageCodec.changedPhysicalChunkPagesFast
          state.tree.root updatedTree.root
        let changedIds := changedPhysical.map
          CorePageCodec.PhysicalChunkPage.pageNumber
        let beforeIds := changedIds ++ deleted.2
        let beforePages ← encodeChunkNodesWithIds state.table.schema beforeIds
          state.tree.root
        let pages ← changedPhysical.mapM
          (CorePageCodec.encodePhysicalChunkPage replacement.schema)
        let after : CoreChunkPageState.TableState :=
          ⟨replacement, updatedTree, represents⟩
        some ⟨state, after, entry.1, pages, some beforePages, deleted.2⟩
      else none
    else none
  else none

/-- Resolve every old chunk row through the replacement primary tree.  This is
the bulk-UPDATE case: rowids and chunk boundaries remain fixed while one or
more payloads change. -/
def replacementChunk? (rows : List Core.Row)
    (chunk : CoreChunkPageState.Chunk) :
    Option (CoreChunkPageState.Chunk × List Core.Row) :=
  let replacement := rows.take chunk.length
  if replacement.length = chunk.length &&
      replacement.map (·.rowid) = chunk.map (·.rowid) then
    some (replacement, rows.drop chunk.length)
  else none

/-- Update all changed chunks without rebuilding table topology.  Stable page
identity selects the exact before/after paths for the rollback journal.  The
final representation equality is retained as the proof field of `TableState`,
so a primary-key change or missing row rejects this path and falls back. -/
def replaceMany? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (replacement : Core.Table) : Option TableDelta := do
  let row ← firstDifference state.table.rows replacement.rows
  let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
    { state.tree with nextPage }
  let updated ← state.tree.root.erase.toList.foldlM (fun accumulator entry => do
    let resolved ← replacementChunk? accumulator.2 entry.2
    let tree := if resolved.1 = entry.2 then accumulator.1
      else accumulator.1.insert entry.1 resolved.1
    some (tree, resolved.2)) (allocating, replacement.rows)
  if _consumed : updated.2 = [] then
    let updatedTree := updated.1
    if _noAllocation : updatedTree.nextPage = nextPage then
      if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
        -- Rowids and topology are fixed on the bulk-update path, so generic
        -- stable-page equality is already byte-complete and avoids computing
        -- derived separators that cannot change.
        let changedIds := (PersistentPageTree.changedPages state.tree.root
          updatedTree.root).map PersistentPageTree.Page.pageId
        let beforePages ← encodeChunkNodesWithIds state.table.schema changedIds
          state.tree.root
        let pages ← encodeChunkNodesWithIds replacement.schema changedIds
          updatedTree.root
        let after : CoreChunkPageState.TableState :=
          ⟨replacement, updatedTree, represents⟩
        some ⟨state, after, row.treeKey, pages, some beforePages, []⟩
      else none
    else none
  else none

theorem replaceMany?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.table = replacement := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
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
      let after : CoreChunkPageState.TableState :=
        ⟨replacement, updatedTree, represents⟩
      some ⟨state, after, row.treeKey, pages, some beforePages,
        updated.2.2⟩
    else none
  else none

theorem retainMany?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.after.table = replacement := by
  unfold retainMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
      rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
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
        dsimp only at success
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
        dsimp only at success
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
        dsimp only at success
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

theorem splitInsert?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.after.table = replacement := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next represents =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with
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

theorem mergeDelete?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.after.table = replacement := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next represents =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
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

structure AlignedTables (target : List Core.Table) where
  tables : List CoreChunkPageState.TableState
  aligned : tables.map (fun state => state.table) = target
  nextPage : Nat
  delta : Option TableDelta

def alignTables? : Nat → List CoreChunkPageState.TableState →
    (target : List Core.Table) → Option (AlignedTables target)
  | nextPage, [], [] => some ⟨[], rfl, nextPage, none⟩
  | nextPage, old :: olds, replacement :: replacements =>
      if same : old.table.contents = replacement.contents then do
        let tail ← alignTables? nextPage olds replacements
        let retained := old.retarget replacement same
        some ⟨retained :: tail.tables, by
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨CoreChunkPageState.TableState.retarget_table
            old replacement same, tail.aligned⟩, tail.nextPage,
          tail.delta⟩
      else
        match headResult : replaceBetween? old nextPage replacement with
        | none => none
        | some head =>
            match alignTables? head.after.tree.nextPage olds replacements with
            | none => none
            | some tail =>
                if _onlyChange : tail.delta.isNone then
                  some ⟨head.after :: tail.tables, by
                    simp [replaceBetween?_table headResult, tail.aligned],
                    tail.nextPage, some head⟩
                else none
  | _, _, _ => none

structure StateDelta where
  before : CoreChunkPageState.State
  after : CoreChunkPageState.State
  table : TableDelta

/-- Physical identity is deliberately separate from logical tree erasure.
`PersistentPageTree`'s semantic proofs forget page IDs, so this invariant rules
out duplicate active pages and prevents a released page from remaining live. -/
def TableDelta.IdentityWellFormed (delta : TableDelta) : Prop :=
  delta.after.tree.root.pageIds.Nodup ∧
    delta.freedPageNumbers.Nodup ∧
    ∀ pageId ∈ delta.freedPageNumbers,
      pageId ∉ delta.after.tree.root.pageIds

instance (delta : TableDelta) : Decidable delta.IdentityWellFormed :=
  inferInstanceAs (Decidable
    (delta.after.tree.root.pageIds.Nodup ∧
      delta.freedPageNumbers.Nodup ∧
      ∀ pageId ∈ delta.freedPageNumbers,
        pageId ∉ delta.after.tree.root.pageIds))

def indexImage (table : Core.Table) :
    List (Core.Index × List CoreDecode.IndexEntry) :=
  table.indexes.map fun index =>
    (index, CoreDecode.expectedIndexEntries table index)

def indexEntryOfRow (index : Core.Index) (row : Core.Row) :
    CoreDecode.IndexEntry :=
  ⟨row.value index.column, row.rowid⟩

def indexEntryLess (left right : CoreDecode.IndexEntry) : Bool :=
  match PhysicalQuery.compareValue left.value right.value with
  | .lt => true
  | .gt => false
  | .eq => left.rowid.value < right.rowid.value

def insertIndexEntry (entry : CoreDecode.IndexEntry) :
    List CoreDecode.IndexEntry → List CoreDecode.IndexEntry
  | [] => [entry]
  | candidate :: entries =>
      if indexEntryLess entry candidate then entry :: candidate :: entries
      else candidate :: insertIndexEntry entry entries

def integerIndexEntryKey (entry : CoreDecode.IndexEntry) : Int :=
  match entry.value with
  | .integer value => value.value
  | _ => 0

def integerIndexEntryLe (left right : CoreDecode.IndexEntry) : Bool :=
  decide (integerIndexEntryKey left < integerIndexEntryKey right ∨
    (integerIndexEntryKey left = integerIndexEntryKey right ∧
      left.rowid.value ≤ right.rowid.value))

def indexEntriesInteger (entries : List CoreDecode.IndexEntry) : Bool :=
  entries.all fun entry => CoreFile.valueIsInteger entry.value

def textIndexEntrySortKey (entry : CoreDecode.IndexEntry) :
    List UInt8 × Int :=
  let bytes := match entry.value with
    | .text value => value.bytes
    | _ => []
  (bytes, entry.rowid.value)

def textIndexEntryLe (left right : CoreDecode.IndexEntry) : Bool :=
  (compare (textIndexEntrySortKey left) (textIndexEntrySortKey right)).isLE

def indexEntriesText (entries : List CoreDecode.IndexEntry) : Bool :=
  entries.all fun entry => CoreFile.valueIsText entry.value

def sortIndexEntries (entries : List CoreDecode.IndexEntry) :
    List CoreDecode.IndexEntry :=
  if indexEntriesInteger entries then
    entries.mergeSort integerIndexEntryLe
  else if indexEntriesText entries then
    entries.mergeSort textIndexEntryLe
  else entries.foldl (fun sorted entry => insertIndexEntry entry sorted) []

theorem integerIndexRowLe_entry (index : Core.Index)
    (left right : Core.Row) :
    CoreFile.integerIndexRowLe index left right =
      integerIndexEntryLe (indexEntryOfRow index left)
        (indexEntryOfRow index right) := by
  rfl

theorem textIndexRowLe_entry (index : Core.Index)
    (left right : Core.Row) :
    CoreFile.textIndexRowLe index left right =
      textIndexEntryLe (indexEntryOfRow index left)
        (indexEntryOfRow index right) := by
  rfl

theorem indexEntriesInteger_map (index : Core.Index) (rows : List Core.Row) :
    indexEntriesInteger (rows.map (indexEntryOfRow index)) =
      rows.all (fun row => CoreFile.valueIsInteger (row.value index.column)) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      unfold indexEntriesInteger at induction ⊢
      simp only [List.map_cons, List.all_cons, indexEntryOfRow, induction]

theorem indexEntriesText_map (index : Core.Index) (rows : List Core.Row) :
    indexEntriesText (rows.map (indexEntryOfRow index)) =
      rows.all (fun row => CoreFile.valueIsText (row.value index.column)) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      unfold indexEntriesText at induction ⊢
      simp only [List.map_cons, List.all_cons, indexEntryOfRow, induction]

theorem map_insertIndexRow (index : Core.Index) (row : Core.Row) :
    ∀ rows,
    (CoreFile.insertIndexRow index row rows).map (indexEntryOfRow index) =
      insertIndexEntry (indexEntryOfRow index row)
        (rows.map (indexEntryOfRow index))
  | [] => rfl
  | candidate :: rows => by
      simp only [CoreFile.insertIndexRow, insertIndexEntry, List.map_cons]
      have comparison : indexEntryLess (indexEntryOfRow index row)
          (indexEntryOfRow index candidate) =
          CoreFile.indexRowLess index row candidate := rfl
      rw [comparison]
      split
      · rfl
      · simp only [List.map_cons, map_insertIndexRow index row rows]

theorem map_foldInsertIndexRow (index : Core.Index) :
    ∀ (rows accumulator : List Core.Row),
    (rows.foldl (fun sorted row => CoreFile.insertIndexRow index row sorted)
        accumulator).map (indexEntryOfRow index) =
      (rows.map (indexEntryOfRow index)).foldl
        (fun sorted entry => insertIndexEntry entry sorted)
        (accumulator.map (indexEntryOfRow index))
  | [], _ => rfl
  | row :: rows, accumulator => by
      simp only [List.foldl_cons, List.map_cons]
      rw [map_foldInsertIndexRow index rows
        (CoreFile.insertIndexRow index row accumulator)]
      rw [map_insertIndexRow]

theorem expectedIndexEntries_eq_sortSource (table : Core.Table)
    (index : Core.Index) :
    CoreDecode.expectedIndexEntries table index =
      sortIndexEntries (table.rows.map (indexEntryOfRow index)) := by
  unfold CoreDecode.expectedIndexEntries CoreFile.sortedIndexRows
    sortIndexEntries
  by_cases integers : CoreFile.indexValuesInteger table index = true
  · rw [if_pos integers]
    have sourceIntegers :
        indexEntriesInteger (table.rows.map (indexEntryOfRow index)) = true := by
      rw [indexEntriesInteger_map]
      exact integers
    rw [if_pos sourceIntegers]
    exact List.map_mergeSort fun left _ right _ =>
      integerIndexRowLe_entry index left right
  · rw [if_neg integers]
    have sourceNotIntegers :
        indexEntriesInteger (table.rows.map (indexEntryOfRow index)) ≠ true := by
      rw [indexEntriesInteger_map]
      exact integers
    rw [if_neg sourceNotIntegers]
    by_cases texts : CoreFile.indexValuesText table index = true
    · rw [if_pos texts]
      have sourceTexts :
          indexEntriesText (table.rows.map (indexEntryOfRow index)) = true := by
        rw [indexEntriesText_map]
        exact texts
      rw [if_pos sourceTexts]
      exact List.map_mergeSort fun left _ right _ =>
        textIndexRowLe_entry index left right
    · rw [if_neg texts]
      have sourceNotTexts :
          indexEntriesText (table.rows.map (indexEntryOfRow index)) ≠ true := by
        rw [indexEntriesText_map]
        exact texts
      rw [if_neg sourceNotTexts]
      simpa using map_foldInsertIndexRow index table.rows []

/-- Primary-order index inputs. Equality is linear to decide; unlike
`indexImage`, it does not sort every index twice on each table mutation. -/
def indexSourceImage (table : Core.Table) :
    List (Core.Index × List CoreDecode.IndexEntry) :=
  table.indexes.map fun index =>
    (index, table.rows.map (indexEntryOfRow index))

def sortIndexSourceImage
    (source : List (Core.Index × List CoreDecode.IndexEntry)) :
    List (Core.Index × List CoreDecode.IndexEntry) :=
  source.map fun pair => (pair.1, sortIndexEntries pair.2)

theorem indexImage_eq_sortIndexSourceImage (table : Core.Table) :
    indexImage table = sortIndexSourceImage (indexSourceImage table) := by
  unfold indexImage indexSourceImage sortIndexSourceImage
  rw [List.map_map]
  apply List.map_congr_left
  intro index _
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  exact expectedIndexEntries_eq_sortSource table index

def TableDelta.tablePagesSufficient (delta : TableDelta) : Bool :=
  delta.before.table.schema == delta.after.table.schema &&
    delta.before.table.indexes == delta.after.table.indexes &&
    (delta.before.table.indexes.isEmpty ||
      (delta.before.table.rows.length == delta.after.table.rows.length &&
        indexSourceImage delta.before.table == indexSourceImage delta.after.table))

/-- The linear source-image check is strong enough to leave physical index
pages untouched: deterministic logical sorting maps equal sources to the exact
same promoted-key index image. -/
theorem TableDelta.tablePagesSufficient_indexImage (delta : TableDelta)
    (sufficient : delta.tablePagesSufficient = true) :
    indexImage delta.before.table = indexImage delta.after.table := by
  by_cases empty : delta.before.table.indexes = []
  · simp [TableDelta.tablePagesSufficient, empty] at sufficient
    unfold indexImage
    rw [sufficient.2]
    simp [empty]
  · simp [TableDelta.tablePagesSufficient, empty] at sufficient
    rw [indexImage_eq_sortIndexSourceImage,
      indexImage_eq_sortIndexSourceImage, sufficient.2.2]

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
  rcases Option.bind_eq_some.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some.mp updated with
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
  rcases Option.bind_eq_some.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next identities =>
    injection updated with equal
    subst delta
    exact ⟨rfl, rfl⟩
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
  rcases Option.bind_eq_some.mp updated with
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
  rcases Option.bind_eq_some.mp updated with
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
  rcases Option.bind_eq_some.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_endpoints candidateResult
  next => contradiction

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

def beforeWrites (delta : TableDelta) :
    Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) := do
  let pages ← (match delta.beforePages? with
    | some pages => some pages
    | none => CorePageCodec.encodeChunkPath delta.before.table.schema
        delta.chunkKey delta.before.tree.root)
  pages.mapM numberedWrite?

end CoreChunkPageDelta
end SQLeanite
