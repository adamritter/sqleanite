import SQLeanite.CorePageCodec.EncodeChunkPathSubsetEncodeChunkNode
import SQLeanite.PersistentPageTree.NodeDeleteCandidateRootId

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

structure TableDelta where
  before : CoreChunkPageState.TableState
  after : CoreChunkPageState.TableState
  chunkKey : Nat
  pages : List CorePageCodec.NumberedPage
  /-- Structural mutations may touch two old search paths.  Ordinary point
  mutations leave this absent and reconstruct their single old path. -/
  beforePages? : Option (List CorePageCodec.NumberedPage) := none
  freedPageNumbers : List Nat := []

/-- Every complete post-state tree page is either emitted by the delta or is
byte-identical to a page in the complete pre-state tree encoding.  The
post-state schema is used on both sides; schema preservation is a separate
database-level frame fact. -/
def TableDelta.TreePagesAccounted (delta : TableDelta) : Prop :=
  ∀ (beforePages afterPages : List CorePageCodec.NumberedPage),
    CorePageCodec.encodeChunkNode delta.after.table.schema
        delta.before.tree.root = some beforePages →
    CorePageCodec.encodeChunkNode delta.after.table.schema
        delta.after.tree.root = some afterPages →
    ∀ page ∈ afterPages, page ∈ delta.pages ∨ page ∈ beforePages

/-- Every selected page is an exact member of the complete post-state tree
encoding.  This is deliberately separate from `TreePagesAccounted`: together
they give the two directions required to preserve an image without a runtime
decode-and-compare pass. -/
def TableDelta.TreePagesSelected (delta : TableDelta) : Prop :=
  ∀ (afterPages : List CorePageCodec.NumberedPage),
    CorePageCodec.encodeChunkNode delta.after.table.schema
        delta.after.tree.root = some afterPages →
    ∀ page ∈ delta.pages, page ∈ afterPages

/-- A localized delta preserves total physical encodability.  This is stated
as a proof-only implication from the already represented pre-tree, so the live
writer never runs the full post-tree encoder merely to construct evidence. -/
def TableDelta.EncodabilityPreserved (delta : TableDelta) : Prop :=
  ∀ beforePages,
    CorePageCodec.encodeChunkNode delta.after.table.schema
        delta.before.tree.root = some beforePages →
    ∃ afterPages,
      CorePageCodec.encodeChunkNode delta.after.table.schema
        delta.after.tree.root = some afterPages

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

theorem treePagesAccounted_of_changedPhysical
    (schema : Core.Schema)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (encoded : (CorePageCodec.changedPhysicalChunkPagesFast before after).mapM
      (CorePageCodec.encodePhysicalChunkPage schema) = some pages) :
    ∀ (beforePages afterPages : List CorePageCodec.NumberedPage),
      CorePageCodec.encodeChunkNode schema before = some beforePages →
      CorePageCodec.encodeChunkNode schema after = some afterPages →
      ∀ page ∈ afterPages, page ∈ pages ∨ page ∈ beforePages := by
  rw [CorePageCodec.changedPhysicalChunkPagesFast_eq] at encoded
  intro beforePages afterPages beforeEncoded afterEncoded
  exact CorePageCodec.encodeChangedChunkPages_accounts schema before after
    beforePages afterPages pages beforeEncoded afterEncoded (by
      simpa [CorePageCodec.encodeChangedChunkPages] using encoded)

theorem treePagesAccounted_of_pathAgrees
    (schema : Core.Schema) (key : Nat)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (agrees : PersistentPageTree.Node.PathAgrees key before after)
    (encoded : CorePageCodec.encodeChunkPath schema key after = some pages) :
    ∀ (beforePages afterPages : List CorePageCodec.NumberedPage),
      CorePageCodec.encodeChunkNode schema before = some beforePages →
      CorePageCodec.encodeChunkNode schema after = some afterPages →
      ∀ page ∈ afterPages, page ∈ pages ∨ page ∈ beforePages := by
  intro beforePages afterPages beforeEncoded afterEncoded
  exact CorePageCodec.encodeChunkPath_accounts_of_pathAgrees schema key pages
    beforePages afterPages agrees encoded beforeEncoded afterEncoded

theorem treePagesSelected_of_changedPhysical
    (schema : Core.Schema)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (encoded : (CorePageCodec.changedPhysicalChunkPagesFast before after).mapM
      (CorePageCodec.encodePhysicalChunkPage schema) = some pages) :
    ∀ (afterPages : List CorePageCodec.NumberedPage),
      CorePageCodec.encodeChunkNode schema after = some afterPages →
      ∀ page ∈ pages, page ∈ afterPages := by
  rw [CorePageCodec.changedPhysicalChunkPagesFast_eq] at encoded
  intro afterPages afterEncoded
  exact CorePageCodec.encodeChangedChunkPages_subset schema before after
    afterPages pages afterEncoded (by
      simpa [CorePageCodec.encodeChangedChunkPages] using encoded)

theorem treePagesSelected_of_path
    (schema : Core.Schema) (key : Nat)
    (after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (encoded : CorePageCodec.encodeChunkPath schema key after = some pages) :
    ∀ (afterPages : List CorePageCodec.NumberedPage),
      CorePageCodec.encodeChunkNode schema after = some afterPages →
      ∀ page ∈ pages, page ∈ afterPages := by
  intro afterPages afterEncoded
  exact CorePageCodec.encodeChunkPath_subset_encodeChunkNode schema key after
    pages afterPages encoded afterEncoded

theorem encodabilityPreserved_of_changedPhysical
    (schema : Core.Schema)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (encoded : (CorePageCodec.changedPhysicalChunkPagesFast before after).mapM
      (CorePageCodec.encodePhysicalChunkPage schema) = some pages) :
    ∀ beforePages,
      CorePageCodec.encodeChunkNode schema before = some beforePages →
      ∃ afterPages,
        CorePageCodec.encodeChunkNode schema after = some afterPages := by
  rw [CorePageCodec.changedPhysicalChunkPagesFast_eq] at encoded
  intro beforePages beforeEncoded
  exact CorePageCodec.exists_encodeChunkNode_of_changed schema before after
    beforePages pages beforeEncoded (by
      simpa [CorePageCodec.encodeChangedChunkPages] using encoded)

theorem encodabilityPreserved_of_pathAgrees
    (schema : Core.Schema) (key : Nat)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (agrees : PersistentPageTree.Node.PathAgrees key before after)
    (encoded : CorePageCodec.encodeChunkPath schema key after = some pages) :
    ∀ beforePages,
      CorePageCodec.encodeChunkNode schema before = some beforePages →
      ∃ afterPages,
        CorePageCodec.encodeChunkNode schema after = some afterPages := by
  intro beforePages beforeEncoded
  exact CorePageCodec.exists_encodeChunkNode_of_pathAgrees schema key pages
    beforePages agrees encoded beforeEncoded

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
        let after : CoreChunkPageState.TableState := {
          table := replacement
          tree := updatedTree
          represents
          capacity := state.capacity
          capacity_pos := state.capacity_pos }
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
    if _room : entry.2.length < state.capacity then
      let updatedChunk := Core.orderedUpsert row entry.2
      let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
        { state.tree with nextPage }
      let updatedTree := allocating.insert entry.1 updatedChunk
      if _noAllocation : updatedTree.nextPage = nextPage then
        if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
          let after : CoreChunkPageState.TableState := {
            table := replacement
            tree := updatedTree
            represents
            capacity := state.capacity
            capacity_pos := state.capacity_pos }
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
    if _full : state.capacity < updated.length then
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
        let after : CoreChunkPageState.TableState := {
          table := replacement
          tree := updatedTree
          represents
          capacity := state.capacity
          capacity_pos := state.capacity_pos }
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
          let after : CoreChunkPageState.TableState := {
            table := replacement
            tree := updatedTree
            represents
            capacity := state.capacity
            capacity_pos := state.capacity_pos }
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
        let after : CoreChunkPageState.TableState := {
          table := replacement
          tree := updatedTree
          represents
          capacity := state.capacity
          capacity_pos := state.capacity_pos }
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

/-- The proof-oriented bulk replacement loop, named separately so page
identity can be related to its accumulator without unfolding a higher-order
`foldlM` application. -/
def replaceManyFold :
    List (PagedBTree.Entry CoreChunkPageState.Chunk) →
      (PersistentPageTree.Store CoreChunkPageState.Chunk × List Core.Row) →
      Option (PersistentPageTree.Store CoreChunkPageState.Chunk × List Core.Row)
  | [], accumulator => some accumulator
  | entry :: entries, accumulator => do
      let resolved ← replacementChunk? accumulator.2 entry.2
      let tree := if resolved.1 = entry.2 then accumulator.1
        else accumulator.1.insert entry.1 resolved.1
      replaceManyFold entries (tree, resolved.2)

theorem replaceManyFold_nextPage_le :
    ∀ {entries : List (PagedBTree.Entry CoreChunkPageState.Chunk)}
      {store updated : PersistentPageTree.Store CoreChunkPageState.Chunk}
      {rows remaining : List Core.Row},
      replaceManyFold entries (store, rows) = some (updated, remaining) →
      store.nextPage ≤ updated.nextPage
  | [], store, updated, rows, remaining, success => by
      simp only [replaceManyFold, Option.some.injEq, Prod.mk.injEq] at success
      exact success.1 ▸ Nat.le_refl _
  | entry :: entries, store, updated, rows, remaining, success => by
      unfold replaceManyFold at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨resolved, resolvedResult, success⟩
      split at success
      next => exact replaceManyFold_nextPage_le success
      next =>
        exact Nat.le_trans (store.nextPage_le_insert entry.1 resolved.1)
          (replaceManyFold_nextPage_le success)

end CoreChunkPageDelta

end SQLeanite
