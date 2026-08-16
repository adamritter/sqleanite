import SQLeanite.Core
import SQLeanite.CoreOverflow

namespace SQLeanite
namespace CoreChunkPageState

/-!
# Packed proof-carrying table pages

The generic verified 2-3 tree stores *page chunks*, not individual rows.  This
keeps its small, fully proved branching algorithm while making physical page
count proportional to SQLite leaf capacity rather than row count.  A chunk is
bounded at the byte-aware `chunkCapacityFor`, so one chunk fills at most one
SQLite leaf page.  The selected positive capacity is retained in each
proof-carrying `TableState`; bulk construction and later local splits therefore
use one policy rather than silently reverting to a fixed row count.
-/

abbrev Chunk := List Core.Row

def chunkCapacity : Nat := 16

/-- Exact arithmetic size of one serial-type varint and its payload.  Unlike
encoding a `RecordField`, this only inspects already-materialized byte-list
lengths and allocates no payload bytes. -/
def fieldSizes : FileFormat.RecordField → Nat × Nat
  | .null => (1, 0)
  | .integer width _ => (1, width.bytes)
  | .floatBits _ => (1, 8)
  | .constantZero | .constantOne => (1, 0)
  | .blob metadata payload | .text metadata payload =>
      (FileFormat.sqliteVarintSize metadata.code.val, payload.bytes.length)

/-- Exact encoded length of an inline table cell.  `rowRecordFields` matters:
it omits a hidden rowid and substitutes NULL for an INTEGER PRIMARY KEY, so a
schema-blind estimator wastes roughly half of each narrow-row leaf.  Overflow
cells occupy no more space than this inline length, making it a safe capacity
input for both cases. -/
def rowCellBound (schema : Core.Schema) (row : Core.Row) : Nat :=
  let sizes := (CoreRecord.rowRecordFields schema row).foldl
    (fun total field =>
      let size := fieldSizes field
      (total.1 + size.1, total.2 + size.2)) (0, 0)
  let recordBytes := FileFormat.recordHeaderSize sizes.1 + sizes.2
  FileFormat.sqliteVarintSize recordBytes +
    FileFormat.sqliteVarintSize row.rowid.toUnsigned + recordBytes

/-- Rows per chunk for one table, chosen so the encoder can always place a
leaf's cells on one page.

A wide physical leaf holds one chunk, so up to `capacity` cells must satisfy
`PhysicalCodec.PageFit 0`, which is
`8 + 2 * cells.length + totalCellBytes ≤ pageSize`. Bounding every cell by
`widest` makes `8 + capacity * (widest + 2) ≤ pageSize` sufficient, which is
what the division below solves for.

Chunking at a fixed sixteen rows was byte-blind. The module comment claimed the
codec "falls back cleanly" on wide rows, but it does not: `tableLeafPage?`
returns `none`, `encodeBulk` propagates it, and the CLI reports "general MVP
database exceeds the physical subset". A table of 512-byte rows was therefore
unloadable, and so was a table of 130-byte rows at exactly 32, 48 or 64 rows --
the counts that give some leaf a full sixteen-row pair. Narrow rows keep the
sixteen-row cap also left narrow-row pages mostly empty.  Capacity is now
limited only by the proved byte bound. -/
def chunkCapacityFor (schema : Core.Schema) (rows : List Core.Row) : Nat :=
  let widest := rows.foldl
    (fun bound row => max bound (rowCellBound schema row)) 0
  max 1 ((PhysicalCodec.pageSize - 8) / (widest + 2))

theorem chunkCapacityFor_pos (schema : Core.Schema) (rows : List Core.Row) :
    0 < chunkCapacityFor schema rows := by
  simp only [chunkCapacityFor, chunkCapacity]
  omega

def chunks : Nat → List α → List (List α)
  | 0, values => if values.isEmpty then [] else [values]
  | _ + 1, [] => []
  | capacity + 1, value :: values =>
      let input := value :: values
      input.take (capacity + 1) :: chunks (capacity + 1)
        (input.drop (capacity + 1))
  termination_by _ values => values.length
  decreasing_by
    simp only [input, List.length_drop, List.length_cons]
    omega

theorem flatten_chunks (capacity : Nat) (values : List α) :
    (chunks capacity values).flatten = values := by
  induction capacity, values using chunks.induct with
  | case1 values =>
      simp only [chunks]
      split <;> simp_all
  | case2 values empty => simp [chunks, empty]
  | case3 capacity => simp [chunks]
  | case4 capacity value values input induction =>
      simp only [chunks, List.flatten_cons]
      rw [induction, List.take_append_drop]

/-- Tail-recursive implementation of `chunks` used by compiled bulk builds.

The proof-facing `chunks` has one recursive frame per physical leaf chunk.  At
512-byte YCSB rows that exhausted the native stack around 130,000 rows even
though the resulting tree is shallow.  This loop carries the already produced
chunks in reverse order and is proved extensionally equal below. -/
def chunksGo : Nat → List α → List (List α) → List (List α)
  | 0, values, reversed =>
      if values.isEmpty then reversed.reverse
      else reversed.reverseAux [values]
  | _ + 1, [], reversed => reversed.reverse
  | capacity + 1, value :: values, reversed =>
      let input := value :: values
      chunksGo (capacity + 1) (input.drop (capacity + 1))
        (input.take (capacity + 1) :: reversed)
  termination_by _ values _ => values.length
  decreasing_by
    simp only [input, List.length_drop, List.length_cons]
    omega

def chunksTR (capacity : Nat) (values : List α) : List (List α) :=
  chunksGo capacity values []

theorem chunksGo_eq (capacity : Nat) (values : List α)
    (reversed : List (List α)) :
    chunksGo capacity values reversed = reversed.reverse ++ chunks capacity values := by
  induction capacity, values using chunks.induct generalizing reversed with
  | case1 values =>
      simp only [chunksGo, chunks]
      split
      · simp_all
      · simp [List.reverseAux_eq]
  | case2 values empty => simp [chunksGo, chunks, empty]
  | case3 capacity => simp [chunksGo, chunks]
  | case4 capacity value values input induction =>
      simp only [chunksGo, chunks]
      rw [induction]
      simp [input]

@[csimp] theorem chunks_eq_chunksTR :
    @chunks = @chunksTR := by
  funext α capacity values
  rw [chunksTR, chunksGo_eq]
  simp

def chunkKey? (chunk : Chunk) : Option Nat :=
  chunk.getLast?.map Core.Row.treeKey

def lastRows (rowChunks : List Chunk) : List Core.Row :=
  rowChunks.filterMap List.getLast?

theorem lastRows_sublist_flatten (rowChunks : List Chunk) :
    List.Sublist (lastRows rowChunks) rowChunks.flatten := by
  induction rowChunks with
  | nil => exact List.Sublist.slnil
  | cons chunk rowChunks induction =>
      unfold lastRows
      simp only [List.filterMap_cons, List.flatten_cons]
      cases last : chunk.getLast? with
      | none =>
          have empty : chunk = [] := List.getLast?_eq_none_iff.mp last
          simpa [empty, lastRows] using induction
      | some row =>
          rcases List.getLast?_eq_some_iff.mp last with ⟨front, equal⟩
          subst chunk
          simp only [List.getLast?_concat, Option.toList_some]
          exact (List.sublist_append_right front [row]).append induction

def entries? : List Chunk → Option (List (PagedBTree.Entry Chunk))
  | [] => some []
  | chunk :: rowChunks => do
    let key ← chunkKey? chunk
    let entries ← entries? rowChunks
    some ((key, chunk) :: entries)

/-- Every physical chunk entry is indexed by the key of its final row.  This
is retained as erased evidence by the wide store: localized append can then
raise the terminal separator without rescanning or comparing the table. -/
def EntriesWellKeyed (entries : List (PagedBTree.Entry Chunk)) : Prop :=
  ∀ entry ∈ entries, chunkKey? entry.2 = some entry.1

theorem entries?_wellKeyed {rowChunks : List Chunk}
    {entries : List (PagedBTree.Entry Chunk)}
    (success : entries? rowChunks = some entries) :
    EntriesWellKeyed entries := by
  induction rowChunks generalizing entries with
  | nil =>
      simp [entries?] at success
      subst entries
      simp [EntriesWellKeyed]
  | cons chunk rowChunks induction =>
      simp only [entries?] at success
      cases keyResult : chunkKey? chunk with
      | none => simp [keyResult] at success
      | some key =>
          simp only [keyResult, Option.bind_eq_bind, Option.bind] at success
          cases tailResult : entries? rowChunks with
          | none => simp [tailResult] at success
          | some tail =>
              simp only [tailResult, Option.some.injEq] at success
              subst entries
              intro entry member
              simp only [List.mem_cons] at member
              rcases member with rfl | later
              · exact keyResult
              · exact induction tailResult entry later

theorem entries?_projections {rowChunks : List Chunk}
    {entries : List (PagedBTree.Entry Chunk)}
    (success : entries? rowChunks = some entries) :
    entries.map (fun entry => entry.2) = rowChunks ∧
      entries.map (fun entry => entry.1) =
        (lastRows rowChunks).map Core.Row.treeKey := by
  induction rowChunks generalizing entries with
  | nil =>
      simp [entries?] at success
      subst entries
      simp [lastRows]
  | cons chunk rowChunks induction =>
      cases last : chunk.getLast? with
      | none => simp [entries?, chunkKey?, last] at success
      | some row =>
          cases tailResult : entries? rowChunks with
          | none => simp [entries?, chunkKey?, last, tailResult] at success
          | some tail =>
              simp [entries?, chunkKey?, last, tailResult] at success
              subst entries
              have tailProjection := induction tailResult
              simp [lastRows, last, tailProjection.1, tailProjection.2]

/-- Tail-recursive compiled implementation of `entries?`. -/
def entriesGo? : List Chunk → List (PagedBTree.Entry Chunk) →
    Option (List (PagedBTree.Entry Chunk))
  | [], reversed => some reversed.reverse
  | chunk :: rowChunks, reversed => do
      let key ← chunkKey? chunk
      entriesGo? rowChunks ((key, chunk) :: reversed)

def entriesTR? (rowChunks : List Chunk) :
    Option (List (PagedBTree.Entry Chunk)) :=
  entriesGo? rowChunks []

theorem entriesGo?_eq (rowChunks : List Chunk)
    (reversed : List (PagedBTree.Entry Chunk)) :
    entriesGo? rowChunks reversed =
      (entries? rowChunks).map (reversed.reverse ++ ·) := by
  induction rowChunks generalizing reversed with
  | nil => simp [entriesGo?, entries?]
  | cons chunk rowChunks induction =>
      simp only [entriesGo?, entries?]
      cases key : chunkKey? chunk with
      | none => simp [key]
      | some value =>
          simp only [Option.bind_eq_bind, Option.bind]
          rw [induction]
          cases tail : entries? rowChunks <;> simp [tail]

@[csimp] theorem entries?_eq_entriesTR? :
    entries? = entriesTR? := by
  funext rowChunks
  rw [entriesTR?, entriesGo?_eq]
  simp

theorem entries?_sorted (capacity : Nat) (table : Core.Table)
    {entries : List (PagedBTree.Entry Chunk)}
    (success : entries? (chunks capacity table.rows) = some entries) :
    PagedBTree.KeysStrictlySorted entries := by
  have flattenedOrdered :
      (chunks capacity table.rows).flatten.Pairwise Core.Row.keyLess := by
    simpa [flatten_chunks] using table.rowsWellFormed.2
  have lastOrdered :
      (lastRows (chunks capacity table.rows)).Pairwise Core.Row.keyLess :=
    flattenedOrdered.sublist (lastRows_sublist_flatten _)
  have keyOrdered :
      ((lastRows (chunks capacity table.rows)).map
        Core.Row.treeKey).Pairwise (fun left right => left < right) :=
    lastOrdered.map Core.Row.treeKey fun left right less =>
      (Core.Row.treeKey_lt_iff left right).2 less
  have projection := (entries?_projections success).2
  unfold PagedBTree.KeysStrictlySorted
  apply List.pairwise_map.mp
  rw [projection]
  exact keyOrdered

def Node.rows (node : PersistentPageTree.Node Chunk) : List Core.Row :=
  node.erase.toList.flatMap (fun entry => entry.2)

def Store.rows (store : PersistentPageTree.Store Chunk) : List Core.Row :=
  Node.rows store.root

structure TableState where
  table : Core.Table
  tree : PersistentPageTree.Store Chunk
  represents : Store.rows tree = table.rows
  capacity : Nat
  capacity_pos : 0 < capacity

/-- Change only the logical witness attached to a physical table.  This is the
critical abstraction seam for persistent topology: equal logical contents do
not require equal tree shapes. -/
def TableState.retarget (state : TableState) (table : Core.Table)
    (equivalent : state.table.Equiv table) : TableState :=
  { table
    tree := state.tree
    represents := state.represents.trans equivalent.rows_eq
    capacity := state.capacity
    capacity_pos := state.capacity_pos }

/-- Table-page topology depends on the schema and ordered rows, but not on
secondary-index metadata.  A validating open first reconstructs table pages
and only then restores indexes from their own physical trees, so this is the
precise equivalence needed to attach the final logical table without decoding
the table pages a second time. -/
def TableState.DataEquiv (left right : Core.Table) : Prop :=
  left.schema = right.schema ∧ left.rows = right.rows

instance (left right : Core.Table) : Decidable (TableState.DataEquiv left right) :=
  inferInstanceAs (Decidable (left.schema = right.schema ∧ left.rows = right.rows))

theorem TableState.DataEquiv.withoutIndexes_eq {left right : Core.Table}
    (equivalent : TableState.DataEquiv left right) :
    left.withoutIndexes = right.withoutIndexes := by
  have rebuilt := Core.Table.rebuild_withoutIndexes left
  rw [equivalent.1, equivalent.2,
    Core.Table.rebuild_withoutIndexes right] at rebuilt
  injection rebuilt with equal
  exact equal.symm

theorem table_withoutIndexes_eq_self_of_rebuild
    {schema : Core.Schema} {rows : List Core.Row} {table : Core.Table}
    (rebuilt : Core.Table.rebuild schema [] rows = .ok table) :
    table.withoutIndexes = table := by
  have rebuiltWithout := Core.Table.rebuild_withoutIndexes table
  have exact := Core.Table.rebuild_exact rebuilt
  rw [exact.1, exact.2.2, rebuilt] at rebuiltWithout
  injection rebuiltWithout with equal
  exact equal.symm

def TableState.retargetData (state : TableState) (table : Core.Table)
    (equivalent : TableState.DataEquiv state.table table) : TableState :=
  { table
    tree := state.tree
    represents := state.represents.trans equivalent.2
    capacity := state.capacity
    capacity_pos := state.capacity_pos }

@[simp] theorem TableState.retargetData_table (state : TableState)
    (table : Core.Table) (equivalent : TableState.DataEquiv state.table table) :
    (state.retargetData table equivalent).table = table := rfl

@[simp] theorem TableState.retargetData_tree (state : TableState)
    (table : Core.Table) (equivalent : TableState.DataEquiv state.table table) :
    (state.retargetData table equivalent).tree = state.tree := rfl

theorem TableState.retarget_table (state : TableState) (table : Core.Table)
    (equivalent : state.table.Equiv table) :
    (state.retarget table equivalent).table = table := rfl

theorem TableState.retarget_tree (state : TableState) (table : Core.Table)
    (equivalent : state.table.Equiv table) :
    (state.retarget table equivalent).tree = state.tree := rfl

def TableState.rootPage (state : TableState) : Nat := state.tree.root.rootId

def TableState.pageIds (state : TableState) : List Nat := state.tree.root.pageIds

theorem buildTree_rows (capacity : Nat) (rootPage : Nat) (table : Core.Table)
    {entries : List (PagedBTree.Entry Chunk)}
    (success : entries? (chunks capacity table.rows) = some entries) :
    let built := PersistentPageTree.Store.build rootPage entries
    let tree := PersistentPageTree.Store.ofTree rootPage built.root.erase
      built.rootValid
    Store.rows tree = table.rows := by
  dsimp only
  have builtRepresents := PersistentPageTree.Store.build_represents rootPage
    entries (entries?_sorted capacity table success)
  let built := PersistentPageTree.Store.build rootPage entries
  have identifiedRepresents := PersistentPageTree.Store.ofTree_represents
    rootPage built.root.erase built.rootValid
  unfold PersistentPageTree.Store.Represents at builtRepresents identifiedRepresents
  have treeEntries :
      (PersistentPageTree.Store.ofTree rootPage built.root.erase
        built.rootValid).root.erase.toList = entries :=
    identifiedRepresents.trans builtRepresents
  unfold Store.rows Node.rows
  rw [treeEntries, List.flatMap_def, (entries?_projections success).1,
    flatten_chunks]

def TableState.build? (rootPage : Nat) (table : Core.Table) :
    Option TableState :=
  let capacity := chunkCapacityFor table.schema table.rows
  let rowChunks := chunks capacity table.rows
  match result : entries? rowChunks with
  | none => none
  | some entries =>
      let built := PersistentPageTree.Store.build rootPage entries
      -- Bulk assignment is preorder so a file-backed pager can traverse with
      -- a forward cursor. Later mutations preserve these identities locally.
      let tree := PersistentPageTree.Store.ofTree rootPage built.root.erase
        built.rootValid
      some ⟨table, tree, buildTree_rows _ rootPage table result, capacity,
        chunkCapacityFor_pos table.schema table.rows⟩

def buildTables? : Nat → List Core.Table →
    Option (List TableState × Nat)
  | nextPage, [] => some ([], nextPage)
  | nextPage, table :: tables => do
      let head ← TableState.build? nextPage table
      let tail ← buildTables? head.tree.nextPage tables
      some (head :: tail.1, tail.2)

def tablePageIds (tables : List TableState) : List Nat :=
  tables.flatMap TableState.pageIds

/-- Global page-ID uniqueness implies pairwise separation between the page
sets owned by two different tables.  Localized commits use this to transport
an unchanged table without inspecting its bytes: a write selected from the
changed table cannot name one of the unchanged table's tree pages. -/
theorem pageIds_disjoint_of_nodup
    {tables : List TableState} (unique : (tablePageIds tables).Nodup) :
    ∀ left ∈ tables, ∀ right ∈ tables, left ≠ right →
      ∀ pageId, pageId ∈ left.pageIds → pageId ∉ right.pageIds := by
  induction tables with
  | nil => simp
  | cons head tail induction =>
      unfold tablePageIds at unique
      simp only [List.flatMap_cons] at unique
      have separated := List.pairwise_append.mp unique
      intro left leftMember right rightMember different pageId leftPage rightPage
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftTail
      · rcases rightMember with rfl | rightTail
        · exact different rfl
        · exact separated.2.2 pageId leftPage pageId
            (List.mem_flatMap.mpr ⟨right, rightTail, rightPage⟩) rfl
      · rcases rightMember with rfl | rightTail
        · exact separated.2.2 pageId rightPage pageId
            (List.mem_flatMap.mpr ⟨left, leftTail, leftPage⟩) rfl
        · exact induction separated.2.1 left leftTail right rightTail
            different pageId leftPage rightPage

theorem TableState.pageIds_length_le_tablePageIds {table : TableState} :
    ∀ {tables : List TableState}, table ∈ tables →
      table.pageIds.length ≤ (tablePageIds tables).length
  | [], member => by simp at member
  | head :: tables, member => by
      simp only [List.mem_cons] at member
      unfold tablePageIds
      simp only [List.flatMap_cons, List.length_append]
      rcases member with rfl | tailMember
      · omega
      · have bound := pageIds_length_le_tablePageIds tailMember
        unfold tablePageIds at bound
        omega

theorem TableState.build?_table {rootPage : Nat} {table : Core.Table}
    {state : TableState} (built : TableState.build? rootPage table = some state) :
    state.table = table := by
  simp only [TableState.build?] at built
  split at built
  next => contradiction
  next entries =>
    simp only [Option.some.injEq] at built
    subst state
    rfl

theorem TableState.build?_represents {rootPage : Nat} {table : Core.Table}
    {state : TableState} (built : TableState.build? rootPage table = some state) :
    Store.rows state.tree = table.rows := by
  rw [state.represents, TableState.build?_table built]

theorem TableState.build?_pageIds {rootPage : Nat} {table : Core.Table}
    {state : TableState} (built : TableState.build? rootPage table = some state) :
    state.pageIds = List.range' rootPage state.tree.root.erase.pageCount := by
  simp only [TableState.build?] at built
  split at built
  next => contradiction
  next entries =>
    simp only [Option.some.injEq] at built
    subst state
    unfold TableState.pageIds PersistentPageTree.Store.ofTree
    simp only
    rw [PersistentPageTree.identifyFrom_pageIds,
      PersistentPageTree.identifyFrom_erases]

theorem TableState.build?_nextPage {rootPage : Nat} {table : Core.Table}
    {state : TableState} (built : TableState.build? rootPage table = some state) :
    state.tree.nextPage = rootPage + state.tree.root.erase.pageCount := by
  simp only [TableState.build?] at built
  split at built
  next => contradiction
  next entries =>
    simp only [Option.some.injEq] at built
    subst state
    unfold PersistentPageTree.Store.ofTree
    simp only
    rw [PersistentPageTree.identifyFrom_nextPage,
      PersistentPageTree.identifyFrom_erases]

theorem buildTables?_tables : ∀ (nextPage : Nat) (tables : List Core.Table)
    (result : List TableState × Nat),
    buildTables? nextPage tables = some result →
      result.1.map (fun state => state.table) = tables
  | _, [], result, built => by
      simp only [buildTables?, Option.some.injEq] at built
      subst result
      rfl
  | nextPage, table :: tables, result, built => by
      simp only [buildTables?, Option.bind_eq_bind, Option.bind] at built
      cases headResult : TableState.build? nextPage table with
      | none => simp [headResult] at built
      | some head =>
          simp only [headResult] at built
          cases tailResult : buildTables? head.tree.nextPage tables with
          | none => simp [tailResult] at built
          | some tail =>
              simp only [tailResult, Option.some.injEq] at built
              subst result
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨TableState.build?_table headResult,
                buildTables?_tables head.tree.nextPage tables tail tailResult⟩

theorem buildTables?_interval : ∀ (nextPage : Nat)
    (tables : List Core.Table) (result : List TableState × Nat),
    buildTables? nextPage tables = some result →
      ∃ count, result.2 = nextPage + count ∧
        tablePageIds result.1 = List.range' nextPage count
  | nextPage, [], result, built => by
      simp only [buildTables?, Option.some.injEq] at built
      subst result
      exact ⟨0, rfl, rfl⟩
  | nextPage, table :: tables, result, built => by
      simp only [buildTables?, Option.bind_eq_bind, Option.bind] at built
      cases headResult : TableState.build? nextPage table with
      | none => simp [headResult] at built
      | some head =>
          simp only [headResult] at built
          cases tailResult : buildTables? head.tree.nextPage tables with
          | none => simp [tailResult] at built
          | some tail =>
              simp only [tailResult, Option.some.injEq] at built
              subst result
              obtain ⟨tailCount, tailNext, tailPages⟩ :=
                buildTables?_interval head.tree.nextPage tables tail tailResult
              let headCount := head.tree.root.erase.pageCount
              have headNext : head.tree.nextPage = nextPage + headCount :=
                TableState.build?_nextPage headResult
              refine ⟨headCount + tailCount, ?_, ?_⟩
              · simp only
                rw [tailNext, headNext]
                omega
              · unfold tablePageIds
                simp only [List.flatMap_cons]
                rw [TableState.build?_pageIds headResult]
                change List.range' nextPage headCount ++
                    tablePageIds tail.1 = _
                rw [tailPages, headNext]
                exact List.range'_append_1

structure State where
  database : Core.Database
  tables : List TableState
  tables_eq : tables.map (fun state => state.table) = database.tables
  nextPage : Nat
  freePages : List Nat := []

/-- Database table-name uniqueness lifts to the proof-carrying physical table
list.  In particular, the selected table in a one-table delta cannot occur
again in an unchanged prefix or suffix. -/
theorem State.tables_nodup (state : State) : state.tables.Nodup := by
  have names := state.database.tablesWellFormed
  unfold Core.TablesWellFormed at names
  rw [← state.tables_eq] at names
  simp only [List.map_map, Function.comp_apply] at names
  have tableNames := List.pairwise_map.mp names
  exact tableNames.imp (by
    intro left right different equal
    apply different
    rw [equal])

def State.activePageIds (state : State) : List Nat :=
  tablePageIds state.tables

def State.AllocationWellFormed (state : State) : Prop :=
  state.activePageIds.Nodup ∧
  (∀ pageId ∈ state.activePageIds, pageId < state.nextPage) ∧
  state.freePages.Nodup ∧
  (∀ pageId ∈ state.freePages, pageId < state.nextPage) ∧
  (∀ pageId ∈ state.freePages, pageId ∉ state.activePageIds) ∧
  (∀ pageId ∈ state.activePageIds, 1 < pageId) ∧
  (∀ pageId ∈ state.freePages, 1 < pageId)

instance (state : State) : Decidable state.AllocationWellFormed :=
  inferInstanceAs (Decidable
    (state.activePageIds.Nodup ∧
      (∀ pageId ∈ state.activePageIds, pageId < state.nextPage) ∧
      state.freePages.Nodup ∧
      (∀ pageId ∈ state.freePages, pageId < state.nextPage) ∧
      (∀ pageId ∈ state.freePages, pageId ∉ state.activePageIds) ∧
      (∀ pageId ∈ state.activePageIds, 1 < pageId) ∧
      (∀ pageId ∈ state.freePages, 1 < pageId)))

theorem State.AllocationWellFormed.active_after_catalog
    {state : State} (wellFormed : state.AllocationWellFormed) :
    ∀ pageId ∈ state.activePageIds, 1 < pageId :=
  wellFormed.2.2.2.2.2.1

theorem State.AllocationWellFormed.free_after_catalog
    {state : State} (wellFormed : state.AllocationWellFormed) :
    ∀ pageId ∈ state.freePages, 1 < pageId :=
  wellFormed.2.2.2.2.2.2

theorem State.AllocationWellFormed.free_not_active
    {state : State} (wellFormed : state.AllocationWellFormed) :
    ∀ pageId ∈ state.freePages, pageId ∉ state.activePageIds :=
  wellFormed.2.2.2.2.1

def State.build? (database : Core.Database) : Option State :=
  match result : buildTables? 2 database.tables with
  | none => none
  | some built => some {
      database
      tables := built.1
      tables_eq := buildTables?_tables 2 database.tables built result
      nextPage := built.2 }

/-- The packed physical tree represents every logical table in the database.
Unlike the former encoder check, this relation is populated by proofs from
the bulk builder and is erased before execution. -/
def State.Represents (state : State) (database : Core.Database) : Prop :=
  state.database = database ∧
    state.tables.map (fun table => table.table) = database.tables ∧
    ∀ table ∈ state.tables, Store.rows table.tree = table.table.rows

theorem State.build?_represents {database : Core.Database} {state : State}
    (built : State.build? database = some state) :
    state.Represents database := by
  unfold State.build? at built
  split at built
  next => contradiction
  next buildResult result =>
    simp only [Option.some.injEq] at built
    subst state
    refine ⟨rfl,
      buildTables?_tables 2 database.tables buildResult result, ?_⟩
    intro table _
    exact table.represents

theorem State.represents_self (state : State) :
    state.Represents state.database := by
  refine ⟨rfl, state.tables_eq, ?_⟩
  intro table _
  exact table.represents

theorem State.build?_interval {database : Core.Database} {state : State}
    (built : State.build? database = some state) :
    ∃ count, state.nextPage = 2 + count ∧
      tablePageIds state.tables = List.range' 2 count := by
  unfold State.build? at built
  split at built
  next => contradiction
  next buildResult result =>
    simp only [Option.some.injEq] at built
    subst state
    exact buildTables?_interval 2 database.tables buildResult result

theorem State.build?_allocationWellFormed {database : Core.Database}
    {state : State} (built : State.build? database = some state) :
    state.AllocationWellFormed := by
  unfold State.build? at built
  split at built
  next => contradiction
  next buildResult result =>
    simp only [Option.some.injEq] at built
    subst state
    obtain ⟨count, nextPage, pages⟩ :=
      buildTables?_interval 2 database.tables buildResult result
    unfold State.AllocationWellFormed State.activePageIds
    simp only
    rw [pages, nextPage]
    refine ⟨List.nodup_range', ?_, List.nodup_nil, ?_, ?_, ?_, ?_⟩
    · intro pageId member
      simp only [List.mem_range'_1] at member
      exact member.2
    · simp
    · simp
    · intro pageId member
      simp only [List.mem_range'_1] at member
      omega
    · simp

end CoreChunkPageState
end SQLeanite
