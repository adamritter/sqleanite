import SQLeanite.CoreEngine.ExecuteUncertifiedQueryWithCandidatesEqExecute
import SQLeanite.CoreWidePageState
import SQLeanite.WidePageTree.AppendStepToList

namespace SQLeanite
namespace CoreWidePageDelta

/-!
# Proof-carrying localized mutation of wide table pages

The public Core already proves that a successful generated-rowid INSERT is a
logical append.  This module consumes that equation as erased evidence and
updates only the terminal chunk/right spine of the high-fanout physical tree.
No table list is rebuilt or compared at runtime.
-/

theorem chunkKey?_append_singleton (chunk : CoreWidePageState.Chunk)
    (row : Core.Row) :
    CoreChunkPageState.chunkKey? (chunk ++ [row]) = some row.treeKey := by
  simp [CoreChunkPageState.chunkKey?]

theorem row_mem_store_of_entry {tree : WidePageTree.Store
    CoreWidePageState.Chunk} {entry : PagedBTree.Entry
      CoreWidePageState.Chunk} {row : Core.Row}
    (entryMember : entry ∈ tree.toList) (rowMember : row ∈ entry.2) :
    row ∈ CoreWidePageState.Store.rows tree := by
  unfold CoreWidePageState.Store.rows CoreWidePageState.Node.rows
  exact List.mem_flatMap.mpr ⟨entry, entryMember, rowMember⟩

theorem entry_key_lt_of_rows_after {state : CoreWidePageState.TableState}
    {row : Core.Row} (afterAll : ∀ existing ∈ state.table.rows,
      existing.rowid.value < row.rowid.value) :
    ∀ entry ∈ state.tree.toList, entry.1 < row.treeKey := by
  intro entry entryMember
  have keyed := state.wellKeyed entry entryMember
  unfold CoreChunkPageState.chunkKey? at keyed
  cases lastResult : entry.2.getLast? with
  | none => simp [lastResult] at keyed
  | some last =>
      have keyEq : last.treeKey = entry.1 := by
        exact Option.some.inj (by simpa [lastResult] using keyed)
      have lastMember : last ∈ entry.2 := List.mem_of_getLast? lastResult
      have tableMember : last ∈ state.table.rows := by
        rw [← state.represents]
        exact row_mem_store_of_entry entryMember lastMember
      have before := afterAll last tableMember
      rw [← keyEq]
      exact (Core.Row.treeKey_lt_iff last row).2 before

theorem pairwise_replace_last {entries initial : List
    (PagedBTree.Entry CoreWidePageState.Chunk)}
    {old replacement : PagedBTree.Entry CoreWidePageState.Chunk}
    (ordered : entries.Pairwise (fun left right => left.1 < right.1))
    (before : entries = initial ++ [old])
    (replacementAfter : ∀ entry ∈ entries, entry.1 < replacement.1) :
    (initial ++ [replacement]).Pairwise
      (fun left right => left.1 < right.1) := by
  rw [before, List.pairwise_append] at ordered
  rw [List.pairwise_append]
  refine ⟨ordered.1, by simp, ?_⟩
  intro left leftMember right rightMember
  simp only [List.mem_singleton] at rightMember
  subst right
  exact replacementAfter left (by rw [before]; simp [leftMember])

theorem replaceLast_rows {tree : WidePageTree.Store
    CoreWidePageState.Chunk} {old : PagedBTree.Entry
      CoreWidePageState.Chunk} {row : Core.Row}
    {ordered : ∀ initial previous, tree.toList = initial ++ [previous] →
      (initial ++ [(row.treeKey, old.2 ++ [row])]).Pairwise
        (fun left right => left.1 < right.1)}
    {result : WidePageTree.ReplacedLast tree
      (row.treeKey, old.2 ++ [row])}
    (_success : tree.replaceLast? (row.treeKey, old.2 ++ [row]) ordered =
      some result) (terminal : tree.root.lastEntry? = some old) :
    CoreWidePageState.Store.rows result.value =
      CoreWidePageState.Store.rows tree ++ [row] := by
  have oldExact := WidePageTree.Node.lastEntry?_witness terminal
  change tree.toList.getLast? = some old at oldExact
  have sameOld : result.old = old := by
    rw [result.before_eq] at oldExact
    simpa using oldExact
  unfold CoreWidePageState.Store.rows CoreWidePageState.Node.rows
  change result.value.toList.flatMap (fun entry => entry.2) =
    tree.toList.flatMap (fun entry => entry.2) ++ [row]
  rw [result.after_eq, result.before_eq, sameOld]
  simp [List.flatMap_append, List.append_assoc]

theorem replaceLast_wellKeyed {tree : WidePageTree.Store
    CoreWidePageState.Chunk} {old : PagedBTree.Entry
      CoreWidePageState.Chunk} {row : Core.Row}
    {ordered : ∀ initial previous, tree.toList = initial ++ [previous] →
      (initial ++ [(row.treeKey, old.2 ++ [row])]).Pairwise
        (fun left right => left.1 < right.1)}
    {result : WidePageTree.ReplacedLast tree
      (row.treeKey, old.2 ++ [row])}
    (wellKeyed : CoreChunkPageState.EntriesWellKeyed tree.toList)
    (_success : tree.replaceLast? (row.treeKey, old.2 ++ [row]) ordered =
      some result) (terminal : tree.root.lastEntry? = some old) :
    CoreChunkPageState.EntriesWellKeyed result.value.toList := by
  have oldExact := WidePageTree.Node.lastEntry?_witness terminal
  change tree.toList.getLast? = some old at oldExact
  have sameOld : result.old = old := by
    rw [result.before_eq] at oldExact
    simpa using oldExact
  intro entry member
  rw [result.after_eq] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with initialMember | rfl
  · apply wellKeyed entry
    rw [result.before_eq, sameOld]
    simp [initialMember]
  · exact chunkKey?_append_singleton old.2 row

theorem append_rows {tree : WidePageTree.Store CoreWidePageState.Chunk}
    {row : Core.Row} {after : ∀ old ∈ tree.toList,
      old.1 < row.treeKey}
    {result : WidePageTree.Appended tree (row.treeKey, [row])}
    (_success : tree.append? (row.treeKey, [row]) after = some result) :
    CoreWidePageState.Store.rows result.value =
      CoreWidePageState.Store.rows tree ++ [row] := by
  unfold CoreWidePageState.Store.rows CoreWidePageState.Node.rows
  change result.value.toList.flatMap (fun entry => entry.2) =
    tree.toList.flatMap (fun entry => entry.2) ++ [row]
  rw [result.toList_eq]
  simp [List.flatMap_append]

theorem append_wellKeyed {tree : WidePageTree.Store
    CoreWidePageState.Chunk} {row : Core.Row}
    {after : ∀ old ∈ tree.toList, old.1 < row.treeKey}
    {result : WidePageTree.Appended tree (row.treeKey, [row])}
    (wellKeyed : CoreChunkPageState.EntriesWellKeyed tree.toList)
    (_success : tree.append? (row.treeKey, [row]) after = some result) :
    CoreChunkPageState.EntriesWellKeyed result.value.toList := by
  intro entry member
  rw [result.toList_eq] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with oldMember | rfl
  · exact wellKeyed entry oldMember
  · simp [CoreChunkPageState.chunkKey?]

inductive AppendMode where
  | extendedTerminalChunk
  | appendedChunk
  deriving Repr, DecidableEq

/-- Exact result of one physical append.  `logicalRows` is the bridge to the
Core execution theorem; `rootStable` is the catalog frame fact used by the
localized byte commit. -/
structure TableAppend (before : CoreWidePageState.TableState)
    (replacement : Core.Table) (row : Core.Row) where
  after : CoreWidePageState.TableState
  mode : AppendMode
  logicalRows : CoreWidePageState.Store.rows after.tree =
    before.table.rows ++ [row]
  table_eq : after.table = replacement
  rootStable : after.tree.root.rootId = before.tree.root.rootId

def append? (state : CoreWidePageState.TableState)
    (replacement : Core.Table) (row : Core.Row)
    (rowsEq : replacement.rows = state.table.rows ++ [row])
    (afterAll : ∀ existing ∈ state.table.rows,
      existing.rowid.value < row.rowid.value) :
    Option (TableAppend state replacement row) :=
  let afterEntries : ∀ entry ∈ state.tree.toList,
      entry.1 < row.treeKey := entry_key_lt_of_rows_after afterAll
  match terminal : state.tree.root.lastEntry? with
  | some old =>
      if _room : old.2.length < state.capacity then
        let entry : PagedBTree.Entry CoreWidePageState.Chunk :=
          (row.treeKey, old.2 ++ [row])
        let ordered : ∀ initial previous,
            state.tree.toList = initial ++ [previous] →
            (initial ++ [entry]).Pairwise
              (fun left right => left.1 < right.1) := by
          intro initial previous before
          exact pairwise_replace_last state.tree.represents before
            afterEntries
        match changed : state.tree.replaceLast? entry ordered with
        | none => none
        | some result =>
            let physicalRows := replaceLast_rows changed terminal
            let logicalRows := physicalRows.trans
              (congrArg (· ++ [row]) state.represents)
            let after : CoreWidePageState.TableState := {
              table := replacement
              tree := result.value
              represents := logicalRows.trans rowsEq.symm
              wellKeyed := replaceLast_wellKeyed state.wellKeyed changed terminal
              capacity := state.capacity
              capacity_pos := state.capacity_pos }
            some {
              after
              mode := .extendedTerminalChunk
              logicalRows := logicalRows
              table_eq := rfl
              rootStable := result.rootId_eq }
      else
        match appended : state.tree.append? (row.treeKey, [row]) afterEntries with
        | none => none
        | some result =>
            let physicalRows := append_rows appended
            let logicalRows := physicalRows.trans
              (congrArg (· ++ [row]) state.represents)
            let after : CoreWidePageState.TableState := {
              table := replacement
              tree := result.value
              represents := logicalRows.trans rowsEq.symm
              wellKeyed := append_wellKeyed state.wellKeyed appended
              capacity := state.capacity
              capacity_pos := state.capacity_pos }
            some {
              after
              mode := .appendedChunk
              logicalRows := logicalRows
              table_eq := rfl
              rootStable := result.rootId_eq }
  | none =>
      match appended : state.tree.append? (row.treeKey, [row]) afterEntries with
      | none => none
      | some result =>
          let physicalRows := append_rows appended
          let logicalRows := physicalRows.trans
            (congrArg (· ++ [row]) state.represents)
          let after : CoreWidePageState.TableState := {
            table := replacement
            tree := result.value
            represents := logicalRows.trans rowsEq.symm
            wellKeyed := append_wellKeyed state.wellKeyed appended
            capacity := state.capacity
            capacity_pos := state.capacity_pos }
          some {
            after
            mode := .appendedChunk
            logicalRows := logicalRows
            table_eq := rfl
            rootStable := result.rootId_eq }

theorem append?_represents {state : CoreWidePageState.TableState}
    {replacement : Core.Table} {row : Core.Row}
    {rowsEq : replacement.rows = state.table.rows ++ [row]}
    {afterAll : ∀ existing ∈ state.table.rows,
      existing.rowid.value < row.rowid.value}
    {result : TableAppend state replacement row}
    (_success : append? state replacement row rowsEq afterAll = some result) :
    CoreWidePageState.Store.rows result.after.tree = replacement.rows :=
  result.after.represents.trans (congrArg Core.Table.rows result.table_eq)

/-- One-table database form used by the exact YCSB schema.  The list-shape
callbacks are proof arguments, so matching the two singleton lists is the
only runtime work above `append?`; no logical database comparison occurs. -/
structure StateAppend (before : CoreWidePageState.State)
    (replacement : Core.Database) (row : Core.Row) where
  after : CoreWidePageState.State
  table : CoreWidePageState.TableState
  replacementTable : Core.Table
  mutation : TableAppend table replacementTable row
  before_eq : before.tables = [table]
  database_eq : replacement.tables = [replacementTable]
  after_database : after.database = replacement
  after_tables : after.tables = [mutation.after]

def appendSingle? (state : CoreWidePageState.State)
    (database : Core.Database) (row : Core.Row)
    (rowsEq : ∀ before replacement,
      state.tables = [before] → database.tables = [replacement] →
      replacement.rows = before.table.rows ++ [row])
    (afterAll : ∀ before replacement,
      state.tables = [before] → database.tables = [replacement] →
      ∀ existing ∈ before.table.rows,
        existing.rowid.value < row.rowid.value) :
    Option (StateAppend state database row) :=
  match stateResult : state.tables, databaseResult : database.tables with
  | [before], [replacement] =>
      match changed : append? before replacement row
          (rowsEq before replacement stateResult databaseResult)
          (afterAll before replacement stateResult databaseResult) with
      | none => none
      | some mutation =>
          let after : CoreWidePageState.State := {
            database
            tables := [mutation.after]
            tables_eq := by
              rw [databaseResult]
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
              exact mutation.table_eq
            nextPage := mutation.after.tree.nextPage }
          some {
            after
            table := before
            replacementTable := replacement
            mutation
            before_eq := stateResult
            database_eq := databaseResult
            after_database := rfl
            after_tables := rfl }
  | _, _ => none

theorem appendSingle?_represents {state : CoreWidePageState.State}
    {database : Core.Database} {row : Core.Row}
    {rowsEq : ∀ before replacement,
      state.tables = [before] → database.tables = [replacement] →
      replacement.rows = before.table.rows ++ [row]}
    {afterAll : ∀ before replacement,
      state.tables = [before] → database.tables = [replacement] →
      ∀ existing ∈ before.table.rows,
        existing.rowid.value < row.rowid.value}
    {result : StateAppend state database row}
    (_success : appendSingle? state database row rowsEq afterAll = some result) :
    result.after.Represents database := by
  refine ⟨result.after_database, ?_, ?_⟩
  · rw [result.after_tables, result.database_eq]
    simp [result.mutation.table_eq]
  · intro table member
    rw [result.after_tables] at member
    simp only [List.mem_singleton] at member
    subst table
    exact result.mutation.after.represents

/-- A generated-rowid Core INSERT executed directly against the database owned
by the wide state, together with the exact localized physical append.  This is
the proof-carrying bridge used by the live writer; executing the command twice
is logarithmic and avoids any whole-database equality check. -/
structure ExecutedInsert (state : CoreWidePageState.State)
    (snapshot : Option Core.Database) (tableName : String)
    (values : List Core.Value) where
  next : Core.State
  result : Core.Result
  row : Core.Row
  append : StateAppend state next.database row
  execution : Core.execute
    { database := state.database, transactionSnapshot := snapshot }
    (.insert tableName values) = .ok (next, result)

def executeInsert? (state : CoreWidePageState.State)
    (snapshot : Option Core.Database) (tableName : String)
    (values : List Core.Value) :
    Option (ExecutedInsert state snapshot tableName values) :=
  let beforeState : Core.State := {
    database := state.database
    transactionSnapshot := snapshot }
  match found : state.database.findTable? tableName with
  | none => none
  | some table =>
      match hidden : table.schema.hasHiddenRowid with
      | false => none
      | true =>
          if automatic : values[table.schema.primaryKey]? = some .null then
            match created : table.createRow values with
            | .error _ => none
            | .ok row =>
              match execution : Core.execute beforeState (.insert tableName values) with
              | .error _ => none
              | .ok (next, result) =>
                match replacementFound : next.database.findTable? tableName with
                | none => none
                | some replacement =>
                  have afterAllTable : ∀ existing ∈ table.rows,
                      existing.rowid.value < row.rowid.value := by
                    rcases table.createRow_generated automatic created with
                      ⟨rowid, generated, rowidEq⟩
                    intro existing member
                    have greater := table.nextGeneratedRowid?_greater generated
                      existing member
                    simpa [rowidEq] using greater
                  have appendedRows : replacement.rows = table.rows ++ [row] := by
                    rcases Core.execute_insert_exact execution with
                      ⟨old, updated, insertedRow, oldFound, inserted,
                        rowValid, freshRowid, declaredFresh, updatedRows,
                        updatedFound, snapshotEq, resultEq, frame⟩
                    have oldEq : old = table := Option.some.inj
                      (oldFound.symm.trans found)
                    subst old
                    have rowEq : insertedRow = row := Except.ok.inj
                      (inserted.symm.trans created)
                    subst insertedRow
                    have updatedEq : updated = replacement := Option.some.inj
                      (updatedFound.symm.trans replacementFound)
                    subst updated
                    rw [updatedRows,
                      Core.orderedUpsert_eq_append_of_afterAll row table.rows
                        afterAllTable]
                  let rowsEq : ∀ before candidate,
                      state.tables = [before] → next.database.tables = [candidate] →
                        candidate.rows = before.table.rows ++ [row] := by
                    intro before candidate beforeEq candidateEq
                    have oldTables : state.database.tables = [before.table] := by
                      rw [← state.tables_eq, beforeEq]
                      rfl
                    have tableMember := Core.Database.findTable?_mem found
                    rw [oldTables] at tableMember
                    have tableEq : before.table = table := by
                      have : table = before.table := by
                        simpa only [List.mem_singleton] using tableMember
                      exact this.symm
                    have replacementMember :=
                      Core.Database.findTable?_mem replacementFound
                    rw [candidateEq] at replacementMember
                    have candidateEqual : candidate = replacement := by
                      have : replacement = candidate := by
                        simpa only [List.mem_singleton] using replacementMember
                      exact this.symm
                    rw [candidateEqual, tableEq]
                    exact appendedRows
                  let afterAll : ∀ before candidate,
                      state.tables = [before] → next.database.tables = [candidate] →
                        ∀ existing ∈ before.table.rows,
                          existing.rowid.value < row.rowid.value := by
                    intro before candidate beforeEq candidateEq existing member
                    have oldTables : state.database.tables = [before.table] := by
                      rw [← state.tables_eq, beforeEq]
                      rfl
                    have tableMember := Core.Database.findTable?_mem found
                    rw [oldTables] at tableMember
                    have tableEq : before.table = table := by
                      have : table = before.table := by
                        simpa only [List.mem_singleton] using tableMember
                      exact this.symm
                    rw [tableEq] at member
                    exact afterAllTable existing member
                  match changed : appendSingle? state next.database row rowsEq
                      afterAll with
                  | none => none
                  | some append => some {
                      next
                      result
                      row
                      append
                      execution }
          else none

end CoreWidePageDelta
end SQLeanite
