import SQLeanite.CoreChunkPageState.Chunk
import SQLeanite.CoreFile.Page
import SQLeanite.WidePageTree.NumberedBranchesRootNePendingBytePage

namespace SQLeanite
namespace CoreWidePageState

/-!
# Proof-carrying high-fanout Core table state

This is the migration target for the live physical representation.  It reuses
the byte-budgeted chunks from `CoreChunkPageState`, but one `WidePageTree`
branch corresponds to one SQLite interior page and can own 256 children.
The former 2-3 store remains live until the matching byte codec and localized
mutation proofs are complete; keeping this state separate makes that cutover
atomic and leaves the public path green throughout the migration.
-/

abbrev Chunk := CoreChunkPageState.Chunk

def Node.rows (node : WidePageTree.Node Chunk) : List Core.Row :=
  node.toList.flatMap fun entry => entry.2

def Store.rows (store : WidePageTree.Store Chunk) : List Core.Row :=
  Node.rows store.root

structure TableState where
  table : Core.Table
  tree : WidePageTree.Store Chunk
  represents : Store.rows tree = table.rows
  wellKeyed : CoreChunkPageState.EntriesWellKeyed tree.toList
  capacity : Nat
  capacity_pos : 0 < capacity

def TableState.rootPage (state : TableState) : Nat :=
  state.tree.root.rootId

def TableState.pageIds (state : TableState) : List Nat :=
  state.tree.root.pageIds

def TableState.withNextPage (state : TableState) (nextPage : Nat) : TableState := {
  state with tree := { state.tree with nextPage := nextPage } }

@[simp] theorem TableState.withNextPage_table (state : TableState)
    (nextPage : Nat) : (state.withNextPage nextPage).table = state.table := rfl

@[simp] theorem TableState.withNextPage_rows (state : TableState)
    (nextPage : Nat) :
    Store.rows (state.withNextPage nextPage).tree = state.table.rows :=
  state.represents

theorem buildTree_rows (capacity startPage : Nat) (table : Core.Table)
    {entries : List (PagedBTree.Entry Chunk)}
    (entriesResult : CoreChunkPageState.entries?
      (CoreChunkPageState.chunks capacity table.rows) = some entries)
    {tree : WidePageTree.Store Chunk}
    (built : WidePageTree.Store.build? startPage entries
      (CoreChunkPageState.entries?_sorted capacity table entriesResult) =
        some tree) :
    Store.rows tree = table.rows := by
  unfold Store.rows Node.rows
  change tree.toList.flatMap (fun entry => entry.2) = table.rows
  rw [WidePageTree.Store.build?_toList built,
    List.flatMap_def, (CoreChunkPageState.entries?_projections entriesResult).1,
    CoreChunkPageState.flatten_chunks]

def TableState.build? (startPage : Nat) (table : Core.Table) :
    Option TableState :=
  let capacity := CoreChunkPageState.chunkCapacityFor table.schema table.rows
  let rowChunks := CoreChunkPageState.chunks capacity table.rows
  match entriesResult : CoreChunkPageState.entries? rowChunks with
  | none => none
  | some entries =>
      let ordered := CoreChunkPageState.entries?_sorted capacity table
        entriesResult
      match built : WidePageTree.Store.build? startPage entries ordered with
      | none => none
      | some tree => some {
          table
          tree
          represents := buildTree_rows capacity startPage table entriesResult built
          wellKeyed := by
            rw [WidePageTree.Store.build?_toList built]
            exact CoreChunkPageState.entries?_wellKeyed entriesResult
          capacity
          capacity_pos := CoreChunkPageState.chunkCapacityFor_pos table.schema table.rows }

theorem TableState.build?_table {startPage : Nat} {table : Core.Table}
    {state : TableState}
    (built : TableState.build? startPage table = some state) :
    state.table = table := by
  simp only [TableState.build?] at built
  split at built
  next => contradiction
  next entries =>
    split at built
    next => contradiction
    next tree =>
      injection built with equal
      subst state
      rfl

theorem TableState.build?_represents {startPage : Nat} {table : Core.Table}
    {state : TableState}
    (built : TableState.build? startPage table = some state) :
    Store.rows state.tree = table.rows := by
  rw [state.represents, TableState.build?_table built]

theorem TableState.build?_nextPage_ge {startPage : Nat} {table : Core.Table}
    {state : TableState}
    (built : TableState.build? startPage table = some state) :
    startPage ≤ state.tree.nextPage := by
  simp only [TableState.build?] at built
  split at built
  next => contradiction
  next entries entriesResult =>
    split at built
    next => contradiction
    next tree treeResult =>
      injection built with equal
      rw [← congrArg (fun candidate : TableState => candidate.tree.nextPage) equal]
      exact WidePageTree.Store.build?_nextPage_ge treeResult

def buildTables? : Nat → List Core.Table →
    Option (List TableState × Nat)
  | nextPage, [] => some ([], nextPage)
  | nextPage, table :: tables => do
      let head ← TableState.build? nextPage table
      let tail ← buildTables? head.tree.nextPage tables
      some (head :: tail.1, tail.2)

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

theorem buildTables?_nextPage_ge : ∀ (nextPage : Nat)
    (tables : List Core.Table) (result : List TableState × Nat),
    buildTables? nextPage tables = some result → nextPage ≤ result.2
  | nextPage, [], result, built => by
      simp only [buildTables?, Option.some.injEq] at built
      subst result
      exact Nat.le_refl nextPage
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
              exact Nat.le_trans (TableState.build?_nextPage_ge headResult)
                (buildTables?_nextPage_ge head.tree.nextPage tables tail
                  tailResult)

structure State where
  database : Core.Database
  tables : List TableState
  tables_eq : tables.map (fun state => state.table) = database.tables
  nextPage : Nat

/-- Cached homogeneous-index fact for the one-table/one-index live shape.
It is decided once when the physical state is loaded and then transported by
localized inserts.  Keeping the equation in `Prop` lets the executable reuse
the result without rescanning every logical row. -/
def State.SingleIndexValuesText (state : State) : Prop :=
  match state.tables with
  | [table] =>
      match table.table.indexes with
      | [index] => CoreFile.indexValuesText table.table index = true
      | _ => True
  | _ => True

instance (state : State) : Decidable state.SingleIndexValuesText := by
  unfold State.SingleIndexValuesText
  split
  next table =>
    split <;> infer_instance
  next => exact isTrue trivial

structure State.SingleIndexTextCertificate (state : State) : Type where
  exact : state.SingleIndexValuesText

def State.singleIndexValuesText? (state : State) :
    Option (state.SingleIndexTextCertificate) :=
  if exact : state.SingleIndexValuesText then some ⟨exact⟩ else none

theorem State.singleIndexValuesText_exact {state : State}
    (text : state.SingleIndexValuesText) {table : TableState}
    (tables : state.tables = [table]) {index : Core.Index}
    (indexes : table.table.indexes = [index]) :
    CoreFile.indexValuesText table.table index = true := by
  unfold State.SingleIndexValuesText at text
  simpa [tables, indexes] using text

theorem State.singleIndexValuesText_of_exact {state : State}
    {table : TableState} (tables : state.tables = [table])
    {index : Core.Index} (indexes : table.table.indexes = [index])
    (text : CoreFile.indexValuesText table.table index = true) :
    state.SingleIndexValuesText := by
  simpa [State.SingleIndexValuesText, tables, indexes] using text

def State.build? (database : Core.Database) : Option State :=
  match result : buildTables? 2 database.tables with
  | none => none
  | some built => some {
      database
      tables := built.1
      tables_eq := buildTables?_tables 2 database.tables built result
      nextPage := built.2 }

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
    refine ⟨rfl, buildTables?_tables 2 database.tables buildResult result, ?_⟩
    intro table _
    exact table.represents

theorem State.build?_nextPage_ge {database : Core.Database} {state : State}
    (built : State.build? database = some state) : 2 ≤ state.nextPage := by
  unfold State.build? at built
  split at built
  next => contradiction
  next result resultEq =>
    injection built with equal
    rw [← congrArg State.nextPage equal]
    exact buildTables?_nextPage_ge 2 database.tables result resultEq

/-- Reserve page identities through an external tail (currently generated
secondary indexes) without changing any table topology or abstraction. -/
def State.reserveThrough (state : State) (nextPage : Nat) : State := {
  database := state.database
  tables := state.tables.map (·.withNextPage nextPage)
  tables_eq := by simpa [List.map_map, Function.comp_def] using state.tables_eq
  nextPage }

theorem State.reserveThrough_represents (state : State) (nextPage : Nat) :
    (state.reserveThrough nextPage).Represents state.database := by
  refine ⟨rfl, ?_, ?_⟩
  · simpa [State.reserveThrough, List.map_map, Function.comp_def] using
      state.tables_eq
  · intro table member
    rcases List.mem_map.mp member with ⟨old, oldMember, rfl⟩
    exact old.represents

end CoreWidePageState
end SQLeanite
