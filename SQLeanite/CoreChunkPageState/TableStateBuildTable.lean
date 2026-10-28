import SQLeanite.CoreChunkPageState.Chunk

namespace SQLeanite
namespace CoreChunkPageState

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
