import SQLeanite.PhysicalCodec
import SQLeanite.PersistentPageTree

namespace SQLeanite
namespace Core

abbrev Value := PhysicalCodec.Value
abbrev Integer := FileFormat.SignedInteger .eight

structure Column where
  name : String
  notNull : Bool := false
  integerPrimaryKey : Bool := false
  deriving DecidableEq, Repr

structure Schema where
  name : String
  columns : List Column
  primaryKey : Nat
  deriving DecidableEq, Repr

def namesUnique (names : List String) : Prop :=
  names.Pairwise (· ≠ ·)

instance (names : List String) : Decidable (namesUnique names) :=
  inferInstanceAs (Decidable (names.Pairwise (· ≠ ·)))

def Schema.WellFormed (schema : Schema) : Prop :=
  schema.name ≠ "" ∧
  schema.primaryKey < schema.columns.length ∧
  (schema.columns[schema.primaryKey]?).any (·.integerPrimaryKey) ∧
  (schema.columns.filter (·.integerPrimaryKey)).length = 1 ∧
  namesUnique (schema.columns.map (·.name)) ∧
  schema.columns.findIdx? (·.integerPrimaryKey) = some schema.primaryKey ∧
  (∀ column ∈ schema.columns, column.integerPrimaryKey → column.notNull)

instance (schema : Schema) : Decidable schema.WellFormed := by
  unfold Schema.WellFormed namesUnique
  infer_instance

theorem Schema.findIdx?_column_name (schema : Schema)
    (wellFormed : schema.WellFormed) (index : Nat)
    (bound : index < schema.columns.length) :
    schema.columns.findIdx?
      (fun candidate => candidate.name = schema.columns[index].name) = some index := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨bound, ?_, ?_⟩
  · simp
  · intro earlier earlierLt
    have earlierBound : earlier < schema.columns.length := Nat.lt_trans earlierLt bound
    have earlierNamesBound :
        earlier < (schema.columns.map (·.name)).length := by simpa
    have indexNamesBound :
        index < (schema.columns.map (·.name)).length := by simpa
    have unique := List.pairwise_iff_getElem.mp wellFormed.2.2.2.2.1
      earlier index earlierNamesBound indexNamesBound earlierLt
    simpa using unique

structure Index where
  name : String
  column : Nat
  deriving DecidableEq, Repr

def Index.WellFormed (schema : Schema) (index : Index) : Prop :=
  index.name ≠ "" ∧ index.column < schema.columns.length

instance (schema : Schema) (index : Index) : Decidable (index.WellFormed schema) :=
  by unfold Index.WellFormed; infer_instance

structure Row where
  rowid : Integer
  values : List Value
  deriving DecidableEq

def columnAccepts (column : Column) (value : Value) : Prop :=
  column.notNull = true → value ≠ .null

instance (column : Column) (value : Value) : Decidable (columnAccepts column value) :=
  by unfold columnAccepts; infer_instance

def columnAcceptsBool (column : Column) (value : Value) : Bool :=
  !column.notNull || value != .null

theorem columnAcceptsBool_iff (column : Column) (value : Value) :
    columnAcceptsBool column value = true ↔ columnAccepts column value := by
  unfold columnAcceptsBool columnAccepts
  cases notNull : column.notNull <;> simp_all

def Row.WellFormed (schema : Schema) (row : Row) : Prop :=
  row.values.length = schema.columns.length ∧
  row.values[schema.primaryKey]? = some (.integer row.rowid) ∧
  (schema.columns.zip row.values).all
    (fun pair => columnAcceptsBool pair.1 pair.2) = true

instance (schema : Schema) (row : Row) : Decidable (row.WellFormed schema) :=
  by unfold Row.WellFormed; infer_instance

def Row.keyLess (left right : Row) : Prop :=
  left.rowid.value < right.rowid.value

instance (left right : Row) : Decidable (Row.keyLess left right) :=
  by unfold Row.keyLess; infer_instance

/-- Bias a signed 64-bit integer into the natural key space without changing
order. This is the routing key shared by logical rows, persisted index rowids,
and the primary tree. -/
def Integer.treeKey (integer : Integer) : Nat :=
  (integer.value + Int.ofNat FileFormat.IntegerWidth.eight.midpoint).toNat

def Row.treeKey (row : Row) : Nat := row.rowid.treeKey

theorem Integer.treeKey_int (integer : Integer) :
    Int.ofNat integer.treeKey =
      integer.value + Int.ofNat FileFormat.IntegerWidth.eight.midpoint := by
  unfold Integer.treeKey
  exact Int.toNat_of_nonneg (by
    have lower := integer.lowerBound
    omega)

theorem Integer.treeKey_eq_iff (left right : Integer) :
    left.treeKey = right.treeKey ↔ left.value = right.value := by
  constructor
  · intro equal
    have coerced := congrArg Int.ofNat equal
    rw [left.treeKey_int, right.treeKey_int] at coerced
    omega
  · intro equal
    unfold Integer.treeKey
    rw [equal]

theorem Row.treeKey_int (row : Row) :
    Int.ofNat row.treeKey =
      row.rowid.value + Int.ofNat FileFormat.IntegerWidth.eight.midpoint := by
  exact row.rowid.treeKey_int

theorem Row.treeKey_lt_iff (left right : Row) :
    left.treeKey < right.treeKey ↔ left.rowid.value < right.rowid.value := by
  constructor
  · intro less
    have coerced : Int.ofNat left.treeKey < Int.ofNat right.treeKey :=
      Int.ofNat_lt.mpr less
    rw [left.treeKey_int, right.treeKey_int] at coerced
    omega
  · intro less
    apply Int.ofNat_lt.mp
    change Int.ofNat left.treeKey < Int.ofNat right.treeKey
    rw [left.treeKey_int, right.treeKey_int]
    omega

theorem Row.treeKey_eq_iff (left right : Row) :
    left.treeKey = right.treeKey ↔ left.rowid.value = right.rowid.value := by
  exact Integer.treeKey_eq_iff left.rowid right.rowid

def treeEntries (rows : List Row) :
    List (RecursiveBPlusTree.Entry Row) :=
  rows.map fun row => (row.treeKey, row)

theorem treeEntries_sorted {rows : List Row}
    (sorted : rows.Pairwise Row.keyLess) :
    PagedBTree.KeysStrictlySorted (treeEntries rows) := by
  unfold treeEntries PagedBTree.KeysStrictlySorted
  change (rows.map fun row => (row.treeKey, row)).Pairwise
    (fun left right : Nat × Row => left.1 < right.1)
  apply List.pairwise_map.mpr
  exact sorted.imp fun less => (Row.treeKey_lt_iff _ _).2 less

def IndexesWellFormed (schema : Schema) (indexes : List Index) : Prop :=
  (∀ index ∈ indexes, index.WellFormed schema) ∧
  namesUnique (indexes.map (·.name))

instance (schema : Schema) (indexes : List Index) :
    Decidable (IndexesWellFormed schema indexes) := by
  unfold IndexesWellFormed namesUnique Index.WellFormed
  infer_instance

def RowsWellFormed (schema : Schema) (rows : List Row) : Prop :=
  (∀ row ∈ rows, row.WellFormed schema) ∧ rows.Pairwise Row.keyLess

/-- A linear-time decision form of `RowsWellFormed`.  Checking every pair in
an ordered row list made validation quadratic even though integer order is
transitive.  Adjacent comparisons carry exactly the same information. -/
def RowsWellFormedAdjacent (schema : Schema) : List Row → Prop
  | [] => True
  | [row] => row.WellFormed schema
  | row :: next :: rows =>
      row.WellFormed schema ∧ Row.keyLess row next ∧
        RowsWellFormedAdjacent schema (next :: rows)

def decideRowsWellFormedAdjacent (schema : Schema) :
    (rows : List Row) → Decidable (RowsWellFormedAdjacent schema rows)
  | [] => isTrue trivial
  | [row] => by
      exact inferInstanceAs (Decidable (row.WellFormed schema))
  | row :: next :: rows =>
      let rowValid : Decidable (row.WellFormed schema) := inferInstance
      let ordered : Decidable (Row.keyLess row next) := inferInstance
      let tail := decideRowsWellFormedAdjacent schema (next :: rows)
      @instDecidableAnd (row.WellFormed schema)
        (Row.keyLess row next ∧ RowsWellFormedAdjacent schema (next :: rows))
        rowValid
        (@instDecidableAnd (Row.keyLess row next)
          (RowsWellFormedAdjacent schema (next :: rows)) ordered tail)
termination_by rows => rows.length

instance (schema : Schema) (rows : List Row) :
    Decidable (RowsWellFormedAdjacent schema rows) :=
  decideRowsWellFormedAdjacent schema rows

theorem Row.keyLess_trans {first second third : Row}
    (left : Row.keyLess first second) (right : Row.keyLess second third) :
    Row.keyLess first third := by
  exact Int.lt_trans left right

private theorem keyLess_all_of_cons {first second : Row} {rows : List Row}
    (head : Row.keyLess first second)
    (tail : (second :: rows).Pairwise Row.keyLess) :
    ∀ row ∈ second :: rows, Row.keyLess first row := by
  intro row member
  rcases List.pairwise_cons.mp tail with ⟨secondBefore, _⟩
  simp only [List.mem_cons] at member
  cases member with
  | inl equal => simpa [equal] using head
  | inr later =>
      exact Row.keyLess_trans head (secondBefore row later)

theorem rowsWellFormedAdjacent_iff (schema : Schema) (rows : List Row) :
    RowsWellFormedAdjacent schema rows ↔ RowsWellFormed schema rows := by
  induction rows with
  | nil => simp [RowsWellFormedAdjacent, RowsWellFormed]
  | cons row rows induction =>
      cases rows with
      | nil => simp [RowsWellFormedAdjacent, RowsWellFormed]
      | cons next rows =>
          constructor
          · intro adjacent
            rcases adjacent with ⟨rowValid, head, tailAdjacent⟩
            have tail := induction.mp tailAdjacent
            refine ⟨?_, ?_⟩
            · intro candidate member
              simp only [List.mem_cons] at member
              cases member with
              | inl equal => simpa [equal] using rowValid
              | inr later => exact tail.1 candidate (by simpa using later)
            · exact List.pairwise_cons.mpr
                ⟨keyLess_all_of_cons head tail.2, tail.2⟩
          · intro wellFormed
            rcases wellFormed with ⟨allValid, ordered⟩
            rcases List.pairwise_cons.mp ordered with ⟨rowBefore, tailOrdered⟩
            refine ⟨allValid row (by simp), rowBefore next (by simp), ?_⟩
            apply induction.mpr
            exact ⟨fun candidate member =>
              allValid candidate (by simp [member]), tailOrdered⟩

instance (schema : Schema) (rows : List Row) :
    Decidable (RowsWellFormed schema rows) :=
  decidable_of_iff (RowsWellFormedAdjacent schema rows)
    (rowsWellFormedAdjacent_iff schema rows)

def storedRows (tree : PersistentPageTree.Store Row) : List Row :=
  tree.root.erase.toList.map (fun entry => entry.2)

def RowTreeWellKeyed (tree : PersistentPageTree.Store Row) : Prop :=
  tree.Represents (treeEntries (storedRows tree))

structure Table where
  schema : Schema
  indexes : List Index := []
  rowTree : PersistentPageTree.Store Row
  rowTreeWellKeyed : RowTreeWellKeyed rowTree
  schemaWellFormed : schema.WellFormed
  indexesWellFormed : IndexesWellFormed schema indexes
  rowsWellFormed : RowsWellFormed schema (storedRows rowTree)

/-- The sole logical row view.  Rows are no longer stored alongside the tree:
they are the abstraction of the proof-carrying persistent representation. -/
def Table.rows (table : Table) : List Row := storedRows table.rowTree

def buildRowTree (rows : List Row) : PersistentPageTree.Store Row :=
  PersistentPageTree.Store.build 0 (treeEntries rows)

theorem buildRowTree_rows {rows : List Row} (sorted : rows.Pairwise Row.keyLess) :
    storedRows (buildRowTree rows) = rows := by
  have represented := PersistentPageTree.Store.build_represents 0
    (treeEntries rows) (treeEntries_sorted sorted)
  unfold storedRows buildRowTree
  rw [represented]
  simp [treeEntries, List.map_map, Function.comp_def]

theorem buildRowTree_wellKeyed {rows : List Row}
    (sorted : rows.Pairwise Row.keyLess) :
    RowTreeWellKeyed (buildRowTree rows) := by
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents
  have represented := PersistentPageTree.Store.build_represents 0
    (treeEntries rows) (treeEntries_sorted sorted)
  unfold PersistentPageTree.Store.Represents at represented
  unfold buildRowTree
  rw [represented]
  change treeEntries rows = treeEntries (storedRows (buildRowTree rows))
  rw [buildRowTree_rows sorted]

def Table.rebuild (schema : Schema) (indexes : List Index) (rows : List Row) :
    Except String Table :=
  if schemaWF : schema.WellFormed then
    if indexesWF : IndexesWellFormed schema indexes then
      if rowsWF : RowsWellFormed schema rows then
        .ok {
          schema
          indexes
          rowTree := buildRowTree rows
          rowTreeWellKeyed := buildRowTree_wellKeyed rowsWF.2
          schemaWellFormed := schemaWF
          indexesWellFormed := indexesWF
          rowsWellFormed := by
            rw [buildRowTree_rows rowsWF.2]
            exact rowsWF }
      else .error "rows violate the verified table schema"
    else .error "invalid verified index metadata"
  else .error "invalid verified table schema"

theorem Table.rebuild_exact {schema : Schema} {indexes : List Index}
    {rows : List Row} {table : Table}
    (success : Table.rebuild schema indexes rows = .ok table) :
    table.schema = schema ∧ table.indexes = indexes ∧ table.rows = rows := by
  unfold Table.rebuild at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success
  next rowsWF =>
    injection success with equal
    subst table
    exact ⟨rfl, rfl, buildRowTree_rows rowsWF.2⟩
  next => contradiction

def Table.withoutIndexes (table : Table) : Table := {
  table with
  indexes := []
  rowTree := buildRowTree table.rows
  rowTreeWellKeyed := buildRowTree_wellKeyed table.rowsWellFormed.2
  indexesWellFormed := by simp [IndexesWellFormed, namesUnique]
  rowsWellFormed := by
    change RowsWellFormed table.schema
      (storedRows (buildRowTree (storedRows table.rowTree)))
    rw [buildRowTree_rows table.rowsWellFormed.2]
    exact table.rowsWellFormed }

@[simp] theorem Table.withoutIndexes_schema (table : Table) :
    table.withoutIndexes.schema = table.schema := rfl

@[simp] theorem Table.withoutIndexes_rows (table : Table) :
    table.withoutIndexes.rows = table.rows := by
  exact buildRowTree_rows table.rowsWellFormed.2

theorem Table.rebuild_withoutIndexes (table : Table) :
    Table.rebuild table.schema [] table.rows = .ok table.withoutIndexes := by
  unfold Table.rebuild
  rw [dif_pos table.schemaWellFormed]
  rw [dif_pos (by simp [IndexesWellFormed, namesUnique])]
  split
  next => congr 1
  next invalid => exact False.elim (invalid table.rowsWellFormed)

def Table.canonicalize (table : Table) : Table := {
  table with
  rowTree := buildRowTree table.rows
  rowTreeWellKeyed := buildRowTree_wellKeyed table.rowsWellFormed.2
  rowsWellFormed := by
    change RowsWellFormed table.schema
      (storedRows (buildRowTree (storedRows table.rowTree)))
    rw [buildRowTree_rows table.rowsWellFormed.2]
    exact table.rowsWellFormed }

@[simp] theorem Table.canonicalize_schema (table : Table) :
    table.canonicalize.schema = table.schema := rfl

@[simp] theorem Table.canonicalize_indexes (table : Table) :
    table.canonicalize.indexes = table.indexes := rfl

@[simp] theorem Table.canonicalize_rows (table : Table) :
    table.canonicalize.rows = table.rows := by
  exact buildRowTree_rows table.rowsWellFormed.2

theorem Table.rebuild_self (table : Table) :
    Table.rebuild table.schema table.indexes table.rows =
      .ok table.canonicalize := by
  unfold Table.rebuild
  rw [dif_pos table.schemaWellFormed]
  rw [dif_pos table.indexesWellFormed]
  split
  next => congr 1
  next invalid => exact False.elim (invalid table.rowsWellFormed)

theorem Table.rebuild_withoutIndexesRows (table : Table) :
    Table.rebuild table.schema table.indexes table.withoutIndexes.rows =
      .ok table.canonicalize := by
  rw [Table.withoutIndexes_rows]
  exact Table.rebuild_self table

def emptyTable (schema : Schema) : Except String Table :=
  Table.rebuild schema [] []

def Row.create (schema : Schema) (values : List Value) : Except String Row :=
  match values[schema.primaryKey]? with
  | some (.integer rowid) =>
      let row : Row := ⟨rowid, values⟩
      if row.WellFormed schema then .ok row
      else .error "row violates width or NOT NULL constraints"
  | _ => .error "INTEGER PRIMARY KEY must be an integer"

theorem Row.create_wellFormed {schema : Schema} {values : List Value} {row : Row}
    (success : Row.create schema values = .ok row) : row.WellFormed schema := by
  unfold Row.create at success
  cases present : values[schema.primaryKey]? with
  | none => simp [present] at success
  | some value =>
      cases value with
      | null => simp [present] at success
      | realBits bits => simp [present] at success
      | text text => simp [present] at success
      | blob blob => simp [present] at success
      | integer integer =>
          simp only [present] at success
          split at success
          next valid =>
            injection success with equal
            subst row
            exact valid
          next invalid => contradiction

theorem Row.create_self (schema : Schema) (row : Row)
    (valid : row.WellFormed schema) :
    Row.create schema row.values = .ok row := by
  unfold Row.create
  rw [valid.2.1]
  simp only
  rw [if_pos valid]

def orderedUpsert (row : Row) : List Row → List Row
  | [] => [row]
  | existing :: rows =>
      if row.rowid.value < existing.rowid.value then row :: existing :: rows
      else if existing.rowid.value < row.rowid.value then
        existing :: orderedUpsert row rows
      else row :: rows

theorem orderedInsert_treeEntries (row : Row) (rows : List Row) :
    PagedBTree.orderedInsert row.treeKey row (treeEntries rows) =
      treeEntries (orderedUpsert row rows) := by
  induction rows with
  | nil => rfl
  | cons existing rows induction =>
      by_cases before : row.rowid.value < existing.rowid.value
      · have keyBefore : row.treeKey < existing.treeKey :=
          (Row.treeKey_lt_iff row existing).2 before
        simp [treeEntries, orderedUpsert, PagedBTree.orderedInsert,
          before, keyBefore]
      · have keyNotBefore : ¬row.treeKey < existing.treeKey := by
          simpa [Row.treeKey_lt_iff] using before
        by_cases after : existing.rowid.value < row.rowid.value
        · have keyAfter : existing.treeKey < row.treeKey :=
            (Row.treeKey_lt_iff existing row).2 after
          simp only [treeEntries, List.map_cons, orderedUpsert,
            PagedBTree.orderedInsert, if_neg before, if_pos after,
            if_neg keyNotBefore, if_pos keyAfter]
          simpa only [treeEntries] using
            congrArg ((existing.treeKey, existing) :: ·) induction
        · have keyNotAfter : ¬existing.treeKey < row.treeKey := by
            simpa [Row.treeKey_lt_iff] using after
          simp [treeEntries, orderedUpsert, PagedBTree.orderedInsert,
            before, after, keyNotBefore, keyNotAfter]

/-- Tail-recursive companion to `orderedUpsert`.

`orderedUpsert` rebuilds the prefix with `existing :: orderedUpsert row rows`,
so inserting an ascending rowid recurses to the end of the table and the stack
depth equals the row count. That exhausted the stack at roughly 60,000 rows and
dumped core instead of failing cleanly. This version carries the prefix in a
reversed accumulator and is proved equal below, so the clean definition is what
every proof still sees while the compiler runs this one. -/
def orderedUpsertGo (row : Row) : List Row → List Row → List Row
  | [], acc => acc.reverseAux [row]
  | existing :: rows, acc =>
      if row.rowid.value < existing.rowid.value then
        acc.reverseAux (row :: existing :: rows)
      else if existing.rowid.value < row.rowid.value then
        orderedUpsertGo row rows (existing :: acc)
      else acc.reverseAux (row :: rows)

def orderedUpsertTR (row : Row) (rows : List Row) : List Row :=
  orderedUpsertGo row rows []

theorem orderedUpsertGo_eq (row : Row) :
    (rows acc : List Row) →
      orderedUpsertGo row rows acc = acc.reverse ++ orderedUpsert row rows
  | [], acc => by simp [orderedUpsertGo, orderedUpsert, List.reverseAux_eq]
  | existing :: rows, acc => by
      unfold orderedUpsertGo orderedUpsert
      split
      · simp [List.reverseAux_eq]
      · split
        · rw [orderedUpsertGo_eq row rows (existing :: acc)]
          simp
        · simp [List.reverseAux_eq]

@[csimp] theorem orderedUpsert_eq_orderedUpsertTR :
    @orderedUpsert = @orderedUpsertTR := by
  funext row rows
  rw [orderedUpsertTR, orderedUpsertGo_eq]
  simp

theorem mem_orderedUpsert {row candidate : Row} {rows : List Row}
    (membership : candidate ∈ orderedUpsert row rows) :
    candidate = row ∨ candidate ∈ rows := by
  induction rows with
  | nil => simpa [orderedUpsert] using membership
  | cons existing rows induction =>
      simp only [orderedUpsert] at membership
      split at membership
      · simp only [List.mem_cons] at membership
        rcases membership with equal | equal | member
        · exact .inl equal
        · exact .inr (by simp [equal])
        · exact .inr (.tail existing member)
      · split at membership
        · simp only [List.mem_cons] at membership
          rcases membership with equal | member
          · exact .inr (by simp [equal])
          · exact (induction member).imp id (List.Mem.tail existing)
        · simp only [List.mem_cons] at membership
          rcases membership with equal | member
          · exact .inl equal
          · exact .inr (.tail existing member)

theorem orderedUpsert_sorted (row : Row) (rows : List Row)
    (sorted : rows.Pairwise Row.keyLess) :
    (orderedUpsert row rows).Pairwise Row.keyLess := by
  induction rows with
  | nil => simp [orderedUpsert, Row.keyLess]
  | cons existing rows induction =>
      simp only [List.pairwise_cons] at sorted
      simp only [orderedUpsert]
      split
      next rowLess =>
        simp only [List.pairwise_cons]
        refine ⟨?_, sorted⟩
        intro candidate member
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · simpa [Row.keyLess, equal] using rowLess
        · exact Int.lt_trans rowLess (sorted.1 candidate member)
      next rowNotLess =>
        split
        next existingLess =>
          simp only [List.pairwise_cons]
          refine ⟨?_, induction sorted.2⟩
          intro candidate member
          rcases mem_orderedUpsert member with equal | old
          · simpa [Row.keyLess, equal] using existingLess
          · exact sorted.1 candidate old
        next existingNotLess =>
          have equal : row.rowid.value = existing.rowid.value := by omega
          simp only [List.pairwise_cons]
          refine ⟨?_, sorted.2⟩
          intro candidate member
          change row.rowid.value < candidate.rowid.value
          rw [equal]
          exact sorted.1 candidate member

theorem storedRows_insert (tree : PersistentPageTree.Store Row)
    (wellKeyed : RowTreeWellKeyed tree) (row : Row) :
    storedRows (tree.insert row.treeKey row) =
      orderedUpsert row (storedRows tree) := by
  unfold storedRows
  rw [PersistentPageTree.Store.insert_toList, wellKeyed,
    orderedInsert_treeEntries]
  simp [treeEntries, List.map_map, Function.comp_def]

theorem rowTreeWellKeyed_insert (tree : PersistentPageTree.Store Row)
    (wellKeyed : RowTreeWellKeyed tree) (row : Row) :
    RowTreeWellKeyed (tree.insert row.treeKey row) := by
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at wellKeyed
  rw [PersistentPageTree.Store.insert_toList, wellKeyed,
    orderedInsert_treeEntries, storedRows_insert tree wellKeyed row]

def Table.upsert (table : Table) (row : Row)
    (valid : row.WellFormed table.schema) : Table :=
  { table with
    rowTree := table.rowTree.insert row.treeKey row
    rowTreeWellKeyed := rowTreeWellKeyed_insert table.rowTree
      table.rowTreeWellKeyed row
    rowsWellFormed := by
      rw [storedRows_insert table.rowTree table.rowTreeWellKeyed row]
      constructor
      · intro candidate member
        rcases mem_orderedUpsert member with equal | old
        · simpa [equal] using valid
        · exact table.rowsWellFormed.1 candidate old
      · exact orderedUpsert_sorted row table.rows table.rowsWellFormed.2 }

/-- Exact routed lookup in the proof-carrying primary tree. -/
def Table.findRowid? (table : Table) (rowid : Integer) : Option Row :=
  table.rowTree.root.erase.lookup rowid.treeKey

theorem Table.upsert_rows (table : Table) (row : Row)
    (valid : row.WellFormed table.schema) :
    (table.upsert row valid).rows = orderedUpsert row table.rows := by
  exact storedRows_insert table.rowTree table.rowTreeWellKeyed row

def Table.insertValues (table : Table) (values : List Value) :
    Except String Table :=
  match Row.create table.schema values with
  | .error message => .error message
  | .ok row =>
      if valid : row.WellFormed table.schema then
        if (table.findRowid? row.rowid).isSome then
          .error "UNIQUE constraint failed: INTEGER PRIMARY KEY"
        else .ok (table.upsert row valid)
      else .error "internal row validation mismatch"

theorem Table.insertValues_exact {table next : Table} {values : List Value}
    (success : table.insertValues values = .ok next) :
    ∃ row, Row.create table.schema values = .ok row ∧
      row.WellFormed table.schema ∧
      next.rows = orderedUpsert row table.rows := by
  unfold Table.insertValues at success
  cases created : Row.create table.schema values with
  | error message => simp [created] at success
  | ok row =>
      have valid := Row.create_wellFormed created
      simp only [created, valid, dite_true] at success
      split at success
      next duplicate => contradiction
      next fresh =>
        injection success with equal
        subst next
        exact ⟨row, rfl, valid, Table.upsert_rows table row valid⟩

theorem Table.insertValues_schema {table next : Table} {values : List Value}
    (success : table.insertValues values = .ok next) :
    next.schema = table.schema := by
  unfold Table.insertValues at success
  cases created : Row.create table.schema values with
  | error message => simp [created] at success
  | ok row =>
      simp only [created] at success
      split at success <;> try contradiction
      split at success <;> try contradiction
      injection success with equal
      subst next
      rfl

/-- INSERT OR REPLACE: overwrite any row with the same rowid instead of
failing. `orderedUpsert` already replaces on an equal key, so this is
`insertValues` without the duplicate check. -/
def Table.replaceValues (table : Table) (values : List Value) :
    Except String Table :=
  match Row.create table.schema values with
  | .error message => .error message
  | .ok row =>
      if valid : row.WellFormed table.schema then .ok (table.upsert row valid)
      else .error "internal row validation mismatch"

theorem Table.replaceValues_rows {table next : Table} {values : List Value}
    (success : table.replaceValues values = .ok next) :
    ∃ row, Row.create table.schema values = .ok row ∧
      next.rows = orderedUpsert row table.rows := by
  unfold Table.replaceValues at success
  cases created : Row.create table.schema values with
  | error message => simp [created] at success
  | ok row =>
      have valid := Row.create_wellFormed created
      simp only [created, valid, dite_true] at success
      injection success with equal
      subst next
      exact ⟨row, rfl, Table.upsert_rows table row valid⟩

theorem Table.replaceValues_schema {table next : Table} {values : List Value}
    (success : table.replaceValues values = .ok next) :
    next.schema = table.schema := by
  unfold Table.replaceValues at success
  cases created : Row.create table.schema values with
  | error message => simp [created] at success
  | ok row =>
      simp only [created] at success
      split at success <;> try contradiction
      injection success with equal
      subst next
      rfl

def Table.withIndexes (table : Table) (indexes : List Index) :
    Except String Table :=
  if valid : IndexesWellFormed table.schema indexes then
    .ok { table with indexes, indexesWellFormed := valid }
  else .error "invalid index metadata"

theorem Table.withIndexes_exact {table next : Table} {indexes : List Index}
    (success : table.withIndexes indexes = .ok next) :
    next.schema = table.schema ∧ next.indexes = indexes ∧
      next.rows = table.rows := by
  unfold Table.withIndexes at success
  split at success
  next =>
    injection success with equal
    subst next
    exact ⟨rfl, rfl, rfl⟩
  next => contradiction

def Table.addIndex (table : Table) (index : Index) : Except String Table :=
  if table.indexes.any (fun existing => existing.name == index.name) then
    .error s!"index already exists: {index.name}"
  else table.withIndexes (index :: table.indexes)

theorem Table.addIndex_exact {table next : Table} {index : Index}
    (success : table.addIndex index = .ok next) :
    next.schema = table.schema ∧ next.indexes = index :: table.indexes ∧
      next.rows = table.rows := by
  unfold Table.addIndex at success
  split at success
  next duplicate => contradiction
  next fresh => exact Table.withIndexes_exact success

def TablesWellFormed (tables : List Table) : Prop :=
  namesUnique (tables.map (·.schema.name))

instance (tables : List Table) : Decidable (TablesWellFormed tables) := by
  unfold TablesWellFormed namesUnique
  infer_instance

structure Database where
  tables : List Table
  tablesWellFormed : TablesWellFormed tables

/-- Observable logical contents, deliberately excluding proof fields. -/
def Table.contents (table : Table) : Schema × List Index × List Row :=
  (table.schema, table.indexes, table.rows)

/-- Logical table equivalence deliberately forgets proof fields and, once the
stored row tree lands, its physical topology.  Page splits can produce two
different valid trees with the same ordered rows, so exact structure equality
is not a sound serialization or refinement boundary. -/
def Table.Equiv (left right : Table) : Prop :=
  left.contents = right.contents

instance (left right : Table) : Decidable (left.Equiv right) :=
  inferInstanceAs (Decidable (left.contents = right.contents))

theorem Table.Equiv.refl (table : Table) : table.Equiv table := rfl

theorem Table.Equiv.symm {left right : Table} (equivalent : left.Equiv right) :
    right.Equiv left := Eq.symm equivalent

theorem Table.Equiv.trans {first second third : Table}
    (left : first.Equiv second) (right : second.Equiv third) :
    first.Equiv third := Eq.trans left right

theorem Table.canonicalize_equiv (table : Table) :
    table.canonicalize.Equiv table := by
  unfold Table.Equiv Table.contents Table.canonicalize Table.rows
  simp only
  rw [buildRowTree_rows table.rowsWellFormed.2]

theorem Table.Equiv.schema_eq {left right : Table}
    (equivalent : left.Equiv right) : left.schema = right.schema := by
  simpa [Table.Equiv, Table.contents] using congrArg Prod.fst equivalent

theorem Table.Equiv.indexes_eq {left right : Table}
    (equivalent : left.Equiv right) : left.indexes = right.indexes := by
  simpa [Table.Equiv, Table.contents] using
    congrArg (fun contents => contents.2.1) equivalent

theorem Table.Equiv.rows_eq {left right : Table}
    (equivalent : left.Equiv right) : left.rows = right.rows := by
  simpa [Table.Equiv, Table.contents] using
    congrArg (fun contents => contents.2.2) equivalent

def Database.contents (database : Database) :
    List (Schema × List Index × List Row) :=
  database.tables.map Table.contents

/-- Logical database equivalence used at serialization boundaries. -/
def Database.Equiv (left right : Database) : Prop :=
  left.contents = right.contents

instance (left right : Database) : Decidable (left.Equiv right) :=
  inferInstanceAs (Decidable (left.contents = right.contents))

theorem Database.Equiv.refl (database : Database) : database.Equiv database := rfl

theorem Database.Equiv.symm {left right : Database} (equivalent : left.Equiv right) :
    right.Equiv left := Eq.symm equivalent

theorem Database.Equiv.trans {first second third : Database}
    (left : first.Equiv second) (right : second.Equiv third) :
    first.Equiv third := Eq.trans left right

def Database.empty : Database := ⟨[], by simp [TablesWellFormed, namesUnique]⟩

def Database.withoutIndexes (database : Database) : Database := {
  tables := database.tables.map Table.withoutIndexes
  tablesWellFormed := by
    have valid := database.tablesWellFormed
    unfold TablesWellFormed at valid ⊢
    simpa only [List.map_map, Function.comp_apply,
      Table.withoutIndexes_schema] using valid }

def Database.canonicalize (database : Database) : Database := {
  tables := database.tables.map Table.canonicalize
  tablesWellFormed := by
    have valid := database.tablesWellFormed
    unfold TablesWellFormed at valid ⊢
    simpa only [List.map_map, Function.comp_apply, Table.canonicalize]
      using valid }

theorem Database.canonicalize_contents (database : Database) :
    database.canonicalize.contents = database.contents := by
  unfold Database.canonicalize Database.contents
  rw [List.map_map]
  apply List.map_congr_left
  intro table member
  exact table.canonicalize_equiv

theorem Database.canonicalize_equiv (database : Database) :
    database.canonicalize.Equiv database :=
  database.canonicalize_contents

def Database.rebuild (tables : List Table) : Except String Database :=
  if valid : TablesWellFormed tables then .ok ⟨tables, valid⟩
  else .error "duplicate verified table name"

theorem Database.rebuild_tables {tables : List Table} {database : Database}
    (success : Database.rebuild tables = .ok database) :
    database.tables = tables := by
  unfold Database.rebuild at success
  split at success <;> try contradiction
  injection success with equal
  subst database
  rfl

theorem Database.rebuild_withoutIndexes (database : Database) :
    Database.rebuild (database.tables.map Table.withoutIndexes) =
      .ok database.withoutIndexes := by
  unfold Database.rebuild
  have valid : TablesWellFormed (database.tables.map Table.withoutIndexes) :=
    database.withoutIndexes.tablesWellFormed
  rw [dif_pos valid]
  congr 1

theorem Database.rebuild_self (database : Database) :
    Database.rebuild database.tables = .ok database := by
  unfold Database.rebuild
  rw [dif_pos database.tablesWellFormed]

def Database.findTable? (database : Database) (name : String) : Option Table :=
  database.tables.find? (fun table => table.schema.name == name)

def Database.createTable (database : Database) (schema : Schema) :
    Except String Database :=
  if (database.findTable? schema.name).isSome then
    .error s!"table already exists: {schema.name}"
  else
    match emptyTable schema with
    | .error message => .error message
    | .ok table => Database.rebuild (table :: database.tables)

theorem Database.createTable_exact {database next : Database} {schema : Schema}
    (success : database.createTable schema = .ok next) :
    ∃ table, emptyTable schema = .ok table ∧
      next.tables = table :: database.tables := by
  unfold Database.createTable at success
  split at success
  next existingTable => contradiction
  next absent =>
    cases created : emptyTable schema with
    | error message => simp [created] at success
    | ok table =>
        simp only [created] at success
        exact ⟨table, rfl, Database.rebuild_tables success⟩

def replaceTable (replacement : Table) : List Table → List Table
  | [] => []
  | table :: tables =>
      if table.schema.name == replacement.schema.name then replacement :: tables
      else table :: replaceTable replacement tables

def Database.updateTable (database : Database) (replacement : Table) :
    Except String Database :=
  Database.rebuild (replaceTable replacement database.tables)

theorem findTable?_some_schemaName {database : Database} {name : String}
    {table : Table} (found : database.findTable? name = some table) :
    table.schema.name = name := by
  unfold Database.findTable? at found
  have satisfies := List.find?_some found
  simpa only [beq_iff_eq] using satisfies

private theorem find?_replaceTable_target (replacement : Table)
    (name : String) (sameName : replacement.schema.name = name) :
    ∀ (tables : List Table) (table : Table),
      tables.find? (fun current => current.schema.name == name) = some table →
      (replaceTable replacement tables).find?
          (fun current => current.schema.name == name) = some replacement
  | [], _, found => by simp at found
  | current :: tables, table, found => by
      by_cases currentName : current.schema.name = name
      · have replacementMatch : current.schema.name = replacement.schema.name :=
          currentName.trans sameName.symm
        have nameReplacement : name = replacement.schema.name := sameName.symm
        simp [replaceTable, currentName, replacementMatch, nameReplacement]
      · have replacementMiss : current.schema.name ≠ replacement.schema.name := by
          intro equal
          exact currentName (equal.trans sameName)
        simp [currentName] at found
        simpa [replaceTable, currentName, replacementMiss] using
          find?_replaceTable_target replacement name sameName tables table found

private theorem find?_replaceTable_other (replacement : Table)
    (other : String) (different : other ≠ replacement.schema.name) :
    ∀ tables : List Table,
      (replaceTable replacement tables).find?
          (fun current => current.schema.name == other) =
        tables.find? (fun current => current.schema.name == other)
  | [] => rfl
  | current :: tables => by
      by_cases sameName : current.schema.name = replacement.schema.name
      · have currentDifferent : current.schema.name ≠ other := by
          intro equal
          exact different (equal.symm.trans sameName)
        have replacementDifferent : replacement.schema.name ≠ other :=
          Ne.symm different
        simp [replaceTable, sameName, currentDifferent,
          replacementDifferent]
      · simp only [replaceTable, beq_iff_eq, sameName, ↓reduceIte,
          List.find?_cons]
        rw [find?_replaceTable_other replacement other different tables]

/-- Updating a table makes the replacement observable at exactly the original
name.  This is the target half of every execute-level write correspondence
theorem. -/
theorem Database.updateTable_target {database next : Database}
    {name : String} {table replacement : Table}
    (found : database.findTable? name = some table)
    (sameName : replacement.schema.name = name)
    (success : database.updateTable replacement = .ok next) :
    next.findTable? name = some replacement := by
  have nextTables : next.tables = replaceTable replacement database.tables :=
    Database.rebuild_tables success
  unfold Database.findTable?
  rw [nextTables]
  exact find?_replaceTable_target replacement name sameName
    database.tables table found

/-- Updating one table preserves lookup of every differently named table. -/
theorem Database.updateTable_frame {database next : Database}
    {replacement : Table}
    (success : database.updateTable replacement = .ok next)
    (other : String) (different : other ≠ replacement.schema.name) :
    next.findTable? other = database.findTable? other := by
  have nextTables : next.tables = replaceTable replacement database.tables :=
    Database.rebuild_tables success
  unfold Database.findTable?
  rw [nextTables]
  exact find?_replaceTable_other replacement other different database.tables

def Table.retainRows (table : Table) (keep : Row → Bool) : Except String Table :=
  Table.rebuild table.schema table.indexes (table.rows.filter keep)

theorem Table.retainRows_exact {table next : Table} {keep : Row → Bool}
    (success : table.retainRows keep = .ok next) :
    next.rows = table.rows.filter keep := by
  exact (Table.rebuild_exact success).2.2

theorem Table.retainRows_schema {table next : Table} {keep : Row → Bool}
    (success : table.retainRows keep = .ok next) :
    next.schema = table.schema := by
  exact (Table.rebuild_exact success).1

def replaceValue : Nat → Value → List Value → List Value
  | _, _, [] => []
  | 0, value, _ :: values => value :: values
  | index + 1, value, current :: values =>
      current :: replaceValue index value values

def applyAssignments (values : List Value) : List (Nat × Value) → List Value
  | [] => values
  | assignment :: assignments =>
      applyAssignments (replaceValue assignment.1 assignment.2 values) assignments

def patchRows (schema : Schema) (assignments : List (Nat × Value))
    (selected : Row → Bool) : List Row → Except String (List Row)
  | [] => .ok []
  | row :: rows => do
      let patched ← if selected row then
        Row.create schema (applyAssignments row.values assignments)
      else .ok row
      return patched :: (← patchRows schema assignments selected rows)

/-- Apply same-key row replacements through the proof-carrying primary tree.
The two lists are traversed in lockstep, so unchanged rows cost only a list
comparison and changed rows pay one logarithmic tree update.  Any key/shape
change returns `none` and retains the general rebuild fallback. -/
def Table.upsertDifferences? (table : Table) :
    List Row → List Row → Option Table
  | [], [] => some table
  | old :: olds, row :: rows =>
      if old = row then table.upsertDifferences? olds rows
      else if _sameRowid : old.rowid = row.rowid then
        if valid : row.WellFormed table.schema then
          (table.upsert row valid).upsertDifferences? olds rows
        else none
      else none
  | _, _ => none

def Table.withPatchedRows (table : Table) (rows : List Row) :
    Except String Table :=
  match table.upsertDifferences? table.rows rows with
  | some localized =>
      if _exact : localized.rows = rows then .ok localized
      else Table.rebuild table.schema table.indexes rows
  | none => Table.rebuild table.schema table.indexes rows

theorem Table.upsertDifferences?_schema (table : Table) :
    ∀ (old rows : List Row) (next : Table),
      table.upsertDifferences? old rows = some next →
      next.schema = table.schema
  | [], [], next, success => by
      simp only [Table.upsertDifferences?, Option.some.injEq] at success
      subst next
      rfl
  | [], _ :: _, _, success => by simp [Table.upsertDifferences?] at success
  | _ :: _, [], _, success => by simp [Table.upsertDifferences?] at success
  | old :: olds, row :: rows, next, success => by
      unfold Table.upsertDifferences? at success
      split at success
      next same =>
        exact Table.upsertDifferences?_schema table olds rows next success
      next different =>
        split at success
        next sameRowid =>
          split at success
          next valid =>
            have tail := Table.upsertDifferences?_schema (table.upsert row valid)
              olds rows next success
            exact tail
          next => contradiction
        next => contradiction

theorem Table.withPatchedRows_schema {table next : Table} {rows : List Row}
    (success : table.withPatchedRows rows = .ok next) :
    next.schema = table.schema := by
  unfold Table.withPatchedRows at success
  split at success
  next localized localizedResult =>
      have localizedSchema := Table.upsertDifferences?_schema table
        table.rows rows localized localizedResult
      split at success
      next =>
        injection success with equal
        subst next
        exact localizedSchema
      next => exact (Table.rebuild_exact success).1
  next => exact (Table.rebuild_exact success).1

def Table.patchRows (table : Table) (assignments : List (Nat × Value))
    (selected : Row → Bool) : Except String Table := do
  let rows ← Core.patchRows table.schema assignments selected table.rows
  table.withPatchedRows rows

/-- The proof-carrying representation makes the primary-tree lookup exact at
the rowid boundary: a successful routed lookup cannot return a different
signed key. -/
theorem Table.findRowid?_some_eq {table : Table} {rowid : Integer} {row : Row}
    (found : table.findRowid? rowid = some row) : row.rowid = rowid := by
  have inTree := RecursiveBPlusTree.Node.lookup_some_mem found
  have represented := table.rowTreeWellKeyed
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at represented
  rw [represented] at inTree
  rcases List.mem_map.mp inTree with ⟨source, _, pairEqual⟩
  have keyEqual : source.treeKey = rowid.treeKey :=
    congrArg Prod.fst pairEqual
  have rowEqual : source = row := congrArg Prod.snd pairEqual
  rw [rowEqual] at keyEqual
  exact FileFormat.SignedInteger.ext
    ((Integer.treeKey_eq_iff row.rowid rowid).mp keyEqual)

theorem Table.findRowid?_some_mem {table : Table} {rowid : Integer} {row : Row}
    (found : table.findRowid? rowid = some row) : row ∈ table.rows := by
  have inTree := RecursiveBPlusTree.Node.lookup_some_mem found
  have represented := table.rowTreeWellKeyed
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at represented
  rw [represented] at inTree
  rcases List.mem_map.mp inTree with ⟨source, member, pairEqual⟩
  have rowEqual : source = row := congrArg Prod.snd pairEqual
  simpa [rowEqual] using member

/-- Every logical row represented by the table is reachable by routed primary
lookup. This is the completeness half needed to trust pruning rather than
checking it against a scan. -/
theorem Table.findRowid?_eq_some_of_mem {table : Table} {rowid : Integer}
    {row : Row} (member : row ∈ table.rows) (same : row.rowid = rowid) :
    table.findRowid? rowid = some row := by
  have inEntries : (rowid.treeKey, row) ∈ treeEntries table.rows := by
    apply List.mem_map.mpr
    refine ⟨row, member, ?_⟩
    simp only [Prod.mk.injEq, and_true]
    exact congrArg Integer.treeKey same
  have represented := table.rowTreeWellKeyed
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at represented
  unfold Table.findRowid?
  apply RecursiveBPlusTree.Node.lookup_of_mem table.rowTree.rootValid
  rw [represented]
  exact inEntries

theorem Table.findRowid?_eq_some_iff {table : Table} {rowid : Integer}
    {row : Row} :
    table.findRowid? rowid = some row ↔
      row ∈ table.rows ∧ row.rowid = rowid := by
  constructor
  · intro found
    exact ⟨Table.findRowid?_some_mem found, Table.findRowid?_some_eq found⟩
  · intro valid
    exact Table.findRowid?_eq_some_of_mem valid.1 valid.2

/-- Point UPDATE through the persistent primary tree. The rowid equality
checks make the fast path defensive even before lookup correctness is used as
a proof premise, and primary-key-changing assignments stay on the general
validation path. -/
def Table.patchRowid (table : Table) (assignments : List (Nat × Value))
    (rowid : Integer) : Except String (Table × Nat) :=
  match table.findRowid? rowid with
  | none => .ok (table, 0)
  | some row =>
      match created : Row.create table.schema
          (applyAssignments row.values assignments) with
      | .error message => .error message
      | .ok patched =>
          if _samePatched : patched.rowid = rowid then
            .ok (table.upsert patched (Row.create_wellFormed created), 1)
          else .error "point UPDATE changed its INTEGER PRIMARY KEY"

theorem Table.patchRowid_schema {table next : Table}
    {assignments : List (Nat × Value)} {rowid : Integer} {changes : Nat}
    (success : table.patchRowid assignments rowid = .ok (next, changes)) :
    next.schema = table.schema := by
  unfold Table.patchRowid at success
  cases found : table.findRowid? rowid with
  | none =>
      rw [found] at success
      simp only at success
      have pairEqual := Except.ok.inj success
      have tableEqual : table = next := by
        simpa using congrArg Prod.fst pairEqual
      subst next
      rfl
  | some row =>
      rw [found] at success
      simp only at success
      split at success
      next => contradiction
      next patched created =>
        split at success <;> try contradiction
        have pairEqual := Except.ok.inj success
        have tableEqual : table.upsert patched (Row.create_wellFormed created) =
            next := by
          simpa using congrArg Prod.fst pairEqual
        subst next
        rfl

theorem Table.patchRowid_exact {table next : Table}
    {assignments : List (Nat × Value)} {rowid : Integer} {changes : Nat}
    (success : table.patchRowid assignments rowid = .ok (next, changes)) :
    (table.findRowid? rowid = none ∧ next = table ∧ changes = 0) ∨
    ∃ row patched,
      table.findRowid? rowid = some row ∧
      Row.create table.schema (applyAssignments row.values assignments) =
        .ok patched ∧
      patched.rowid = rowid ∧ changes = 1 ∧
      next.rows = orderedUpsert patched table.rows := by
  unfold Table.patchRowid at success
  cases found : table.findRowid? rowid with
  | none =>
      rw [found] at success
      simp only at success
      have pairEqual := Except.ok.inj success
      have tableEqual : table = next := by
        simpa using congrArg Prod.fst pairEqual
      have changesEqual : 0 = changes := by
        simpa using congrArg Prod.snd pairEqual
      exact Or.inl ⟨rfl, tableEqual.symm, changesEqual.symm⟩
  | some row =>
      rw [found] at success
      simp only at success
      split at success
      next => contradiction
      next patched created =>
        split at success
        next samePatched =>
          have pairEqual := Except.ok.inj success
          have tableEqual : table.upsert patched
              (Row.create_wellFormed created) = next := by
            simpa using congrArg Prod.fst pairEqual
          have changesEqual : 1 = changes := by
            simpa using congrArg Prod.snd pairEqual
          refine Or.inr ⟨row, patched, rfl, created, samePatched,
            changesEqual.symm, ?_⟩
          rw [← tableEqual]
          exact Table.upsert_rows table patched (Row.create_wellFormed created)
        next => contradiction

theorem Table.patchRows_exact {table next : Table}
    {assignments : List (Nat × Value)} {selected : Row → Bool}
    {rows : List Row} (patched : Core.patchRows table.schema assignments selected table.rows = .ok rows)
    (success : table.patchRows assignments selected = .ok next) :
    next.rows = rows := by
  unfold Table.patchRows at success
  rw [patched] at success
  change table.withPatchedRows rows = .ok next at success
  unfold Table.withPatchedRows at success
  split at success
  next localized =>
      split at success
      next exactResult =>
        injection success with equal
        subst next
        exact exactResult
      next => exact (Table.rebuild_exact success).2.2
  next =>
      exact (Table.rebuild_exact success).2.2

theorem Table.patchRows_schema {table next : Table}
    {assignments : List (Nat × Value)} {selected : Row → Bool}
    (success : table.patchRows assignments selected = .ok next) :
    next.schema = table.schema := by
  unfold Table.patchRows at success
  cases patched : Core.patchRows table.schema assignments selected table.rows with
  | error message =>
      rw [patched] at success
      contradiction
  | ok rows =>
      simp only [patched] at success
      exact Table.withPatchedRows_schema success

end Core
end SQLeanite
