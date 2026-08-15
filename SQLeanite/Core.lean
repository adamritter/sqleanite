import SQLeanite.PhysicalCodec
import SQLeanite.PersistentPageTree
import Std.Data.TreeMap.Lemmas

namespace SQLeanite
namespace Core

abbrev Value := PhysicalCodec.Value
abbrev Integer := FileFormat.SignedInteger .eight

structure Column where
  name : String
  notNull : Bool := false
  integerPrimaryKey : Bool := false
  /-- A non-aliasing SQLite primary key. Unlike `INTEGER PRIMARY KEY`, this
  column remains in the record payload and is backed by an automatic index. -/
  textPrimaryKey : Bool := false
  deriving DecidableEq, Repr

structure Schema where
  name : String
  columns : List Column
  primaryKey : Nat
  /-- Column named by the user's PRIMARY KEY declaration. It differs from
  `primaryKey` exactly when Core lowers a non-integer key through a hidden
  integer rowid. -/
  declaredPrimaryKey : Nat := primaryKey
  deriving DecidableEq, Repr

def namesUnique (names : List String) : Prop :=
  names.Pairwise (· ≠ ·)

instance (names : List String) : Decidable (namesUnique names) :=
  inferInstanceAs (Decidable (names.Pairwise (· ≠ ·)))

def hiddenRowidColumn : Column := {
  name := "__sqleanite_rowid"
  notNull := true
  integerPrimaryKey := true }

def Schema.hasHiddenRowid (schema : Schema) : Bool :=
  schema.primaryKey != schema.declaredPrimaryKey

/-- Columns described by the public `CREATE TABLE` declaration. The internal
rowid-alias column is deliberately absent from this view. -/
def Schema.catalogColumns (schema : Schema) : List Column :=
  if schema.hasHiddenRowid then schema.columns.take schema.primaryKey
  else schema.columns

/-- The two canonical schema shapes supported by the proved file codec. This
is carried by every `Table`, so the hidden-rowid lowering cannot silently leak
an extra SQL column or lose the declared TEXT primary key. -/
def Schema.CatalogShape (schema : Schema) : Prop :=
  if schema.hasHiddenRowid then
    schema.columns = schema.catalogColumns ++ [hiddenRowidColumn] ∧
    schema.primaryKey = schema.catalogColumns.length ∧
    schema.catalogColumns.findIdx? (·.integerPrimaryKey) = none ∧
    schema.catalogColumns.findIdx? (·.textPrimaryKey) =
      some schema.declaredPrimaryKey
  else
    schema.catalogColumns = schema.columns ∧
    schema.declaredPrimaryKey = schema.primaryKey ∧
    schema.catalogColumns.findIdx? (·.integerPrimaryKey) =
      some schema.primaryKey ∧
    schema.catalogColumns.findIdx? (·.textPrimaryKey) = none

instance (schema : Schema) : Decidable schema.CatalogShape := by
  unfold Schema.CatalogShape
  infer_instance

def Schema.WellFormed (schema : Schema) : Prop :=
  schema.name ≠ "" ∧
  schema.primaryKey < schema.columns.length ∧
  (schema.columns[schema.primaryKey]?).any (·.integerPrimaryKey) ∧
  (schema.columns.filter (·.integerPrimaryKey)).length = 1 ∧
  namesUnique (schema.columns.map (·.name)) ∧
  schema.columns.findIdx? (·.integerPrimaryKey) = some schema.primaryKey ∧
  (∀ column ∈ schema.columns,
    (column.integerPrimaryKey || column.textPrimaryKey) → column.notNull) ∧
  schema.CatalogShape

instance (schema : Schema) : Decidable schema.WellFormed := by
  unfold Schema.WellFormed namesUnique
  infer_instance

def Schema.visibleColumnIndices (schema : Schema) : List Nat :=
  (List.range schema.columns.length).filter fun index =>
    !(schema.primaryKey != schema.declaredPrimaryKey && index == schema.primaryKey)

def Schema.visibleColumns (schema : Schema) : List Column :=
  schema.visibleColumnIndices.filterMap fun index => schema.columns[index]?

def Schema.declaredPrimaryKey? (schema : Schema) : Option Nat :=
  schema.columns[schema.declaredPrimaryKey]?
    |>.map fun _ => schema.declaredPrimaryKey

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

def Index.isImplicitPrimary (schema : Schema) (index : Index) : Bool :=
  schema.hasHiddenRowid &&
    index.name == "sqlite_autoindex_" ++ schema.name ++ "_1" &&
    index.column == schema.declaredPrimaryKey

def Index.WellFormed (schema : Schema) (index : Index) : Prop :=
  index.name ≠ "" ∧ index.column < schema.columns.length

instance (schema : Schema) (index : Index) : Decidable (index.WellFormed schema) :=
  by unfold Index.WellFormed; infer_instance

structure Row where
  rowid : Integer
  values : List Value
  deriving DecidableEq

/-- A comparison key which retains every bit of a SQLite value.  `compareOn`
this key gives the balanced-map implementation a transitive total comparison
without collapsing distinct storage classes or payloads. -/
def Value.orderKey : Value → Nat × (Option Int × (Option Nat ×
    (Option (List UInt8) × Option (List UInt8))))
  | .null => (0, none, none, none, none)
  | .integer value => (1, some value.value, none, none, none)
  | .realBits bits => (2, none, some bits.val, none, none)
  | .text value => (3, none, none, some value.bytes, none)
  | .blob value => (4, none, none, none, some value.bytes)

theorem Value.orderKey_injective : ∀ ⦃left right : Value⦄,
    left.orderKey = right.orderKey → left = right := by
  intro left right equal
  cases left <;> cases right <;> simp_all [Value.orderKey]
  case integer.integer left right =>
    cases left
    cases right
    simp_all
  case realBits.realBits left right =>
    cases left
    cases right
    simp_all
  case text.text left right =>
    cases left
    cases right
    simp_all
  case blob.blob left right =>
    cases left
    cases right
    simp_all

theorem Value.compareOn_orderKey_eq {left right : Value} :
    compareOn Value.orderKey left right = .eq ↔ left = right := by
  simp only [compareOn, Std.compare_eq_iff_eq]
  exact ⟨fun equal => Value.orderKey_injective equal,
    congrArg Value.orderKey⟩

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

def Row.declaredPrimaryValue? (schema : Schema) (row : Row) : Option Value := do
  let column ← schema.declaredPrimaryKey?
  row.values[column]?

def Row.declaredKey (schema : Schema) (row : Row) : Value :=
  (row.declaredPrimaryValue? schema).getD .null

abbrev DeclaredKeyMap :=
  Std.TreeMap Value Row (compareOn Value.orderKey)

def buildDeclaredKeyMap (schema : Schema) (rows : List Row) :
    DeclaredKeyMap :=
  if schema.hasHiddenRowid then
    rows.foldr (fun row (map : DeclaredKeyMap) =>
      map.insert (row.declaredKey schema) row) ∅
  else ∅

theorem buildDeclaredKeyMap_get_of_hidden (schema : Schema) (rows : List Row)
    (key : Value) (hidden : schema.hasHiddenRowid = true) :
    (buildDeclaredKeyMap schema rows).get? key =
      rows.find? (fun row => row.declaredKey schema == key) := by
  unfold buildDeclaredKeyMap
  rw [if_pos hidden]
  induction rows with
  | nil => simp
  | cons row rows induction =>
      simp only [List.foldr_cons]
      change ((rows.foldr
        (fun row (map : DeclaredKeyMap) =>
          map.insert (row.declaredKey schema) row) ∅).insert
          (row.declaredKey schema) row)[key]? = _
      rw [Std.TreeMap.getElem?_insert]
      simp only [Value.compareOn_orderKey_eq, beq_iff_eq]
      change (rows.foldr
        (fun row (map : DeclaredKeyMap) =>
          map.insert (row.declaredKey schema) row) ∅)[key]? = _
        at induction
      by_cases same : row.declaredKey schema = key <;>
        simp [same, induction]

def DeclaredKeyMapRepresents (schema : Schema) (rows : List Row)
    (map : DeclaredKeyMap) : Prop :=
  schema.hasHiddenRowid = true → ∀ key,
    map.get? key = rows.find? (fun row => row.declaredKey schema == key)

theorem buildDeclaredKeyMap_represents (schema : Schema) (rows : List Row) :
    DeclaredKeyMapRepresents schema rows
      (buildDeclaredKeyMap schema rows) := by
  intro hidden key
  exact buildDeclaredKeyMap_get_of_hidden schema rows key hidden

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
  declaredKeyMap : DeclaredKeyMap
  declaredKeyMapRepresents : DeclaredKeyMapRepresents schema
    (storedRows rowTree) declaredKeyMap
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
          declaredKeyMap := buildDeclaredKeyMap schema rows
          declaredKeyMapRepresents := by
            rw [buildRowTree_rows rowsWF.2]
            exact buildDeclaredKeyMap_represents schema rows
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
  declaredKeyMap := buildDeclaredKeyMap table.schema table.rows
  declaredKeyMapRepresents := by
    change DeclaredKeyMapRepresents table.schema
      (storedRows (buildRowTree (storedRows table.rowTree)))
      (buildDeclaredKeyMap table.schema (storedRows table.rowTree))
    rw [buildRowTree_rows table.rowsWellFormed.2]
    exact buildDeclaredKeyMap_represents table.schema table.rows
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
  declaredKeyMap := buildDeclaredKeyMap table.schema table.rows
  declaredKeyMapRepresents := by
    change DeclaredKeyMapRepresents table.schema
      (storedRows (buildRowTree (storedRows table.rowTree)))
      (buildDeclaredKeyMap table.schema (storedRows table.rowTree))
    rw [buildRowTree_rows table.rowsWellFormed.2]
    exact buildDeclaredKeyMap_represents table.schema table.rows
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

def implicitPrimaryIndexes (schema : Schema) : List Index :=
  if schema.hasHiddenRowid then
    match schema.declaredPrimaryKey? with
    | some column => [{
        name := "sqlite_autoindex_" ++ schema.name ++ "_1"
        column }]
    | none => []
  else []

theorem implicitPrimaryIndexes_areImplicit (schema : Schema) :
    ∀ index ∈ implicitPrimaryIndexes schema,
      index.isImplicitPrimary schema = true := by
  intro index member
  unfold implicitPrimaryIndexes at member
  split at member
  next hidden =>
    cases declared : schema.declaredPrimaryKey? with
    | none => simp [declared] at member
    | some column =>
        have columnEq : column = schema.declaredPrimaryKey := by
          unfold Schema.declaredPrimaryKey? at declared
          cases present : schema.columns[schema.declaredPrimaryKey]? with
          | none => simp [present] at declared
          | some definition =>
              rw [present] at declared
              exact (Option.some.inj declared).symm
        simp only [declared, List.mem_singleton] at member
        subst index
        simp [Index.isImplicitPrimary, hidden, columnEq]
  next visible => simp at member

def emptyTable (schema : Schema) : Except String Table :=
  Table.rebuild schema (implicitPrimaryIndexes schema) []

def Row.create (schema : Schema) (values : List Value) : Except String Row :=
  match values[schema.primaryKey]? with
  | some (.integer rowid) =>
      let row : Row := ⟨rowid, values⟩
      if row.WellFormed schema then .ok row
      else .error "row violates width or NOT NULL constraints"
  | _ => .error "INTEGER PRIMARY KEY must be an integer"

/-- Fill the hidden rowid slot used to lower a non-integer SQLite primary key
before applying the ordinary row invariant. -/
def Row.createWithRowid (schema : Schema) (rowid : Integer)
    (values : List Value) : Except String Row :=
  if schema.hasHiddenRowid then
    Row.create schema (values.set schema.primaryKey (.integer rowid))
  else Row.create schema values

theorem Row.createWithRowid_rowid {schema : Schema} {rowid : Integer}
    {values : List Value} {row : Row}
    (hidden : schema.hasHiddenRowid = true)
    (created : Row.createWithRowid schema rowid values = .ok row) :
    row.rowid = rowid := by
  unfold Row.createWithRowid at created
  rw [if_pos hidden] at created
  unfold Row.create at created
  cases present : (values.set schema.primaryKey
      (.integer rowid))[schema.primaryKey]? with
  | none => simp [present] at created
  | some value =>
      cases value with
      | null => simp [present] at created
      | realBits bits => simp [present] at created
      | text text => simp [present] at created
      | blob blob => simp [present] at created
      | integer actual =>
          have bound : schema.primaryKey < values.length := by
            obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp present
            simpa using bound
          have setSelf : (values.set schema.primaryKey
              (.integer rowid))[schema.primaryKey]? = some (.integer rowid) :=
            List.getElem?_set_self (by exact bound)
          have sameInteger : actual = rowid := by
            have sameValue : (PhysicalCodec.Value.integer actual) = .integer rowid :=
              Option.some.inj (present.symm.trans setSelf)
            injection sameValue
          subst actual
          simp only [present] at created
          split at created
          next valid =>
            injection created with equal
            subst row
            rfl
          next => contradiction

def Table.lastRow? (table : Table) : Option Row :=
  table.rowTree.root.last?.map (·.2)

theorem Table.lastRow?_eq_rows_getLast? (table : Table) :
    table.lastRow? = table.rows.getLast? := by
  unfold Table.lastRow? Table.rows storedRows
  rw [PersistentPageTree.Node.last?_eq_erase]
  rw [RecursiveBPlusTree.Node.last?_eq_getLast?]
  simp

def Table.nextGeneratedRowid? (table : Table) : Option Integer :=
  let next := match table.lastRow? with
    | none => 1
    | some row => if row.rowid.value < 0 then 1 else row.rowid.value.toNat + 1
  if upper : next < FileFormat.IntegerWidth.eight.midpoint then
    some ⟨Int.ofNat next, by simp, by simpa using upper⟩
  else none

private theorem row_value_le_last {rows : List Row} {row last : Row}
    (sorted : rows.Pairwise Row.keyLess) (member : row ∈ rows)
    (lastResult : rows.getLast? = some last) :
    row.rowid.value ≤ last.rowid.value := by
  induction rows with
  | nil => contradiction
  | cons head tail induction =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at member
          subst row
          simp only [List.getLast?_singleton, Option.some.injEq] at lastResult
          subst last
          exact Int.le_refl _
      | cons next rest =>
          rcases List.pairwise_cons.mp sorted with ⟨headBefore, tailSorted⟩
          have tailLast : (next :: rest).getLast? = some last := by
            simpa using lastResult
          rcases List.mem_cons.mp member with equal | tailMember
          · subst row
            exact Int.le_of_lt
              (headBefore last (List.mem_of_getLast? tailLast))
          · exact induction tailSorted tailMember tailLast

theorem Table.nextGeneratedRowid?_greater {table : Table} {rowid : Integer}
    (generated : table.nextGeneratedRowid? = some rowid) :
    ∀ row ∈ table.rows, row.rowid.value < rowid.value := by
  intro row member
  unfold Table.nextGeneratedRowid? at generated
  cases lastResult : table.lastRow? with
  | none =>
      have rowsLast : table.rows.getLast? = none := by
        rw [← table.lastRow?_eq_rows_getLast?]
        exact lastResult
      have empty : table.rows = [] := List.getLast?_eq_none_iff.mp rowsLast
      simp [empty] at member
  | some last =>
      have rowsLast : table.rows.getLast? = some last := by
        rw [← table.lastRow?_eq_rows_getLast?]
        exact lastResult
      have beforeLast := row_value_le_last table.rowsWellFormed.2 member rowsLast
      simp only [lastResult] at generated
      split at generated
      next negative =>
        split at generated
        next upper =>
          injection generated with equal
          subst rowid
          change row.rowid.value < (1 : Int)
          omega
        next => contradiction
      next nonnegative =>
        split at generated
        next upper =>
          injection generated with equal
          subst rowid
          have lastToNat : Int.ofNat last.rowid.value.toNat =
              last.rowid.value := Int.toNat_of_nonneg (Int.le_of_not_gt nonnegative)
          change row.rowid.value < Int.ofNat (last.rowid.value.toNat + 1)
          have nextEq : Int.ofNat (last.rowid.value.toNat + 1) =
              Int.ofNat last.rowid.value.toNat + 1 := rfl
          rw [nextEq, lastToNat]
          omega
        next => contradiction

def Table.createRow (table : Table) (values : List Value) : Except String Row :=
  if table.schema.hasHiddenRowid then
    match table.nextGeneratedRowid? with
    | some rowid => Row.createWithRowid table.schema rowid values
    | none => .error "database or disk is full"
  else Row.create table.schema values

theorem Table.createRow_generated {table : Table} {values : List Value}
    {row : Row} (hidden : table.schema.hasHiddenRowid = true)
    (created : table.createRow values = .ok row) :
    ∃ rowid, table.nextGeneratedRowid? = some rowid ∧ row.rowid = rowid := by
  unfold Table.createRow at created
  rw [if_pos hidden] at created
  cases generated : table.nextGeneratedRowid? with
  | none => simp [generated] at created
  | some rowid =>
      rw [generated] at created
      exact ⟨rowid, rfl, Row.createWithRowid_rowid hidden created⟩

def Table.findDeclaredPrimary? (table : Table) (row : Row) : Option Row :=
  if table.schema.hasHiddenRowid then
    table.declaredKeyMap.get? (row.declaredKey table.schema)
  else none

/-- The balanced declared-primary-key lookup is exactly the old logical row
search.  This is the completeness theorem which permits the live INSERT path
to replace an O(n) scan with O(log n) routing. -/
theorem Table.findDeclaredPrimary?_exact (table : Table) (row : Row)
    (hidden : table.schema.hasHiddenRowid = true) :
    table.findDeclaredPrimary? row = table.rows.find? (fun existing =>
      existing.declaredKey table.schema == row.declaredKey table.schema) := by
  unfold Table.findDeclaredPrimary?
  rw [if_pos hidden]
  exact table.declaredKeyMapRepresents hidden (row.declaredKey table.schema)

def Table.createReplacementRow (table : Table) (values : List Value) :
    Except String Row := do
  let candidate ← table.createRow values
  match table.findDeclaredPrimary? candidate with
  | some existing => Row.createWithRowid table.schema existing.rowid values
  | none => pure candidate

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

theorem orderedUpsert_eq_append_of_afterAll (row : Row) :
    ∀ (rows : List Row),
      (∀ existing ∈ rows, existing.rowid.value < row.rowid.value) →
      orderedUpsert row rows = rows ++ [row]
  | [], _ => rfl
  | existing :: rows, afterAll => by
      have existingBefore : existing.rowid.value < row.rowid.value :=
        afterAll existing (by simp)
      have rowNotBefore : ¬row.rowid.value < existing.rowid.value := by omega
      simp only [orderedUpsert, if_neg rowNotBefore, if_pos existingBefore,
        List.cons_append, List.cons.injEq, true_and]
      exact orderedUpsert_eq_append_of_afterAll row rows fun candidate member =>
        afterAll candidate (by simp [member])

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

theorem Table.declaredKeyMap_insert_represents_append (table : Table)
    (row : Row) (hidden : table.schema.hasHiddenRowid = true)
    (fresh : table.declaredKeyMap.get? (row.declaredKey table.schema) = none) :
    DeclaredKeyMapRepresents table.schema (table.rows ++ [row])
      (table.declaredKeyMap.insert (row.declaredKey table.schema) row) := by
  intro _ target
  change (table.declaredKeyMap.insert
    (row.declaredKey table.schema) row)[target]? = _
  rw [Std.TreeMap.getElem?_insert]
  simp only [Value.compareOn_orderKey_eq]
  rw [List.find?_append]
  have represented := table.declaredKeyMapRepresents hidden target
  have keyAbsent := table.declaredKeyMapRepresents hidden
    (row.declaredKey table.schema)
  rw [fresh] at keyAbsent
  change table.declaredKeyMap[target]? =
    table.rows.find? (fun row => row.declaredKey table.schema == target)
    at represented
  have oldNone : table.rows.find? (fun existing =>
      existing.declaredKey table.schema == row.declaredKey table.schema) =
      none := by
    simpa only [Table.rows] using keyAbsent.symm
  by_cases same : row.declaredKey table.schema = target
  · subst target
    rw [if_pos rfl, oldNone]
    simp
  · rw [if_neg same, represented]
    simp [same]

private theorem find?_orderedUpsert_of_false (inserted : Row) (rows : List Row)
    (predicate : Row → Bool) (insertedFalse : predicate inserted = false)
    (freshRowid : ∀ existing ∈ rows,
      existing.rowid.value ≠ inserted.rowid.value) :
    (orderedUpsert inserted rows).find? predicate = rows.find? predicate := by
  induction rows with
  | nil => simp [orderedUpsert, insertedFalse]
  | cons head tail induction =>
      have headFresh := freshRowid head (by simp)
      have tailFresh : ∀ existing ∈ tail,
          existing.rowid.value ≠ inserted.rowid.value := by
        intro existing member
        exact freshRowid existing (by simp [member])
      by_cases before : inserted.rowid.value < head.rowid.value
      · simp [orderedUpsert, before, insertedFalse]
      · by_cases after : head.rowid.value < inserted.rowid.value
        · rw [show orderedUpsert inserted (head :: tail) =
              head :: orderedUpsert inserted tail by
                simp [orderedUpsert, before, after]]
          cases headResult : predicate head
          · simp [headResult, induction tailFresh]
          · simp [headResult]
        · have equal : head.rowid.value = inserted.rowid.value := by omega
          exact False.elim (headFresh equal)

private theorem find?_orderedUpsert_of_true (inserted : Row) (rows : List Row)
    (predicate : Row → Bool) (insertedTrue : predicate inserted = true)
    (oldNone : rows.find? predicate = none) :
    (orderedUpsert inserted rows).find? predicate = some inserted := by
  induction rows with
  | nil => simp [orderedUpsert, insertedTrue]
  | cons head tail induction =>
      have headFalse : predicate head = false := by
        cases result : predicate head <;> simp_all
      have tailNone : tail.find? predicate = none := by
        simpa [headFalse] using oldNone
      by_cases before : inserted.rowid.value < head.rowid.value
      · simp [orderedUpsert, before, insertedTrue]
      · by_cases after : head.rowid.value < inserted.rowid.value
        · simp [orderedUpsert, before, after, headFalse,
            induction tailNone]
        · simp [orderedUpsert, before, after, insertedTrue]

theorem Table.declaredKeyMap_insert_represents_orderedUpsert (table : Table)
    (row : Row) (hidden : table.schema.hasHiddenRowid = true)
    (freshRowid : ∀ existing ∈ table.rows,
      existing.rowid.value ≠ row.rowid.value)
    (fresh : table.declaredKeyMap.get? (row.declaredKey table.schema) = none) :
    DeclaredKeyMapRepresents table.schema (orderedUpsert row table.rows)
      (table.declaredKeyMap.insert (row.declaredKey table.schema) row) := by
  intro _ target
  change (table.declaredKeyMap.insert
    (row.declaredKey table.schema) row)[target]? = _
  rw [Std.TreeMap.getElem?_insert]
  simp only [Value.compareOn_orderKey_eq]
  have represented := table.declaredKeyMapRepresents hidden target
  have keyAbsent := table.declaredKeyMapRepresents hidden
    (row.declaredKey table.schema)
  rw [fresh] at keyAbsent
  change table.declaredKeyMap[target]? =
    table.rows.find? (fun existing => existing.declaredKey table.schema == target)
    at represented
  have oldNone : table.rows.find? (fun existing =>
      existing.declaredKey table.schema == row.declaredKey table.schema) =
      none := by
    simpa only [Table.rows] using keyAbsent.symm
  by_cases same : row.declaredKey table.schema = target
  · subst target
    rw [if_pos rfl]
    exact (find?_orderedUpsert_of_true row table.rows _ (by simp) oldNone).symm
  · rw [if_neg same, represented]
    exact (find?_orderedUpsert_of_false row table.rows _ (by simp [same])
      freshRowid).symm

/-- O(log n) append for the hidden-rowid table shape.  The two erased premises
come from `nextGeneratedRowid?` and the proof-carrying declared-key map, so the
runtime performs one primary-tree insert and one balanced-map insert without
reconstructing either logical list. -/
def Table.upsertGeneratedFresh (table : Table) (row : Row)
    (valid : row.WellFormed table.schema)
    (hidden : table.schema.hasHiddenRowid = true)
    (freshRowid : ∀ existing ∈ table.rows,
      existing.rowid.value ≠ row.rowid.value)
    (fresh : table.declaredKeyMap.get? (row.declaredKey table.schema) = none) :
    Table :=
  { table with
    rowTree := table.rowTree.insert row.treeKey row
    rowTreeWellKeyed := rowTreeWellKeyed_insert table.rowTree
      table.rowTreeWellKeyed row
    declaredKeyMap := table.declaredKeyMap.insert
      (row.declaredKey table.schema) row
    declaredKeyMapRepresents := by
      rw [storedRows_insert table.rowTree table.rowTreeWellKeyed row]
      simpa only [Table.rows] using
        table.declaredKeyMap_insert_represents_orderedUpsert row hidden
          freshRowid fresh
    rowsWellFormed := by
      rw [storedRows_insert table.rowTree table.rowTreeWellKeyed row]
      constructor
      · intro candidate member
        rcases mem_orderedUpsert member with equal | old
        · simpa [equal] using valid
        · exact table.rowsWellFormed.1 candidate old
      · exact orderedUpsert_sorted row table.rows table.rowsWellFormed.2 }

def Table.upsert (table : Table) (row : Row)
    (valid : row.WellFormed table.schema) : Table :=
  { table with
    rowTree := table.rowTree.insert row.treeKey row
    rowTreeWellKeyed := rowTreeWellKeyed_insert table.rowTree
      table.rowTreeWellKeyed row
    declaredKeyMap := buildDeclaredKeyMap table.schema
      (orderedUpsert row table.rows)
    declaredKeyMapRepresents := by
      rw [storedRows_insert table.rowTree table.rowTreeWellKeyed row]
      exact buildDeclaredKeyMap_represents table.schema
        (orderedUpsert row table.rows)
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
  table.rowTree.root.lookup rowid.treeKey

private theorem Table.findRowid?_eq_some_of_mem_early {table : Table}
    {rowid : Integer} {row : Row} (member : row ∈ table.rows)
    (same : row.rowid = rowid) : table.findRowid? rowid = some row := by
  have inEntries : (rowid.treeKey, row) ∈ treeEntries table.rows := by
    apply List.mem_map.mpr
    refine ⟨row, member, ?_⟩
    simp only [Prod.mk.injEq, and_true]
    exact congrArg Integer.treeKey same
  have represented := table.rowTreeWellKeyed
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at represented
  unfold Table.findRowid?
  rw [PersistentPageTree.Node.lookup_eq_erase]
  apply RecursiveBPlusTree.Node.lookup_of_mem table.rowTree.rootValid
  rw [represented]
  exact inEntries

private theorem Table.findRowid?_fresh_of_not_isSome {table : Table}
    {rowid : Integer} (absent : ¬(table.findRowid? rowid).isSome = true) :
    ∀ existing ∈ table.rows, existing.rowid.value ≠ rowid.value := by
  intro existing member sameValue
  have same : existing.rowid = rowid :=
    FileFormat.SignedInteger.ext sameValue
  have found := Table.findRowid?_eq_some_of_mem_early member same
  rw [found] at absent
  simp at absent

theorem Table.upsert_rows (table : Table) (row : Row)
    (valid : row.WellFormed table.schema) :
    (table.upsert row valid).rows = orderedUpsert row table.rows := by
  exact storedRows_insert table.rowTree table.rowTreeWellKeyed row

theorem Table.upsertGeneratedFresh_rows (table : Table) (row : Row)
    (valid : row.WellFormed table.schema)
    (hidden : table.schema.hasHiddenRowid = true)
    (freshRowid : ∀ existing ∈ table.rows,
      existing.rowid.value ≠ row.rowid.value)
    (fresh : table.declaredKeyMap.get? (row.declaredKey table.schema) = none) :
    (table.upsertGeneratedFresh row valid hidden freshRowid fresh).rows =
      orderedUpsert row table.rows := by
  exact storedRows_insert table.rowTree table.rowTreeWellKeyed row

def Table.insertValues (table : Table) (values : List Value) :
    Except String Table :=
  match table.createRow values with
  | .error message => .error message
  | .ok row =>
      if valid : row.WellFormed table.schema then
        if duplicate : (table.findRowid? row.rowid).isSome then
          .error "UNIQUE constraint failed: INTEGER PRIMARY KEY"
        else match declared : table.findDeclaredPrimary? row with
          | some _ => .error "UNIQUE constraint failed: PRIMARY KEY"
          | none =>
              if hidden : table.schema.hasHiddenRowid then
                have fresh : table.declaredKeyMap.get?
                    (row.declaredKey table.schema) = none := by
                  simpa [Table.findDeclaredPrimary?, hidden] using declared
                have freshRowid := table.findRowid?_fresh_of_not_isSome duplicate
                .ok (table.upsertGeneratedFresh row valid hidden freshRowid fresh)
              else .ok (table.upsert row valid)
      else .error "internal row validation mismatch"

theorem Table.insertValues_exact {table next : Table} {values : List Value}
    (success : table.insertValues values = .ok next) :
    ∃ row, table.createRow values = .ok row ∧
      row.WellFormed table.schema ∧
      next.rows = orderedUpsert row table.rows := by
  cases created : table.createRow values with
  | error message =>
      simp only [Table.insertValues, created] at success
      contradiction
  | ok row =>
      simp only [Table.insertValues, created] at success
      split at success
      next valid =>
        split at success
        next duplicate => contradiction
        next fresh =>
          split at success
          next duplicate => contradiction
          next declaredFresh =>
            split at success
            next hidden =>
              injection success with equal
              subst next
              exact ⟨row, rfl, valid,
                Table.upsertGeneratedFresh_rows table row valid _ _ _⟩
            next visible =>
              injection success with equal
              subst next
              exact ⟨row, rfl, valid, Table.upsert_rows table row valid⟩
      next => contradiction

theorem Table.insertValues_schema {table next : Table} {values : List Value}
    (success : table.insertValues values = .ok next) :
    next.schema = table.schema := by
  cases created : table.createRow values with
  | error message =>
      simp only [Table.insertValues, created] at success
      contradiction
  | ok row =>
      simp only [Table.insertValues, created] at success
      split at success <;> try contradiction
      split at success <;> try contradiction
      split at success <;> try contradiction
      split at success
      <;> injection success with equal
      <;> subst next
      <;> rfl

/-- INSERT OR REPLACE: overwrite any row with the same rowid instead of
failing. `orderedUpsert` already replaces on an equal key, so this is
`insertValues` without the duplicate check. -/
def Table.replaceValues (table : Table) (values : List Value) :
    Except String Table :=
  match table.createReplacementRow values with
  | .error message => .error message
  | .ok row =>
      if valid : row.WellFormed table.schema then .ok (table.upsert row valid)
      else .error "internal row validation mismatch"

theorem Table.replaceValues_rows {table next : Table} {values : List Value}
    (success : table.replaceValues values = .ok next) :
    ∃ row, table.createReplacementRow values = .ok row ∧
      next.rows = orderedUpsert row table.rows := by
  unfold Table.replaceValues at success
  cases created : table.createReplacementRow values with
  | error message => simp [created] at success
  | ok row =>
      simp only [created] at success
      split at success
      next valid =>
        injection success with equal
        subst next
        exact ⟨row, rfl, Table.upsert_rows table row valid⟩
      next => contradiction

theorem Table.replaceValues_schema {table next : Table} {values : List Value}
    (success : table.replaceValues values = .ok next) :
    next.schema = table.schema := by
  unfold Table.replaceValues at success
  cases created : table.createReplacementRow values with
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

theorem Database.findTable?_mem {database : Database} {name : String}
    {table : Table} (found : database.findTable? name = some table) :
    table ∈ database.tables := by
  exact List.mem_of_find?_eq_some found

def Database.findTableMember? (database : Database) (name : String) :
    Option { table // table ∈ database.tables } :=
  match found : database.findTable? name with
  | none => none
  | some table => some ⟨table, database.findTable?_mem found⟩

private theorem findTableIn?_eq_some_of_mem :
    ∀ (tables : List Table), TablesWellFormed tables →
      ∀ (table : Table), table ∈ tables →
        tables.find? (fun current => current.schema.name == table.schema.name) =
          some table
  | [], _, _, member => by simp at member
  | head :: tail, valid, table, member => by
      have valid' := valid
      unfold TablesWellFormed namesUnique at valid'
      simp only [List.map_cons, List.pairwise_cons] at valid'
      simp only [List.mem_cons] at member
      rcases member with same | member
      · subst table
        simp
      · have different : head.schema.name ≠ table.schema.name := by
          exact valid'.1 table.schema.name (by
            rw [List.mem_map]
            exact ⟨table, member, rfl⟩)
        have tailValid : TablesWellFormed tail := by
          exact valid'.2
        simp [different,
          findTableIn?_eq_some_of_mem tail tailValid table member]

/-- A table carried by a database can be recovered by its unique schema name.
This is the proof bridge used by connection-local physical certificates: the
cache names a table by membership, while a statement obtains it by lookup. -/
theorem Database.findTable?_eq_some_of_mem {database : Database}
    {table : Table} (member : table ∈ database.tables) :
    database.findTable? table.schema.name = some table := by
  exact findTableIn?_eq_some_of_mem database.tables database.tablesWellFormed
    table member

theorem Database.table_eq_of_mem_of_name_eq {database : Database}
    {left right : Table} (leftMember : left ∈ database.tables)
    (rightMember : right ∈ database.tables)
    (sameName : left.schema.name = right.schema.name) : left = right := by
  have leftFound := database.findTable?_eq_some_of_mem leftMember
  have rightFound := database.findTable?_eq_some_of_mem rightMember
  rw [sameName] at leftFound
  exact Option.some.inj (leftFound.symm.trans rightFound)

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
  have foundErased : table.rowTree.root.erase.lookup rowid.treeKey = some row := by
    rw [← PersistentPageTree.Node.lookup_eq_erase]
    exact found
  have inTree := RecursiveBPlusTree.Node.lookup_some_mem foundErased
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
  have foundErased : table.rowTree.root.erase.lookup rowid.treeKey = some row := by
    rw [← PersistentPageTree.Node.lookup_eq_erase]
    exact found
  have inTree := RecursiveBPlusTree.Node.lookup_some_mem foundErased
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
  rw [PersistentPageTree.Node.lookup_eq_erase]
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
