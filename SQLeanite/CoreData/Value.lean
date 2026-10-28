import SQLeanite.ColumnDefault
import SQLeanite.SQLite.PhysicalAffinity
import SQLeanite.SQLite.PrimaryKey
import Std.Data.TreeMap.Lemmas

namespace SQLeanite
namespace Core
attribute [local instance] lexOrd

abbrev Value := PhysicalCodec.Value

abbrev Integer := FileFormat.SignedInteger .eight

/-- Schema constraint policies supported by the atomic Core SQL boundary.
FAIL/ROLLBACK require a distinct statement outcome and are not represented yet. -/
inductive NotNullConflict where
  | abort | ignore | replace
  deriving DecidableEq, Repr

/-- The declared type of an indexed primary key, including absent versus
explicitly empty types. The legacy TEXT-key shape remains a compact case. -/
structure IndexedType where
  declaredType : String
  explicitEmptyType : Bool := false
  explicitEmptyTypeOnly : explicitEmptyType = true → declaredType = "" := by simp_all
  deriving DecidableEq, Repr

structure Column where
  name : String
  notNull : Bool := false
  integerPrimaryKey : Bool := false
  /-- Explicit SQL NOT NULL on an INTEGER rowid alias. `notNull` separately
  records the internal invariant that an allocated rowid is never NULL. -/
  integerPrimaryNotNull : Bool := false
  integerPrimaryNotNullOnly : integerPrimaryNotNull = true → integerPrimaryKey = true := by
    simp_all
  /-- A non-aliasing SQLite primary key. Unlike `INTEGER PRIMARY KEY`, this
  column remains in the record payload and is backed by an automatic index. -/
  textPrimaryKey : Bool := false
  /-- Non-primary declared type. Primary columns use INTEGER, the compact
  TEXT case, or their indexedType metadata. Keeping these cases disjoint makes
  canonical schema printing invertible for every admitted Column. -/
  declaredType : String := ""
  primaryType : (integerPrimaryKey || textPrimaryKey) = true → declaredType = "" := by
    simp_all
  notNullConflict : NotNullConflict := .abort
  notNullConflictOnly : notNullConflict ≠ .abort →
      notNull = true ∧ (integerPrimaryKey = true → integerPrimaryNotNull = true) := by
    simp_all
  primaryConflict : NotNullConflict := .abort
  primaryConflictOnly : primaryConflict ≠ .abort → (integerPrimaryKey || textPrimaryKey) = true := by
    simp_all
  defaultValue : Option ColumnDefault.Spec := none
  /-- An explicitly empty type has NUMERIC affinity; an absent type has BLOB.
The displayed type is empty in both cases. -/
  explicitEmptyType : Bool := false
  explicitEmptyTypeOnly : explicitEmptyType = true →
      declaredType = "" ∧ integerPrimaryKey = false ∧ textPrimaryKey = false := by simp_all
  indexedType : Option IndexedType := none
  indexedTypeOnly : indexedType.isSome = true → textPrimaryKey = true := by simp_all
  autoIncrement : Bool := false
  autoIncrementOnly : autoIncrement = true → integerPrimaryKey = true := by simp_all
  deriving DecidableEq, Repr

def Column.typed (name typeName : String) (notNull : Bool) : Column :=
  if typeName = "" then { name, notNull, explicitEmptyType := true }
  else { name, notNull, declaredType := typeName }

def Column.withPrimaryConflict (column : Column) (policy : NotNullConflict) : Option Column :=
  if valid : (column.integerPrimaryKey || column.textPrimaryKey) = true then
    some { column with primaryConflict := policy, primaryConflictOnly := fun _ => valid }
  else if policy = .abort then some column else none

def Column.withNotNullConflict (column : Column) (policy : NotNullConflict) : Option Column :=
  if valid : column.notNull = true ∧
      (column.integerPrimaryKey = true → column.integerPrimaryNotNull = true) then
    some { column with notNullConflict := policy, notNullConflictOnly := fun _ => valid }
  else if policy = .abort then some column else none

def Column.withoutNotNullConflict (column : Column) : Column :=
  { column with notNullConflict := .abort, notNullConflictOnly := by simp }

theorem Column.restoreNotNullConflict (column : Column) :
    column.withoutNotNullConflict.withNotNullConflict column.notNullConflict = some column := by
  unfold Column.withNotNullConflict Column.withoutNotNullConflict
  split
  · rfl
  · next invalid =>
      have plain : column.notNullConflict = .abort := by
        by_cases same : column.notNullConflict = .abort
        · exact same
        · exact False.elim (invalid (column.notNullConflictOnly same))
      simp [plain]
      cases column
      simp_all

def Column.affinity (column : Column) : SQLite.Affinity :=
  if column.integerPrimaryKey then .integer
  else if column.textPrimaryKey then
    match column.indexedType with
    | none => .text
    | some typ => if typ.explicitEmptyType then .numeric else SQLite.typeAffinity typ.declaredType
  else if column.explicitEmptyType then .numeric
  else SQLite.typeAffinity column.declaredType

/-- Explicitly empty declared types retain their numeric affinity independently
of column names and nullability; an omitted type has blob affinity instead. -/
theorem Column.typed_empty_affinity (name : String) (notNull : Bool) :
    (Column.typed name "" notNull).affinity = .numeric := by
  simp [Column.typed, Column.affinity]

def Column.defaultForInsert (column : Column) : Except String Value := do
  if column.integerPrimaryKey then return .null
  match column.defaultValue with
  | none => return .null
  | some spec => return SQLite.PhysicalAffinity.write column.affinity (← ColumnDefault.evaluate spec)

def Column.defaultForRecord (column : Column) : Except String Value := do
  match column.defaultValue with
  | none => return .null
  | some spec => return SQLite.PhysicalAffinity.write column.affinity (← ColumnDefault.storedValue spec)

theorem Column.defaultForInsert_rowid (column : Column) (key : column.integerPrimaryKey = true) :
    column.defaultForInsert = .ok .null := by simp [Column.defaultForInsert, key, pure, Except.pure]

structure Schema where
  name : String
  columns : List Column
  primaryKey : Nat
  /-- Column named by the user's PRIMARY KEY declaration. It differs from
  `primaryKey` when Core lowers a non-integer key or an implicit rowid.
  A value equal to columns.length means there is no declared primary key. -/
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

/-- AUTOINCREMENT belongs only to the actual INTEGER rowid alias. -/
def Schema.autoIncrement (schema : Schema) : Bool :=
  (schema.columns[schema.primaryKey]?).any (·.autoIncrement)

/-- Columns described by the public `CREATE TABLE` declaration. The internal
rowid-alias column is deliberately absent from this view. -/
def Schema.catalogColumns (schema : Schema) : List Column :=
  if schema.hasHiddenRowid then schema.columns.take schema.primaryKey
  else schema.columns

/-- Canonical rowid-table shapes supported by the proved file codec. A hidden
rowid represents either a declared TEXT key or a table without a declared key.
The latter uses columns.length as an out-of-range declared-key sentinel. -/
def Schema.CatalogShape (schema : Schema) : Prop :=
  if schema.hasHiddenRowid then
    schema.columns = schema.catalogColumns ++ [hiddenRowidColumn] ∧
    schema.primaryKey = schema.catalogColumns.length ∧
    schema.catalogColumns.findIdx? (·.integerPrimaryKey) = none ∧
    schema.catalogColumns ≠ [] ∧
    schema.declaredPrimaryKey =
      (schema.catalogColumns.findIdx? (·.textPrimaryKey)).getD schema.columns.length
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
  schema.primaryKey < schema.columns.length ∧
  (schema.columns[schema.primaryKey]?).any (·.integerPrimaryKey) ∧
  (schema.columns.filter (·.integerPrimaryKey)).length = 1 ∧
  namesUnique (schema.columns.map (·.name)) ∧
  schema.columns.findIdx? (·.integerPrimaryKey) = some schema.primaryKey ∧
  (∀ column ∈ schema.columns,
    column.integerPrimaryKey → column.notNull) ∧
  schema.CatalogShape

instance (schema : Schema) : Decidable schema.WellFormed := by
  unfold Schema.WellFormed namesUnique
  infer_instance

def Schema.visibleColumnIndices (schema : Schema) : List Nat :=
  (List.range schema.columns.length).filter fun index =>
    !(schema.primaryKey != schema.declaredPrimaryKey && index == schema.primaryKey)

def Schema.visibleColumns (schema : Schema) : List Column :=
  schema.visibleColumnIndices.filterMap fun index => schema.columns[index]?

/-- SQL declared-column names range over visible physical positions only.
The bookkeeping column of an implicit rowid is not a declared SQL name. -/
def Schema.declaredColumn? (schema : Schema) (name : String) : Option Nat :=
  schema.visibleColumnIndices.find? fun index =>
    (schema.columns[index]?).any (fun column => column.name.toLower == name.toLower)

theorem Schema.declaredColumn_visible (schema : Schema) (name : String) (index : Nat)
    (found : schema.declaredColumn? name = some index) :
    index ∈ schema.visibleColumnIndices :=
  List.mem_of_find?_eq_some found

/-- Declared columns shadow SQLite's three implicit rowid spellings. -/
def Schema.column? (schema : Schema) (name : String) : Option Nat :=
  match schema.declaredColumn? name with
  | some index => some index
  | none => if ["rowid", "oid", "_rowid_"].contains name.toLower then
      some schema.primaryKey else none

theorem Schema.column_visible_or_rowid (schema : Schema) (name : String) (index : Nat)
    (found : schema.column? name = some index) :
    index ∈ schema.visibleColumnIndices ∨
      (["rowid", "oid", "_rowid_"].contains name.toLower = true ∧ index = schema.primaryKey) := by
  cases declared : schema.declaredColumn? name with
  | some position =>
      have equal : position = index := by simpa [Schema.column?, declared] using found
      exact Or.inl (schema.declaredColumn_visible name index (equal ▸ declared))
  | none =>
      simp only [Schema.column?, declared] at found
      split at found
      next alias => exact Or.inr ⟨alias, (Option.some.inj found).symm⟩
      next => cases found

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
    have unique := List.pairwise_iff_getElem.mp wellFormed.2.2.2.1
      earlier index earlierNamesBound indexNamesBound earlierLt
    simpa using unique

structure Index where
  name : String
  column : Nat
  unique : Bool := false
  deriving DecidableEq, Repr

def Index.isImplicitPrimary (schema : Schema) (index : Index) : Bool :=
  schema.hasHiddenRowid &&
    index.name == "sqlite_autoindex_" ++ schema.name ++ "_1" &&
    index.column == schema.declaredPrimaryKey && !index.unique

def Index.WellFormed (schema : Schema) (index : Index) : Prop :=
  index.column < schema.columns.length

/-- SQLite identifiers may be empty. An index's local invariant is its column
bound; distinct names are checked separately for the complete index list. -/
theorem Index.wellFormed_rename (schema : Schema) (index : Index) (name : String) :
    ({ index with name } : Index).WellFormed schema ↔ index.WellFormed schema := Iff.rfl

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
  (column.notNull = true → value ≠ .null) ∧
    SQLite.PhysicalAffinity.accepts column.affinity value = true

instance (column : Column) (value : Value) : Decidable (columnAccepts column value) :=
  by unfold columnAccepts; infer_instance

def columnAcceptsBool (column : Column) (value : Value) : Bool :=
  (!column.notNull || value != .null) && SQLite.PhysicalAffinity.accepts column.affinity value

theorem columnAcceptsBool_iff (column : Column) (value : Value) :
    columnAcceptsBool column value = true ↔ columnAccepts column value := by
  unfold columnAcceptsBool columnAccepts
  cases notNull : column.notNull <;> simp_all

theorem columnRead_eq_self {column : Column} {value : Value}
    (accepted : columnAcceptsBool column value = true) :
    SQLite.PhysicalAffinity.read column.affinity value = value :=
  SQLite.PhysicalAffinity.read_eq_self ((columnAcceptsBool_iff _ _).mp accepted).2

theorem columnComparison_eq_self {column : Column} {value : Value}
    (accepted : columnAcceptsBool column value = true) :
    SQLite.PhysicalAffinity.comparison column.affinity value = value :=
  SQLite.PhysicalAffinity.comparison_eq_self ((columnAcceptsBool_iff _ _).mp accepted).2

def readColumnValues : List Column → List Value → List Value
  | column :: columns, value :: values =>
      SQLite.PhysicalAffinity.read column.affinity value :: readColumnValues columns values
  | _, values => values

theorem readColumnValues_eq_self (columns : List Column) (values : List Value)
    (accepted : (columns.zip values).all (fun pair => columnAcceptsBool pair.1 pair.2) = true) :
    readColumnValues columns values = values := by
  induction columns generalizing values with
  | nil => rfl
  | cons column columns induction =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at accepted
          simp only [readColumnValues, columnRead_eq_self accepted.1, induction values accepted.2]

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

/-- Row identities occupy a different namespace from stored SQL values.
This keeps nullable numeric primary keys disjoint from every NULL row. -/
inductive DeclaredKey where
  | rowid (identifier : Integer)
  | value (payload : Value)
  deriving DecidableEq

def DeclaredKey.orderKey : DeclaredKey → Bool × (Nat × (Option Int × (Option Nat ×
    (Option (List UInt8) × Option (List UInt8)))))
  | .rowid integer => (false, Value.orderKey (.integer integer))
  | .value payload => (true, payload.orderKey)

theorem DeclaredKey.orderKey_injective {left right : DeclaredKey}
    (equal : left.orderKey = right.orderKey) : left = right := by
  cases left with
  | rowid left =>
      cases right with
      | rowid right =>
          simp only [DeclaredKey.orderKey, Prod.mk.injEq, true_and] at equal
          have values := Value.orderKey_injective equal
          cases values
          rfl
      | value right => simp [DeclaredKey.orderKey] at equal
  | value left =>
      cases right with
      | rowid right => simp [DeclaredKey.orderKey] at equal
      | value right =>
          simp only [DeclaredKey.orderKey, Prod.mk.injEq, true_and] at equal
          exact congrArg DeclaredKey.value (Value.orderKey_injective equal)

theorem DeclaredKey.compareOn_orderKey_eq {left right : DeclaredKey} :
    compareOn DeclaredKey.orderKey left right = .eq ↔ left = right := by
  simp only [compareOn, Std.compare_eq_iff_eq]
  exact ⟨DeclaredKey.orderKey_injective, congrArg DeclaredKey.orderKey⟩

def Row.declaredKey (schema : Schema) (row : Row) : DeclaredKey :=
  match row.declaredPrimaryValue? schema with
  | none | some .null => .rowid row.rowid
  | some key => .value (SQLite.PrimaryKey.canonical key)

theorem Row.declaredKey_null (schema : Schema) (row : Row)
    (nullKey : row.declaredPrimaryValue? schema = some .null) :
    row.declaredKey schema = .rowid row.rowid := by
  simp [Row.declaredKey, nullKey]

theorem Row.declaredKey_null_injective (schema : Schema) (left right : Row)
    (leftNull : left.declaredPrimaryValue? schema = some .null)
    (rightNull : right.declaredPrimaryValue? schema = some .null) :
    left.declaredKey schema = right.declaredKey schema ↔ left.rowid = right.rowid := by
  rw [Row.declaredKey_null schema left leftNull, Row.declaredKey_null schema right rightNull]
  simp

theorem Row.declaredKey_nonnull (schema : Schema) (row : Row) (key : Value)
    (present : row.declaredPrimaryValue? schema = some key) (nonnull : key ≠ .null) :
    row.declaredKey schema = .value (SQLite.PrimaryKey.canonical key) := by
  cases key <;> simp_all [Row.declaredKey]

theorem Row.declaredKey_null_ne_nonnull (schema : Schema) (left right : Row) (key : Value)
    (leftNull : left.declaredPrimaryValue? schema = some .null)
    (rightValue : right.declaredPrimaryValue? schema = some key) (nonnull : key ≠ .null) :
    left.declaredKey schema ≠ right.declaredKey schema := by
  rw [Row.declaredKey_null schema left leftNull, Row.declaredKey_nonnull schema right key rightValue nonnull]
  simp

theorem Row.declaredKey_no_declared (schema : Schema) (row : Row)
    (absent : schema.declaredPrimaryKey? = none) :
    row.declaredKey schema = .rowid row.rowid := by
  simp [Row.declaredKey, Row.declaredPrimaryValue?, absent]

abbrev DeclaredKeyMap :=
  Std.TreeMap DeclaredKey Row (compareOn DeclaredKey.orderKey)

def buildDeclaredKeyMap (schema : Schema) (rows : List Row) :
    DeclaredKeyMap :=
  if schema.hasHiddenRowid then
    rows.foldr (fun row (map : DeclaredKeyMap) =>
      map.insert (row.declaredKey schema) row) ∅
  else ∅

end Core

end SQLeanite
