import SQLeanite.CoreCatalogSQL
import SQLeanite.CoreData.BuildDeclaredKeyMapGetOfHidden
import SQLeanite.PersistentPageTree.StoreReuseFreshGetDRootId

namespace SQLeanite
namespace Core
attribute [local instance] lexOrd

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
  catalogSource : Option (CoreCatalogSQL.Source schema) := none

/-- Exact retained catalog SQL, or the proved canonical printer for new schemas. -/
def Table.catalogSQL (table : Table) : String :=
  CoreCatalogSQL.text table.schema table.catalogSource

def Table.withoutRowid (table : Table) : Bool :=
  table.catalogSource.any (fun source => CoreCatalogSQL.withoutRowid source.text)

theorem Table.parse_catalogSQL (table : Table) :
    CoreCatalogSQL.parse table.catalogSQL = some table.schema :=
  CoreCatalogSQL.parse_text table.schema
    (CanonicalSchemaSQL.Printable.ofWellFormed table.schema table.schemaWellFormed)
    table.catalogSource

/-- Attach exact catalog text only after checking that it describes this
table's existing schema. The row tree and index metadata are retained. -/
def Table.withCatalogSQL (table : Table) (sql : String) : Except String Table :=
  if decoded : CoreCatalogSQL.parse sql = some table.schema then
    .ok { table with catalogSource := CoreCatalogSQL.retain table.schema sql decoded }
  else .error "catalog SQL does not describe the table schema"

/-- The sole logical row view.  Rows are no longer stored alongside the tree:
they are the abstraction of the proof-carrying persistent representation. -/
def Table.rows (table : Table) : List Row := storedRows table.rowTree

theorem Table.withCatalogSQL_preserves {table after : Table} {sql : String}
    (success : table.withCatalogSQL sql = .ok after) :
    after.schema = table.schema ∧ after.indexes = table.indexes ∧
      after.rows = table.rows ∧ after.catalogSQL = sql := by
  unfold Table.withCatalogSQL at success
  split at success
  next decoded =>
    injection success with equal
    subst after
    exact ⟨rfl, rfl, rfl, CoreCatalogSQL.text_retain table.schema sql decoded⟩
  next => contradiction

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

def Table.rebuild (schema : Schema) (indexes : List Index) (rows : List Row)
    (catalogSource : Option (CoreCatalogSQL.Source schema) := none) :
    Except String Table :=
  if schemaWF : schema.WellFormed then
    if indexesWF : IndexesWellFormed schema indexes then
      if rowsWF : RowsWellFormed schema rows then
        .ok {
          schema
          indexes
          catalogSource
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
    {catalogSource : Option (CoreCatalogSQL.Source schema)}
    (success : Table.rebuild schema indexes rows catalogSource = .ok table) :
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

/-- Validate retained SQL against the exact schema before rebuilding its rows.
The decoder already parsed this text; the check also makes this constructor
safe for every other caller. -/
def Table.rebuildFromCatalog (schema : Schema) (indexes : List Index)
    (rows : List Row) (sql : String) : Except String Table :=
  if decoded : CoreCatalogSQL.parse sql = some schema then
    Table.rebuild schema indexes rows (CoreCatalogSQL.retain schema sql decoded)
  else .error "catalog SQL does not describe the table schema"

theorem Table.rebuildFromCatalog_exact {schema : Schema} {indexes : List Index}
    {rows : List Row} {sql : String} {table : Table}
    (success : Table.rebuildFromCatalog schema indexes rows sql = .ok table) :
    table.schema = schema ∧ table.indexes = indexes ∧ table.rows = rows := by
  unfold Table.rebuildFromCatalog at success
  split at success
  next => exact Table.rebuild_exact success
  next => contradiction

theorem Table.rebuildFromCatalog_catalogSQL (table : Table)
    (indexes : List Index) (rows : List Row) :
    Table.rebuildFromCatalog table.schema indexes rows table.catalogSQL =
      Table.rebuild table.schema indexes rows table.catalogSource := by
  unfold Table.rebuildFromCatalog
  rw [dif_pos table.parse_catalogSQL]
  exact congrArg (fun source => Table.rebuild table.schema indexes rows source)
    (CoreCatalogSQL.retain_text table.schema table.catalogSource table.parse_catalogSQL)

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

@[simp] theorem Table.withoutIndexes_catalogSource (table : Table) :
    table.withoutIndexes.catalogSource = table.catalogSource := rfl

@[simp] theorem Table.withoutIndexes_rows (table : Table) :
    table.withoutIndexes.rows = table.rows := by
  exact buildRowTree_rows table.rowsWellFormed.2

theorem Table.rebuild_withoutIndexes (table : Table) :
    Table.rebuild table.schema [] table.rows table.catalogSource = .ok table.withoutIndexes := by
  unfold Table.rebuild
  rw [dif_pos table.schemaWellFormed]
  rw [dif_pos (by simp [IndexesWellFormed, namesUnique])]
  split
  next => congr 1
  next invalid => exact False.elim (invalid table.rowsWellFormed)

theorem Table.rebuild_withoutIndexes_fixed {schema : Schema}
    {rows : List Row} {table : Table}
    {source : Option (CoreCatalogSQL.Source schema)}
    (success : Table.rebuild schema [] rows source = .ok table) :
    table.withoutIndexes = table := by
  unfold Table.rebuild at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success
  next rowsWF =>
    injection success with equal
    subst table
    simp only [Table.withoutIndexes, Table.rows]
    simp only [buildRowTree_rows rowsWF.2]
  next => contradiction

theorem Table.rebuildFromCatalog_withoutIndexes_fixed {schema : Schema}
    {rows : List Row} {sql : String} {table : Table}
    (success : Table.rebuildFromCatalog schema [] rows sql = .ok table) :
    table.withoutIndexes = table := by
  unfold Table.rebuildFromCatalog at success
  split at success
  next => exact Table.rebuild_withoutIndexes_fixed success
  next => contradiction

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

/-- Canonical rebuilding is a projection, not merely a logical equivalence.
This exact fixed-point fact lets a validating physical open expose the
component-wise decoder invariant required by later page-local writes. -/
@[simp] theorem Table.canonicalize_idempotent (table : Table) :
    table.canonicalize.canonicalize = table.canonicalize := by
  cases table with
  | mk schema indexes rowTree rowTreeWellKeyed declaredKeyMap
      declaredKeyMapRepresents schemaWellFormed indexesWellFormed
      rowsWellFormed catalogSource =>
    simp only [Table.canonicalize, Table.rows]
    simp only [buildRowTree_rows rowsWellFormed.2]

/-- Every table constructed by the checked rebuilder is already an exact
fixed point of canonicalization.  This is stronger than merely having the
same logical rows and is useful at serialization boundaries. -/
theorem Table.rebuild_canonicalize_fixed {schema : Schema}
    {indexes : List Index} {rows : List Row} {table : Table}
    {catalogSource : Option (CoreCatalogSQL.Source schema)}
    (success : Table.rebuild schema indexes rows catalogSource = .ok table) :
    table.canonicalize = table := by
  unfold Table.rebuild at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success
  next rowsWF =>
    injection success with equal
    subst table
    simp only [Table.canonicalize, Table.rows]
    simp only [buildRowTree_rows rowsWF.2]
  next => contradiction

theorem Table.rebuild_self (table : Table) :
    Table.rebuild table.schema table.indexes table.rows table.catalogSource =
      .ok table.canonicalize := by
  unfold Table.rebuild
  rw [dif_pos table.schemaWellFormed]
  rw [dif_pos table.indexesWellFormed]
  split
  next => congr 1
  next invalid => exact False.elim (invalid table.rowsWellFormed)

theorem Table.rebuild_withoutIndexesRows (table : Table) :
    Table.rebuild table.schema table.indexes table.withoutIndexes.rows table.catalogSource =
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

def rowConstraintError (schema : Schema) (values : List Value) : String :=
  match (schema.columns.zip values).find? (fun (column,value) => column.notNull && value == .null) with
  | some (column,_) => s!"NOT NULL constraint failed: {schema.name}.{column.name}"
  | none => "row violates width or NOT NULL constraints"

def Row.create (schema : Schema) (values : List Value) : Except String Row :=
  match values[schema.primaryKey]? with
  | some (.integer rowid) =>
      let row : Row := ⟨rowid, values⟩
      if row.WellFormed schema then .ok row
      else .error (rowConstraintError schema values)
  | _ => .error "INTEGER PRIMARY KEY must be an integer"

/-- Fill the hidden rowid slot used to lower a non-integer SQLite primary key
before applying the ordinary row invariant. -/
def Row.createWithRowid (schema : Schema) (rowid : Integer)
    (values : List Value) : Except String Row :=
  if schema.hasHiddenRowid then
    Row.create schema (values.set schema.primaryKey (.integer rowid))
  else Row.create schema values

theorem Row.create_set_rowid {schema : Schema} {rowid : Integer}
    {values : List Value} {row : Row}
    (created : Row.create schema (values.set schema.primaryKey (.integer rowid)) = .ok row) :
    row.rowid = rowid := by
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

theorem Row.createWithRowid_rowid {schema : Schema} {rowid : Integer}
    {values : List Value} {row : Row}
    (hidden : schema.hasHiddenRowid = true)
    (created : Row.createWithRowid schema rowid values = .ok row) :
    row.rowid = rowid := by
  apply Row.create_set_rowid
  simpa [Row.createWithRowid, hidden] using created

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
    | some row => row.rowid.value + 1
  if upper : next < Int.ofNat FileFormat.IntegerWidth.eight.midpoint then
    some ⟨next, by
      dsimp only [next]
      cases table.lastRow? with
      | none => decide
      | some row =>
          change -(Int.ofNat FileFormat.IntegerWidth.eight.midpoint) ≤ row.rowid.value + 1
          have := row.rowid.lowerBound
          omega, upper⟩
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
      next upper =>
        injection generated with equal
        subst rowid
        change row.rowid.value < last.rowid.value + 1
        omega
      next => contradiction

/-- Retained CHECK clauses are executable constraints, not ordinary schema
annotations. Canonical tables have no checks and avoid reparsing their SQL. -/
def Table.hasChecks (table : Table) : Bool :=
  table.catalogSource.any fun source =>
    (match source.compiledStrictColumns with | .ok columns => columns.isSome | .error _ => true) ||
    (match source.compiledChecks with | .ok checks => !checks.isEmpty | .error _ => true)

def Table.checkFailure (table : Table) (row : Row) (assigned : Option (List Nat) := none) :
    Except String (Option String) := do
  let some source := table.catalogSource | return none
  if let some columns ← source.compiledStrictColumns then CoreStrictSyntax.require table.schema.name columns row.values
  CoreCheck.failure table.schema (CoreCheck.forUpdate table.schema assigned (← source.compiledChecks)) row

def Table.requireChecks (table : Table) (row : Row) (assigned : Option (List Nat) := none) : Except String Unit := do
  if let some message ← table.checkFailure row assigned then throw message

end Core

end SQLeanite
