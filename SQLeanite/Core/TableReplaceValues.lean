import SQLeanite.Core.FindOrderedUpsertOfTrue

namespace SQLeanite
namespace Core
attribute [local instance] lexOrd

/-- INSERT OR REPLACE: overwrite any row with the same rowid instead of
failing. `orderedUpsert` already replaces on an equal key, so this is
`insertValues` without the duplicate check. -/
def Table.replaceValues (table : Table) (values : List Value) :
    Except String Table :=
  match table.createReplacementRow values with
  | .error message => .error message
  | .ok row =>
      if table.uniqueConflict row true then .error (table.uniqueConflictMessage row true)
      else if valid : row.WellFormed table.schema then .ok (table.upsert row valid)
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
      split at success <;> try contradiction
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
      split at success <;> try contradiction
      injection success with equal
      subst next
      rfl

def Table.withIndexes (table : Table) (indexes : List Index) :
    Except String Table :=
  if valid : IndexesWellFormed table.schema indexes then
    if uniqueIndexesAccept indexes table.rows then
      .ok { table with indexes, indexesWellFormed := valid }
    else .error (uniqueRowsError table.schema indexes table.rows)
  else .error "invalid index metadata"

theorem Table.withIndexes_exact {table next : Table} {indexes : List Index}
    (success : table.withIndexes indexes = .ok next) :
    next.schema = table.schema ∧ next.indexes = indexes ∧
      next.rows = table.rows := by
  unfold Table.withIndexes at success
  split at success
  next =>
    split at success <;> try contradiction
    injection success with equal
    subst next
    exact ⟨rfl, rfl, rfl⟩
  next => contradiction

/-- Retain catalog creation order so default SQLite planner ties and file
reopening agree. New indexes are last in the catalog, first in planner order. -/
def Table.addIndex (table : Table) (index : Index) : Except String Table :=
  if table.indexes.any (fun existing => existing.name == index.name) then
    .error s!"index already exists: {index.name}"
  else table.withIndexes (table.indexes ++ [index])

theorem Table.addIndex_exact {table next : Table} {index : Index}
    (success : table.addIndex index = .ok next) :
    next.schema = table.schema ∧ next.indexes = table.indexes ++ [index] ∧
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
def Table.contents (table : Table) : Schema × List Index × List Row × String :=
  (table.schema, table.indexes, table.rows, table.catalogSQL)

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
  unfold Table.Equiv Table.contents Table.canonicalize Table.rows Table.catalogSQL
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
    congrArg (fun contents => contents.2.2.1) equivalent

theorem Table.Equiv.catalogSQL_eq {left right : Table}
    (equivalent : left.Equiv right) : left.catalogSQL = right.catalogSQL := by
  simpa [Table.Equiv, Table.contents] using
    congrArg (fun contents => contents.2.2.2) equivalent

def Database.contents (database : Database) :
    List (Schema × List Index × List Row × String) :=
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
    simpa only [List.map_map, Function.comp_def,
      Table.withoutIndexes_schema] using valid }

def Database.canonicalize (database : Database) : Database := {
  tables := database.tables.map Table.canonicalize
  tablesWellFormed := by
    have valid := database.tablesWellFormed
    unfold TablesWellFormed at valid ⊢
    simpa only [List.map_map, Function.comp_def, Table.canonicalize]
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

/-- Database canonicalization inherits the exact projection law tablewise. -/
@[simp] theorem Database.canonicalize_idempotent (database : Database) :
    database.canonicalize.canonicalize = database.canonicalize := by
  cases database
  simp [Database.canonicalize, Table.canonicalize_idempotent]

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
  Table.rebuild table.schema table.indexes (table.rows.filter keep) table.catalogSource

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
      else Table.rebuild table.schema table.indexes rows table.catalogSource
  | none => Table.rebuild table.schema table.indexes rows table.catalogSource

end Core

end SQLeanite
