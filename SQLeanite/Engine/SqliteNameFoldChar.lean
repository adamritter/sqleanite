import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import SQLeanite.Syntax.TableConstraintDef

namespace SQLeanite

/-- SQLite folds only ASCII letters when comparing schema identifiers. Keeping
this definition structurally transparent also lets the kernel reduce concrete
identifier comparisons used inside proofs. -/
def sqliteNameFoldChar (character : Char) : Char :=
  if 'A' ≤ character && character ≤ 'Z' then Char.ofNat (character.toNat + 32)
  else character

def sqliteNameFold (name : String) : String :=
  String.mk (name.toList.map sqliteNameFoldChar)

def nameEq (a b : String) : Bool := sqliteNameFold a == sqliteNameFold b

def CompoundOp.sqlName : CompoundOp → String
  | .unionAll => "UNION ALL"
  | .unionDistinct => "UNION"
  | .except => "EXCEPT"
  | .intersect => "INTERSECT"

def RowsHaveWidth (rows : Array (Array Value)) (width : Nat) : Prop :=
  ∀ row, row ∈ rows → row.size = width

def combineCompoundRows (operation : CompoundOp) (left right : Array (Array Value)) :
    Array (Array Value) :=
  match operation with
  | .unionAll | .unionDistinct => left ++ right
  | .except => left.filter fun row => !right.contains row
  | .intersect => left.filter fun row => right.contains row

theorem combineCompoundRows_preserves_width {operation : CompoundOp} {left right : Array (Array Value)}
    {width : Nat} (leftWidth : RowsHaveWidth left width) (rightWidth : RowsHaveWidth right width) :
    RowsHaveWidth (combineCompoundRows operation left right) width := by
  intro row membership
  cases operation with
  | unionAll | unionDistinct =>
    simp only [combineCompoundRows, Array.mem_append] at membership
    exact membership.elim (leftWidth row) (rightWidth row)
  | except | intersect =>
    simp only [combineCompoundRows, Array.mem_filter] at membership
    exact leftWidth row membership.1

structure Column where
  name : String
  declaredType : String := ""
  defaultValue : Value := .null
  generated : Option Expr := none
  notNull : Bool := false
  notNullConflict : ConflictAction := .abort
  primaryKey : Bool := false
  unique : Bool := false
  conflict : ConflictAction := .abort
  collation : String := "binary"
  references : Option ForeignKeyDef := none
  check : Option CheckDef := none
  defaultSql : Option String := none
  autoIncrement : Bool := false
  deriving Repr, Inhabited

structure StoredRow where
  rowid : Int
  values : Array Value
  deriving Repr, Inhabited

def StoredRowsHaveWidth (rows : Array StoredRow) (width : Nat) : Prop :=
  ∀ row, row ∈ rows → row.values.size = width

/-- Physical rows bundled with the schema-width invariant. There is no public
way to put an arbitrary `Array StoredRow` into a table: callers must either
prove the width or pass through `checked`. -/
structure RowStore (width : Nat) where
  data : Array StoredRow
  widthInvariant : StoredRowsHaveWidth data width

instance : Repr (RowStore width) where
  reprPrec rows precedence := reprPrec rows.data precedence
namespace RowStore

def empty : RowStore width := ⟨#[], by simp [StoredRowsHaveWidth]⟩

def checked (rows : Array StoredRow) (width : Nat) : Except String (RowStore width) :=
  match invariant : rows.all (fun row => row.values.size == width) with
  | true => .ok ⟨rows, by
      intro row membership
      have rowWidth := (Array.all_eq_true_iff_forall_mem.mp invariant) row membership
      simpa using rowWidth⟩
  | false => .error s!"physical row width does not match declared width {width}"

def push (rows : RowStore width) (row : StoredRow)
    (rowWidth : row.values.size = width) : RowStore width :=
  ⟨rows.data.push row, by
    intro candidate membership
    simp only [Array.mem_push] at membership
    exact membership.elim (rows.widthInvariant candidate) (fun added => added ▸ rowWidth)⟩

def filter (rows : RowStore width) (keep : StoredRow → Bool) : RowStore width :=
  ⟨rows.data.filter keep, by
    intro row membership
    exact rows.widthInvariant row (Array.mem_filter.mp membership).1⟩

def set! (rows : RowStore width) (index : Nat) (row : StoredRow)
    (rowWidth : row.values.size = width) : RowStore width :=
  ⟨rows.data.set! index row, by
    intro candidate membership
    have either := Array.mem_or_eq_of_mem_setIfInBounds (by simpa using membership)
    exact either.elim (rows.widthInvariant candidate) (fun equal => equal ▸ rowWidth)⟩

def map (rows : RowStore width) (transform : StoredRow → StoredRow)
    (newWidth : Nat) (preserves : ∀ row, row ∈ rows.data →
      (transform row).values.size = newWidth) : RowStore newWidth :=
  ⟨rows.data.map transform, by
    intro row membership
    rcases Array.mem_map.mp membership with ⟨source, sourceMembership, rfl⟩
    exact preserves source sourceMembership⟩
end RowStore

structure UniqueIndex where
  columns : Array Nat
  expressions : Array Expr := #[]
  where_ : Option Expr := none
  name : String := ""
  conflict : ConflictAction := .abort
  primaryKey : Bool := false
  deriving Repr

structure SchemaIndex where
  name : String
  table : String
  columns : Array String
  expressions : Array Expr := #[]
  unique : Bool := false
  automatic : Bool := false
  deriving Repr

def SchemaIndex.sql (index : SchemaIndex) : String :=
  "CREATE " ++ (if index.unique then "UNIQUE " else "") ++ "INDEX " ++ index.name ++
    " ON " ++ index.table ++ "(" ++ String.intercalate ","
      (if index.expressions.isEmpty then index.columns.toList
       else index.expressions.toList.map Expr.sql) ++ ")"

structure Table where
  name : String
  columns : Array Column
  rowStore : RowStore columns.size := RowStore.empty
  nextRowid : Int := 1
  uniqueIndexes : Array UniqueIndex := #[]
  checks : Array CheckDef := #[]
  deriving Repr

def Table.rows (table : Table) : Array StoredRow := table.rowStore.data

def Table.withRows (table : Table) (rows : Array StoredRow)
    (invariant : StoredRowsHaveWidth rows table.columns.size) : Table :=
  { table with rowStore := ⟨rows, invariant⟩ }

def Table.withRowsChecked (table : Table) (rows : Array StoredRow) : Except String Table := do
  let rowStore ← RowStore.checked rows table.columns.size
  pure { table with rowStore }

def Table.withColumnsChecked (table : Table) (columns : Array Column) : Except String Table :=
  if sameSize : columns.size = table.columns.size then
    .ok { table with columns, rowStore := sameSize.symm ▸ table.rowStore }
  else .error "replacement schema changes the physical row width"

def Table.usesAutoincrement (table : Table) : Bool :=
  table.columns.any (·.autoIncrement)

def Table.sql (table : Table) : String :=
  "CREATE TABLE " ++ table.name ++ "(" ++ String.intercalate ","
    (table.columns.toList.map fun column =>
      column.name ++ (if column.declaredType.isEmpty then "" else " " ++ column.declaredType)) ++ ")"

structure Trigger where
  name : String
  table : String
  event : TriggerEvent
  timing : TriggerTiming
  when_ : Option Expr
  body : Array Statement
  temporary : Bool := false
  sourceSql : String := ""
  deriving Repr

structure View where
  name : String
  columns : Option (Array String)
  query : Select
  temporary : Bool := false
  sourceSql : String := ""
  deriving Repr

structure DatabaseSnapshot where
  tables : List Table
  views : List View
  triggers : List Trigger
  indexes : List SchemaIndex
  deriving Repr

/-- Every physical row has exactly the width declared by its schema. -/
def Table.WellFormed (t : Table) : Prop :=
  ∀ r, r ∈ t.rows → r.values.size = t.columns.size

theorem Table.wellFormed (table : Table) : table.WellFormed :=
  table.rowStore.widthInvariant

/-- Every allocated rowid is strictly below the next-rowid upper bound. -/
def Table.RowidsBounded (t : Table) : Prop :=
  ∀ r, r ∈ t.rows → r.rowid < t.nextRowid

def Table.insertChecked (t : Table) (row : StoredRow) : Except String Table :=
  if rowWidth : row.values.size = t.columns.size then
    let withRow := { t with rowStore := t.rowStore.push row rowWidth }
    .ok { withRow with nextRowid := max t.nextRowid (row.rowid + 1) }
  else .error s!"table {t.name} has {t.columns.size} columns but {row.values.size} values were supplied"

theorem Table.insertChecked_advances_nextRowid {t t' : Table} {row : StoredRow}
    (ok : t.insertChecked row = .ok t') : row.rowid + 1 ≤ t'.nextRowid := by
  simp only [Table.insertChecked] at ok
  split at ok
  next rowWidth =>
    simp only [Except.ok.injEq] at ok
    subst t'
    exact Int.le_max_right _ _
  next _ => contradiction

theorem Table.insertChecked_preserves_rowid_bound {t t' : Table} {row : StoredRow}
    (h : t.RowidsBounded) (ok : t.insertChecked row = .ok t') : t'.RowidsBounded := by
  simp only [Table.insertChecked] at ok
  split at ok
  next rowWidth =>
    simp only [Except.ok.injEq] at ok
    subst t'
    intro candidate membership
    change candidate ∈ (t.rowStore.push row rowWidth).data at membership
    simp only [RowStore.push, Array.mem_push] at membership
    cases membership with
    | inl old =>
      exact Int.lt_of_lt_of_le (h candidate old) (Int.le_max_left _ _)
    | inr added =>
      simpa [added] using
        Int.lt_of_lt_of_le (Int.lt_succ row.rowid)
          (Int.le_max_right t.nextRowid (row.rowid + 1))
  next _ => contradiction

def Table.retainRows (t : Table) (keep : StoredRow → Bool) : Table :=
  { t with rowStore := t.rowStore.filter keep }

def Table.addColumn (t : Table) (column : Column) : Table :=
  { t with
    columns := t.columns.push column
    rowStore := t.rowStore.map
      (fun row => { row with values := row.values.push column.defaultValue })
      (t.columns.push column).size (by
        intro row membership
        simp [t.rowStore.widthInvariant row membership])
    checks := column.check.map (t.checks.push ·) |>.getD t.checks }

structure Database where
  tables : List Table := []
  views : List View := []
  triggers : List Trigger := []
  indexes : List SchemaIndex := []
  transactionSnapshot : Option DatabaseSnapshot := none
  shortColumnNames : Bool := true
  fullColumnNames : Bool := false
  foreignKeys : Bool := false
  countChanges : Bool := false
  recursiveTriggers : Bool := false
  ignoreCheckConstraints : Bool := false
  checkMyfuncEnabled : Bool := false
  writableSchema : Bool := false
  readOnly : Bool := false
  viewsEnabled : Bool := true
  doubleQuotedStrings : Bool := true
  viewStack : List String := []
  ignoreTempViews : Bool := false
  viewDepthLimit : Nat := 1000
  /-- Unix timestamp used by the stable SQL date/time functions. -/
  currentTime : Int := 0
  lastInsertRowid : Int := 0
  deriving Repr

/-- Every table in a database has rows matching its declared schema width.
This is now true by construction because `Table` stores a `RowStore`. -/
def Database.WellFormed (database : Database) : Prop :=
  ∀ table, table ∈ database.tables → table.WellFormed

theorem Database.wellFormed (database : Database) : database.WellFormed := by
  intro table _
  exact table.wellFormed

def Database.restoreSnapshot (database : Database) (snapshot : DatabaseSnapshot) : Database :=
  { database with
    tables := snapshot.tables
    views := snapshot.views
    triggers := snapshot.triggers
    indexes := snapshot.indexes
    transactionSnapshot := none }

theorem Database.restoreSnapshot_closes_transaction (database : Database)
    (snapshot : DatabaseSnapshot) :
    (database.restoreSnapshot snapshot).transactionSnapshot = none := by rfl

theorem Database.restoreSnapshot_restores_tables (database : Database)
    (snapshot : DatabaseSnapshot) :
    (database.restoreSnapshot snapshot).tables = snapshot.tables := by rfl

structure QueryResult where
  columns : Array String := #[]
  rows : Array (Array Value) := #[]
  changes : Nat := 0
  reportsChanges : Bool := false
  deferredError : Option String := none
  deriving Repr, Inhabited

structure Binding where
  table : String
  alias : String
  column : String
  value : Value
  hidden : Bool := false
  depth : Nat := 0
  collation : String := "binary"
  declaredType : String := ""
  deriving Repr, Inhabited

abbrev Env := Array Binding

def Binding.matchesQualifier (binding : Binding) (qualifier : String) : Bool :=
  nameEq binding.alias qualifier || nameEq binding.table qualifier

theorem Binding.matches_own_table (binding : Binding) :
    binding.matchesQualifier binding.table = true := by
  simp [Binding.matchesQualifier, nameEq]

theorem Binding.matches_own_alias (binding : Binding) :
    binding.matchesQualifier binding.alias = true := by
  simp [Binding.matchesQualifier, nameEq]

def Binding.outerScoped (binding : Binding) : Binding :=
  { binding with depth := binding.depth + 1 }

theorem Binding.outerScoped_has_greater_depth (binding : Binding) :
    binding.depth < binding.outerScoped.depth := by
  simp [Binding.outerScoped]

def charsStartWith : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | actual :: rest, expected :: suffix => actual == expected && charsStartWith rest suffix

def charsContain : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | source@(_ :: rest), pattern => charsStartWith source pattern || charsContain rest pattern

def stringContains (source pattern : String) : Bool :=
  charsContain source.toList pattern.toList

def typeContains (declaredType fragment : String) : Bool :=
  charsContain declaredType.toUpper.toList fragment.toList

def hasTextAffinity (declaredType : String) : Bool :=
  typeContains declaredType "CHAR" || typeContains declaredType "CLOB" ||
    typeContains declaredType "TEXT"

def hasNoAffinity (declaredType : String) : Bool :=
  declaredType.isEmpty || typeContains declaredType "BLOB"

def hasNumericAffinity (declaredType : String) : Bool :=
  !hasTextAffinity declaredType && !hasNoAffinity declaredType

def inSigned64Range (value : Int) : Bool :=
  -9223372036854775808 <= value && value <= 9223372036854775807

def parseInteger64? (source : String) : Option Int := do
  let value ← source.trimAscii.toString.toInt?
  if inSigned64Range value then some value else none

def exactInteger? (number : Float) : Option Int := do
  if !number.isFinite then none else
  -- IEEE-754 rounds Int64.max to 2^63.  Check the upper endpoint before
  -- converting, otherwise 2^63 can masquerade as the saturated Int64.max.
  if number >= Float.ofInt 9223372036854775808 then none else
  let integer := number.toInt64.toInt
  if inSigned64Range integer && Float.ofInt integer == number then some integer else none

/-- SQLite column affinity, applied when a value crosses the persistent row boundary. -/
def Column.applyAffinity (column : Column) (value : Value) : Value :=
  match value with
  | .null => .null
  | value =>
    if typeContains column.declaredType "INT" then
      match value with
      | .text source =>
        let source := source.trimAscii.toString
        match parseInteger64? source with
        | some integer => .integer integer
        | none =>
          match parseDecimal? source with
          | some number => exactInteger? number |>.map Value.integer |>.getD (.real number)
          | none => value
      | .real number => exactInteger? number |>.map Value.integer |>.getD value
      | other => other
    else if hasTextAffinity column.declaredType then
      match value with
      | .integer _ | .real _ => .text (toString value)
      | other => other
    else if typeContains column.declaredType "REAL" || typeContains column.declaredType "FLOA" ||
        typeContains column.declaredType "DOUB" then
      match value.toFloat? with
      | some number => .real number
      | none => value
    else if hasNoAffinity column.declaredType then value
    else
      match value with
      | .text source =>
        let source := source.trimAscii.toString
        match parseInteger64? source with
        | some integer => .integer integer
        | none =>
          match parseDecimal? source with
          | some number => exactInteger? number |>.map Value.integer |>.getD (.real number)
          | none => value
      | .real number => exactInteger? number |>.map Value.integer |>.getD value
      | other => other

theorem Column.applyAffinity_null (column : Column) : column.applyAffinity .null = .null := by
  rfl

theorem Column.applyAffinity_integer_for_integer_type (column : Column) (value : Int)
    (h : typeContains column.declaredType "INT" = true) :
    column.applyAffinity (.integer value) = .integer value := by
  simp [Column.applyAffinity, h]

def unqualifiedName (name : String) : String :=
  name.splitOn "." |>.getLast?.getD name

def findTable? (db : Database) (name : String) : Option Table :=
  if name.toList.contains '.' then
    (db.tables.find? (fun table => nameEq table.name name)).orElse fun _ =>
      if (sqliteNameFold name).startsWith "main." then
        db.tables.find? (fun table => nameEq table.name (name.drop 5).toString)
      else none
  else (db.tables.find? (fun table => table.name.toLower.startsWith "temp." &&
      nameEq (unqualifiedName table.name) name)).orElse fun _ =>
    (db.tables.find? (fun table => nameEq table.name name)).orElse fun _ =>
      db.tables.find? (fun table => nameEq (unqualifiedName table.name) name)

def reservedSchemaName (name : String) : Bool :=
  (unqualifiedName name).toLower.startsWith "sqlite_"

def findView? (db : Database) (name : String) : Option View :=
  let name := unqualifiedName name
  if db.ignoreTempViews then db.views.find? (fun view => !view.temporary && nameEq view.name name)
  else (db.views.find? (fun view => view.temporary && nameEq view.name name)).orElse fun _ =>
      db.views.find? (fun view => !view.temporary && nameEq view.name name)

def replaceTable (db : Database) (table : Table) : Database :=
  { db with tables := db.tables.map fun t => if nameEq t.name table.name then table else t }

def removeTable (db : Database) (name : String) : Database :=
  { db with tables := db.tables.filter fun t => !nameEq t.name name }

def sqliteSequenceTable : Table := {
  name := "sqlite_sequence"
  columns := #[{ name := "name" }, { name := "seq" }]
}

end SQLeanite
