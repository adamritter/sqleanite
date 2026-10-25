import SQLeanite.Parser
import SQLeanite.Record
import SQLeanite.SQLite.Scalar
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

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

private def charsStartWith : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | actual :: rest, expected :: suffix => actual == expected && charsStartWith rest suffix

private def charsContain : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | source@(_ :: rest), pattern => charsStartWith source pattern || charsContain rest pattern

private def stringContains (source pattern : String) : Bool :=
  charsContain source.toList pattern.toList

private def typeContains (declaredType fragment : String) : Bool :=
  charsContain declaredType.toUpper.toList fragment.toList

private def hasTextAffinity (declaredType : String) : Bool :=
  typeContains declaredType "CHAR" || typeContains declaredType "CLOB" ||
    typeContains declaredType "TEXT"

private def hasNoAffinity (declaredType : String) : Bool :=
  declaredType.isEmpty || typeContains declaredType "BLOB"

private def hasNumericAffinity (declaredType : String) : Bool :=
  !hasTextAffinity declaredType && !hasNoAffinity declaredType

private def inSigned64Range (value : Int) : Bool :=
  -9223372036854775808 <= value && value <= 9223372036854775807

private def parseInteger64? (source : String) : Option Int := do
  let value ← source.trimAscii.toString.toInt?
  if inSigned64Range value then some value else none

private def exactInteger? (number : Float) : Option Int := do
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

private def unqualifiedName (name : String) : String :=
  name.splitOn "." |>.getLast?.getD name

private def findTable? (db : Database) (name : String) : Option Table :=
  if name.toList.contains '.' then db.tables.find? (fun table => nameEq table.name name)
  else (db.tables.find? (fun table => table.name.toLower.startsWith "temp." &&
      nameEq (unqualifiedName table.name) name)).orElse fun _ =>
    (db.tables.find? (fun table => nameEq table.name name)).orElse fun _ =>
      db.tables.find? (fun table => nameEq (unqualifiedName table.name) name)

private def reservedSchemaName (name : String) : Bool :=
  (unqualifiedName name).toLower.startsWith "sqlite_"

private def findView? (db : Database) (name : String) : Option View :=
  let name := unqualifiedName name
  if db.ignoreTempViews then db.views.find? (fun view => !view.temporary && nameEq view.name name)
  else (db.views.find? (fun view => view.temporary && nameEq view.name name)).orElse fun _ =>
      db.views.find? (fun view => !view.temporary && nameEq view.name name)

private def replaceTable (db : Database) (table : Table) : Database :=
  { db with tables := db.tables.map fun t => if nameEq t.name table.name then table else t }

private def removeTable (db : Database) (name : String) : Database :=
  { db with tables := db.tables.filter fun t => !nameEq t.name name }

private def sqliteSequenceTable : Table := {
  name := "sqlite_sequence"
  columns := #[{ name := "name" }, { name := "seq" }]
}

private def ensureSequenceTable (db : Database) : Database :=
  if (findTable? db "sqlite_sequence").isSome then db
  else { db with tables := db.tables ++ [sqliteSequenceTable] }

private def recordAutoincrement (db : Database) (table : Table) (rowid : Int) : Database :=
  if !table.usesAutoincrement then db
  else
    let state := ensureSequenceTable db
    let sequence := (findTable? state "sqlite_sequence").getD sqliteSequenceTable
    let index := sequence.rows.findIdx? fun row =>
      row.values[0]?.any (fun value => match value with
        | .text name => nameEq name (unqualifiedName table.name)
        | _ => false)
    let candidate := max 0 rowid
    let updated := match index with
      | some position =>
        let old := sequence.rows[position]!
        let high := max (old.values[1]?.bind Value.toInt? |>.getD 0) candidate
        let row : StoredRow :=
          { old with values := #[.text (unqualifiedName table.name), .integer high] }
        let rows := sequence.rows.set! position row
        let rowStore := (RowStore.checked rows sequence.columns.size).toOption.getD sequence.rowStore
        { sequence with rowStore }
      | none =>
        let row := StoredRow.mk sequence.nextRowid
          #[.text (unqualifiedName table.name), .integer candidate]
        let rows := sequence.rows.push row
        let rowStore := (RowStore.checked rows sequence.columns.size).toOption.getD sequence.rowStore
        let withRows := { sequence with rowStore }
        { withRows with nextRowid := sequence.nextRowid + 1 }
    replaceTable state updated

private def removeAutoincrementRecord (db : Database) (tableName : String) : Database :=
  match findTable? db "sqlite_sequence" with
  | none => db
  | some sequence => replaceTable db (sequence.retainRows fun row =>
      !row.values[0]?.any (fun value => match value with
        | .text name => nameEq name (unqualifiedName tableName)
        | _ => false))

private def applySequenceHighWater (db : Database) : Database :=
  match findTable? db "sqlite_sequence" with
  | none => db
  | some sequence =>
    sequence.rows.foldl (init := db) fun state row =>
      match row.values[0]?, row.values[1]?.bind Value.toInt? with
      | Option.some (Value.text name), Option.some high =>
        match findTable? state name with
        | some table =>
          if table.usesAutoincrement then
            replaceTable state { table with nextRowid := max table.nextRowid (high + 1) }
          else state
        | none => state
      | _, _ => state

private def resolveColumn (env : Env) (qualifier : Option String) (name : String) : Except String Value := do
  let found := env.filter fun b =>
    nameEq b.column name && qualifier.all b.matchesQualifier
  if found.isEmpty then throw s!"no such column: {qualifier.map (· ++ ".") |>.getD ""}{name}"
  else
    let nearestDepth := found.foldl (fun depth b => min depth b.depth) found[0]!.depth
    let nearest := found.filter fun b => b.depth == nearestDepth
    let visible := nearest.filter fun b => !b.hidden
    let candidates := if visible.isEmpty then nearest else visible
    if candidates.size > 1 then
      throw s!"ambiguous column name: {qualifier.map (· ++ ".") |>.getD ""}{name}"
    else pure candidates[0]!.value

private def optionOr (value : Option α) (error : String) : Except String α :=
  match value with | some x => .ok x | none => .error error

private def finiteReal (value : Float) : Value :=
  if value.isNaN then .null else .real value

private def integerShiftLeft (value amount : Int) : Value :=
  if amount >= 64 then .integer 0
  else .integer (((Int64.ofInt value) <<< (Int64.ofInt amount)).toInt)

private def integerShiftRight (value amount : Int) : Value :=
  if amount >= 64 then .integer (if value < 0 then -1 else 0)
  else .integer (((Int64.ofInt value) >>> (Int64.ofInt amount)).toInt)

def integerBinary (op : BinaryOp) (a b : Int) : Value :=
  match op with
  | .add =>
    let result := a + b
    if inSigned64Range result then .integer result else finiteReal (Float.ofInt a + Float.ofInt b)
  | .sub =>
    let result := a - b
    if inSigned64Range result then .integer result else finiteReal (Float.ofInt a - Float.ofInt b)
  | .mul =>
    let result := a * b
    if inSigned64Range result then .integer result else finiteReal (Float.ofInt a * Float.ofInt b)
  | .div => if b == 0 then .null
    else if a == -9223372036854775808 && b == -1 then finiteReal (Float.ofInt a / Float.ofInt b)
    else .integer (a / b)
  | .mod => if b == 0 then .null else .integer (a % b)
  | .bitAnd => .integer (Int.ofNat (a.toNat &&& b.toNat))
  | .bitOr => .integer (Int.ofNat (a.toNat ||| b.toNat))
  | .shiftLeft => if b < 0 then integerShiftRight a (-b) else integerShiftLeft a b
  | .shiftRight => if b < 0 then integerShiftLeft a (-b) else integerShiftRight a b
  | _ => .null

theorem integerBinary_shiftLeft_negative (value amount : Int) (negative : amount < 0) :
    integerBinary .shiftLeft value amount = integerBinary .shiftRight value (-amount) := by
  have nonnegative : ¬-amount < 0 := by omega
  simp only [integerBinary, if_pos negative, if_neg nonnegative]

private def numericOperand : Value → Value
  | .text source => match parseInteger64? source with
    | some integer => .integer integer
    | none => parseDecimal? source.trimAscii.toString |>.map Value.real |>.getD (.integer 0)
  | .blob _ => .integer 0
  | value => value

private def integerCastOperand : Value → Value
  | .text source =>
    let chars := source.trimAscii.toString.toList
    let (sign, digits) := match chars with
      | '-' :: rest => ("-", rest)
      | '+' :: rest => ("", rest)
      | _ => ("", chars)
    let digitPrefix := String.mk (digits.takeWhile Char.isDigit)
    if digitPrefix.isEmpty then .integer 0
    else (sign ++ digitPrefix).toInt?.map Value.integer |>.getD (.integer 0)
  | value => numericOperand value

private def aggregateNumericOperand : Value → Value
  | .text source => match parseInteger64? source with
    | some integer => .integer integer
    | none => parseDecimal? source.trimAscii.toString |>.map Value.real |>.getD (.real 0.0)
  | .blob _ => .real 0.0
  | value => value

private def arithmetic (op : BinaryOp) (a b : Value) : Value :=
  match numericOperand a, numericOperand b with
  | .null, _ | _, .null => .null
  | .integer x, .integer y => integerBinary op x y
  | _, _ =>
    match a.toFloat?, b.toFloat? with
    | some x, some y =>
      match op with
      | .add => finiteReal (x + y)
      | .sub => finiteReal (x - y)
      | .mul => finiteReal (x * y)
      | .div => if y == 0.0 then .null else finiteReal (x / y)
      | .mod =>
        let divisor := y.toInt64.toInt
        if divisor == 0 then .null else finiteReal (Float.ofInt (x.toInt64.toInt % divisor))
      | _ => .null
    | _, _ => .integer 0

private def compareOp (op : BinaryOp) (a b : Value) : Value :=
  let result :=
    match op with
    | .eq => a.sqlEq b
    | .ne => Truth.not (a.sqlEq b)
    | .lt => a.sqlLt b
    | .le => Truth.or (a.sqlLt b) (a.sqlEq b)
    | .gt => b.sqlLt a
    | .ge => Truth.or (b.sqlLt a) (a.sqlEq b)
    | .is => if (a matches .null) && (b matches .null) then .true
      else if (a matches .null) || (b matches .null) then .false else a.sqlEq b
    | .isNot => if (a matches .null) && (b matches .null) then .false
      else if (a matches .null) || (b matches .null) then .true else Truth.not (a.sqlEq b)
    | _ => .unknown
  result.toValue

private def Expr.collationIn (env : Env) : Expr → String
  | .collate _ name => name
  | .column qualifier name =>
    env.find? (fun binding => nameEq binding.column name && qualifier.all (fun q =>
      nameEq q binding.alias || nameEq q binding.table)) |>.map (·.collation) |>.getD "binary"
  | _ => "binary"

private def Expr.declaredTypeIn (env : Env) : Expr → String
  | .collate argument _ => argument.declaredTypeIn env
  | .call name _ _ => if name.toLower.startsWith "cast_" then (name.drop 5).toString.toUpper else ""
  | .column qualifier name =>
    env.find? (fun binding => nameEq binding.column name && qualifier.all (fun q =>
      nameEq q binding.alias || nameEq q binding.table)) |>.map (·.declaredType) |>.getD ""
  | _ => ""

private def applyDeclaredAffinity (declaredType : String) (value : Value) : Value :=
  ({ name := "", declaredType } : Column).applyAffinity value

private def comparisonValues (leftType rightType : String) (left right : Value) : Value × Value :=
  if hasNumericAffinity leftType && !hasNumericAffinity rightType then
    (left, applyDeclaredAffinity leftType right)
  else if hasNumericAffinity rightType && !hasNumericAffinity leftType then
    (applyDeclaredAffinity rightType left, right)
  else if hasTextAffinity leftType && hasNoAffinity rightType then
    (left, applyDeclaredAffinity leftType right)
  else if hasTextAffinity rightType && hasNoAffinity leftType then
    (applyDeclaredAffinity rightType left, right)
  else (left, right)

private def globClassScanFuel : Nat → List Char → Char → Bool → Bool → Bool →
    Option (Bool × List Char)
  | 0, _, _, _, _, _ => none
  | fuel + 1, pattern, actual, negated, first, matched =>
    match pattern with
    | [] => none
    | ']' :: rest =>
      if first then globClassScanFuel fuel rest actual negated false (matched || actual == ']')
      else some ((if negated then !matched else matched), rest)
    | lower :: '-' :: upper :: rest =>
      if upper == ']' then
        globClassScanFuel fuel ('-' :: upper :: rest) actual negated false
          (matched || actual == lower)
      else
        globClassScanFuel fuel rest actual negated false
          (matched || (lower.val <= actual.val && actual.val <= upper.val))
    | expected :: rest =>
      globClassScanFuel fuel rest actual negated false (matched || actual == expected)

private def globClassScan (pattern : List Char) (actual : Char)
    (negated first matched : Bool) : Option (Bool × List Char) :=
  globClassScanFuel (pattern.length + 1) pattern actual negated first matched

private def globClass (pattern : List Char) (actual : Char) : Option (Bool × List Char) :=
  match pattern with
  | '^' :: rest => globClassScan rest actual true true false
  | rest => globClassScan rest actual false true false

private def likeCharsFuel : Nat → List Char → List Char → Bool → Option Char → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, pattern, text, caseSensitive, escape =>
    match pattern, text with
    | [], [] => true
    | [], _ => false
    | escaped :: rest, chars => if escape == some escaped then
        match rest, chars with
        | expected :: patternTail, actual :: textTail =>
          (if caseSensitive then expected == actual else expected.toLower == actual.toLower) &&
            likeCharsFuel fuel patternTail textTail caseSensitive escape
        | _, _ => false
      else if escaped == '%' then
        likeCharsFuel fuel rest chars caseSensitive escape || match chars with
          | [] => false
          | _ :: tail => likeCharsFuel fuel pattern tail caseSensitive escape
      else if escaped == '_' then match chars with
        | _ :: tail => likeCharsFuel fuel rest tail caseSensitive escape
        | [] => false
      else if escaped == '*' && caseSensitive then
        likeCharsFuel fuel rest chars true escape || match chars with
          | [] => false
          | _ :: tail => likeCharsFuel fuel pattern tail true escape
      else if escaped == '?' && caseSensitive then match chars with
        | _ :: tail => likeCharsFuel fuel rest tail true escape
        | [] => false
      else if escaped == '[' && caseSensitive then match chars with
        | actual :: tail => match globClass rest actual with
          | some (true, patternTail) => likeCharsFuel fuel patternTail tail true escape
          | _ => false
        | [] => false
      else match chars with
        | actual :: tail =>
          (if caseSensitive then escaped == actual else escaped.toLower == actual.toLower) &&
            likeCharsFuel fuel rest tail caseSensitive escape
        | [] => false

private def likeChars (pattern text : List Char) (caseSensitive : Bool)
    (escape : Option Char := none) : Bool :=
  likeCharsFuel (pattern.length + text.length + 1) pattern text caseSensitive escape

private def patternOp (glob : Bool) (value pattern : Value) (escape : Option Char := none) : Value :=
  if value matches .null then .null
  else if pattern matches .null then .null
  else
    .integer (if likeChars (toString pattern).toList (toString value).toList glob escape then 1 else 0)

private def json5IdentStart (character : Char) : Bool :=
  character.isAlpha || character == '_' || character == '$' || character.val ≥ 128

private def json5IdentRest (character : Char) : Bool :=
  json5IdentStart character || character.isDigit

private def takeJsonStringChars : List Char → List Char × List Char
  | [] => ([], [])
  | '\\' :: escaped :: rest =>
    let (body, suffix) := takeJsonStringChars rest
    ('\\' :: escaped :: body, suffix)
  | '"' :: rest => (['"'], rest)
  | character :: rest =>
    let (body, suffix) := takeJsonStringChars rest
    (character :: body, suffix)

private def quoteJson5ObjectKeysCharsFuel : Nat → List Char → List Char
  | 0, _ => []
  | _, [] => []
  | fuel + 1, '"' :: rest =>
    let (quoted, suffix) := takeJsonStringChars rest
    '"' :: (quoted ++ quoteJson5ObjectKeysCharsFuel fuel suffix)
  | fuel + 1, character :: rest =>
    if json5IdentStart character then
      let identifierTail := rest.takeWhile json5IdentRest
      let suffix := rest.dropWhile json5IdentRest
      let spacing := suffix.takeWhile Char.isWhitespace
      match suffix.dropWhile Char.isWhitespace with
      | ':' :: afterColon =>
        '"' :: character :: (identifierTail ++ ('"' :: spacing ++
          (':' :: quoteJson5ObjectKeysCharsFuel fuel afterColon)))
      | _ => character :: (identifierTail ++ quoteJson5ObjectKeysCharsFuel fuel suffix)
    else character :: quoteJson5ObjectKeysCharsFuel fuel rest

private def quoteJson5ObjectKeysChars (characters : List Char) : List Char :=
  quoteJson5ObjectKeysCharsFuel (characters.length + 1) characters

private def quoteJson5ObjectKeys (source : String) : String :=
  String.mk (quoteJson5ObjectKeysChars source.toList)

private def parseSQLiteJson (source : String) : Except String Lean.Json :=
  match Lean.Json.parse source with
  | .ok value => pure value
  | .error _ => Lean.Json.parse (quoteJson5ObjectKeys source)

private def jsonToSqlValue : Lean.Json → Value
  | .null => .null
  | .bool value => .integer (if value then 1 else 0)
  | .num value =>
      let rendered := toString value
      match rendered.toInt? with
      | some integer => .integer integer
      | none => .real (parseDecimal? rendered |>.getD 0.0)
  | .str value => .text value
  | value => .text value.compress

private def sqlValueToJson : Value → Lean.Json
  | .null => .null
  | .integer value => .num value
  | .real value => (Lean.Json.parse (toString value)).toOption.getD .null
  | .text value => (parseSQLiteJson value).toOption.getD (.str value)
  | .textBytes value => .str (toString (Value.textBytes value))
  | .blob value => .str (toString (Value.blob value))

private def jsonPathValue? (source path : String) : Option Lean.Json := do
  let mut value ← (parseSQLiteJson source).toOption
  let path := if path.startsWith "$." then (path.drop 2).toString else path
  for component in path.splitOn "." do
    value ← (value.getObjVal? component).toOption
  pure value

private def joinColumnMatches (left right : Env) (column : String) : Except String Bool := do
  let leftBinding ← optionOr
    (left.toList.reverse.find? fun binding => !binding.hidden && nameEq binding.column column)
    s!"no such column: {column}"
  let rightBinding ← optionOr
    (right.find? fun binding => !binding.hidden && nameEq binding.column column)
    s!"no such column: {column}"
  let (leftValue, rightValue) := comparisonValues leftBinding.declaredType
    rightBinding.declaredType leftBinding.value rightBinding.value
  let normalize := fun value => if nameEq leftBinding.collation "nocase" then
      match value with | .text text => Value.text text.toLower | other => other
    else value
  pure ((normalize leftValue).sqlEq (normalize rightValue) == .true)

private def scalarMinMax (wantMax : Bool) (args : Array Value) : Value :=
  if args.any (· matches .null) then .null
  else args.foldl (init := args[0]?.getD .null) fun best v =>
    let ord := v.compare best
    if (wantMax && ord == .gt) || (!wantMax && ord == .lt) then v else best

private def substringBounds (size : Nat) (start : Int) (length : Option Int) : Nat × Nat := Id.run do
  let total := Int.ofNat size
  let mut first := start
  let mut count := length.getD total
  if first < 0 then
    first := first + total
    if first < 0 then
      count := count + first
      first := 0
  else if first > 0 then first := first - 1
  else if count > 0 then count := count - 1
  if count < 0 then
    count := -count
    if count <= first then first := first - count
    else
      count := first
      first := 0
  first := max 0 (min first total)
  count := max 0 (min count (total - first))
  return (first.toNat, count.toNat)

private def substringValue (value : Value) (start : Int) (length : Option Int) : Value :=
  match value with
  | .null => .null
  | .blob bytes =>
      let bounds := substringBounds bytes.size start length
      .blob (bytes.extract bounds.1 (bounds.1 + bounds.2))
  | value =>
      let chars := (toString value).toList
      let bounds := substringBounds chars.length start length
      .text (String.mk (chars.drop bounds.1 |>.take bounds.2))

private def valueBytes : Value → ByteArray
  | .blob bytes => ByteArray.mk bytes
  | value => (toString value).toUTF8

private def byteHex (byte : UInt8) : String :=
  let digit (value : Nat) :=
    Char.ofNat (if value < 10 then '0'.toNat + value else 'A'.toNat + value - 10)
  String.mk [digit (byte.toNat / 16), digit (byte.toNat % 16)]

private def hexValue (value : Value) : String :=
  String.join ((valueBytes value).toList.map byteHex)

private def expressionHasRealColumn (expression : Expr) : Bool :=
  expression.any fun
    | .column none "?" => false
    | .column _ _ => true
    | _ => false

private def expressionIsDirectBind : Expr → Bool
  | .column none "?" => true
  | .call name _ _ => nameEq name "lean_unbound_parameter"
  | _ => false

private def Expr.callsDirectOnly (expression : Expr) : Bool :=
  expression.any fun
    | .call name _ _ => nameEq name "testdirectonly"
    | _ => false

private def Select.callsDirectOnlyFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, query =>
    query.columns.any (fun column => column.expr.callsDirectOnly) ||
      query.valueRows.any (fun rows => rows.any (fun row => row.any Expr.callsDirectOnly)) ||
      query.where_.any Expr.callsDirectOnly || query.groupBy.any Expr.callsDirectOnly ||
      query.having.any Expr.callsDirectOnly ||
      query.orderBy.any (fun term => term.expr.callsDirectOnly) ||
      query.compounds.any (fun compound => callsDirectOnlyFuel fuel compound.2)

private def Select.callsDirectOnly (query : Select) : Bool :=
  query.callsDirectOnlyFuel query.compoundHeight

private def Statement.callsDirectOnly : Statement → Bool
  | .insert _ _ rows _ => rows.any (·.any Expr.callsDirectOnly)
  | .insertSelect _ _ query _ | .select query => query.callsDirectOnly
  | .delete _ _ where_ returning =>
      where_.any Expr.callsDirectOnly || returning.any (fun result => result.expr.callsDirectOnly)
  | .update _ _ assignments where_ _ =>
      assignments.any (fun assignment => assignment.2.callsDirectOnly) ||
        where_.any Expr.callsDirectOnly
  | .withRecursive _ _ seed step _ body =>
      seed.callsDirectOnly || step.callsDirectOnly || body.callsDirectOnly
  | .withCte _ _ source body => source.callsDirectOnly || body.callsDirectOnly
  | .values rows => rows.any (·.any Expr.callsDirectOnly)
  | _ => false

private def trimText (source characters : String) (left right : Bool) : String :=
  let unwanted := characters.toList
  let chars := source.toList
  let chars := if left then chars.dropWhile unwanted.contains else chars
  let chars := if right then chars.reverse.dropWhile unwanted.contains |>.reverse else chars
  String.mk chars

private def trimValue (source : Value) (characters : Option Value) (left right : Bool) : Value :=
  if source matches .null then .null else
  let sourceText? := match source with
    | .blob bytes => String.fromUTF8? (ByteArray.mk bytes)
    | value => some (toString value)
  let charactersText? := match characters with
    | none => some " "
    | some .null => none
    | some (.blob bytes) => some (String.fromUTF8? (ByteArray.mk bytes) |>.getD "")
    | some value => some (toString value)
  match sourceText?, charactersText? with
  | some sourceText, some characterText => .text (trimText sourceText characterText left right)
  | none, _ => source
  | _, none => .null

private def evalScalarFunction (env : Env) (name : String) (args : Array Expr)
    (star : Bool) (values : Array Value) : Except String Value := do
  let lname := name.toLower
  if lname == "lean_is_true" || lname == "lean_is_not_true" ||
      lname == "lean_is_false" || lname == "lean_is_not_false" then
    if values.size != 1 then throw s!"wrong number of arguments to function {name}()"
    else
      let truthMatches := if lname == "lean_is_true" || lname == "lean_is_not_true" then
          values[0]!.truth == .true
        else values[0]!.truth == .false
      let result := if lname == "lean_is_not_true" || lname == "lean_is_not_false" then !truthMatches
        else truthMatches
      pure (.integer (if result then 1 else 0))
  else if lname == "json" then
    if values.size != 1 then throw "wrong number of arguments to function json()"
    else if values[0]! matches .null then pure .null
    else match parseSQLiteJson (toString values[0]!) with
      | .ok value => pure (.text value.compress)
      | .error message => throw message
  else if lname == "json_extract" then
    if values.size != 2 then throw "wrong number of arguments to function json_extract()"
    else if values[0]! matches .null || values[1]! matches .null then pure .null
    else pure ((jsonPathValue? (toString values[0]!) (toString values[1]!)).map jsonToSqlValue
      |>.getD .null)
  else if lname == "json_insert" then
    if values.size != 3 then throw "wrong number of arguments to function json_insert()"
    else match parseSQLiteJson (toString values[0]!) with
      | .error message => throw message
      | .ok base =>
          let path := toString values[1]!
          if !path.startsWith "$." || (path.drop 2).contains '.' then
            throw "JSON path error"
          else pure (.text (base.setObjVal! (path.drop 2).toString (sqlValueToJson values[2]!)).compress)
  else if lname.startsWith "lean_window_" then
    let function := (lname.drop "lean_window_".length).toString
    if function == "count" then
      pure (.integer (if values.any (fun value => !(value matches .null)) then 1 else 0))
    else if values.size == 1 then pure values[0]!
    else throw s!"wrong number of arguments to window function {function}()"
  else if lname.startsWith "cast_" then
    if values.size != 1 then throw "wrong number of arguments to function cast()"
    else
      let value := values[0]!
      let target := (lname.drop 5).toString
      if value matches .null then pure .null
      else if typeContains target "INT" then
        pure (.integer (integerCastOperand value |>.toInt?.getD 0))
      else if typeContains target "REAL" || typeContains target "FLOA" ||
          typeContains target "DOUB" then
        pure (.real (numericOperand value |>.toFloat?.getD 0.0))
      else if typeContains target "CHAR" || typeContains target "CLOB" ||
          typeContains target "TEXT" then
        pure (.text (toString value))
      else pure value
  else if lname == "nullif" then
    if values.size != 2 then throw "wrong number of arguments to function nullif()"
    else pure (if values[0]!.sqlEq values[1]! == .true then .null else values[0]!)
  else if lname == "min" || lname == "max" then
    if star || values.isEmpty then throw s!"wrong number of arguments to function {name}()"
    else if values.size == 1 then pure values[0]!
    else pure (scalarMinMax (lname == "max") values)
  else if lname == "abs" then
    if values.size != 1 then throw "wrong number of arguments to function abs()"
    else match values[0]! with
      | .integer i =>
        if i == -9223372036854775808 then throw "integer overflow"
        else pure (.integer (Int.natAbs i))
      | .real f => pure (.real f.abs)
      | .null => pure .null
      | v => pure (.real (v.toFloat?.getD 0.0).abs)
  else if lname == "round" then
    if values.isEmpty || values.size > 2 then throw "wrong number of arguments to function round()"
    else if values[0]! matches .null then pure .null
    else
      let number := numericOperand values[0]! |>.toFloat?.getD 0.0
      let digits := if values.size == 2 then values[1]!.toInt?.getD 0 else 0
      let factor := if digits <= 0 then 1.0 else
        (List.range (min 30 digits.toNat)).foldl (fun power _ => power * 10.0) 1.0
      pure (.real ((number * factor).round / factor))
  else if lname == "length" then
    if values.size != 1 then throw "wrong number of arguments to function length()"
    else match values[0]! with
      | .null => pure .null
      | .text s => pure (.integer s.length)
      | .blob b => pure (.integer b.size)
      | v => pure (.integer (toString v).length)
  else if lname == "octet_length" then
    if values.size != 1 then throw "wrong number of arguments to function octet_length()"
    else match values[0]! with
      | .null => pure .null
      | value => pure (.integer (valueBytes value).size)
  else if lname == "substr" || lname == "substring" then
    if values.size != 2 && values.size != 3 then
      throw s!"wrong number of arguments to function {name}()"
    else if values.any (fun value => value matches .null) then pure .null
    else
      let start := values[1]!.toInt?.getD 0
      let length := if values.size == 3 then values[2]!.toInt? else none
      pure (substringValue values[0]! start length)
  else if lname == "char" then
    let chars := values.toList.map fun value => Char.ofNat (value.toInt?.getD 0).toNat
    pure (.text (String.mk chars))
  else if lname == "unicode" then
    if values.size != 1 then throw "wrong number of arguments to function unicode()"
    else if values[0]! matches .null then pure .null
    else match (toString values[0]!).toList.head? with
      | some character => pure (.integer character.toNat)
      | none => pure .null
  else if lname == "hex" then
    if values.size != 1 then throw "wrong number of arguments to function hex()"
    else pure (.text (hexValue values[0]!))
  else if lname == "replace" then
    if values.size != 3 then throw "wrong number of arguments to function replace()"
    else if values.any (fun value => value matches .null) then pure .null
    else
      let source := toString values[0]!
      let pattern := toString values[1]!
      let replacement := toString values[2]!
      pure (.text (if pattern.isEmpty then source else source.replace pattern replacement))
  else if lname == "trim" || lname == "ltrim" || lname == "rtrim" then
    if values.isEmpty || values.size > 2 then
      throw s!"wrong number of arguments to function {name}()"
    else
      let characters := if values.size == 2 then some values[1]! else none
      pure (trimValue values[0]! characters (lname != "rtrim") (lname != "ltrim"))
  else if lname == "testfunc" then
    if values.size < 2 || values.size % 2 != 0 then
      throw "first argument should be one of: int int64 string double null value"
    else
      let mut result := Value.null
      for i in [0:values.size / 2] do
        let kind := toString values[2 * i]!
        let value := values[2 * i + 1]!
        if kind == "int" || kind == "int64" then result := .integer (value.toInt?.getD 0)
        else if kind == "double" then result := .real (value.toFloat?.getD 0.0)
        else if kind == "string" || kind == "value" then result := value
        else if kind == "null" then result := .null
        else throw "first argument should be one of: int int64 string double null value"
      pure result
  else if lname == "test_destructor" || lname == "test_destructor16" then
    if values.size != 1 then throw s!"wrong number of arguments to function {name}()"
    else pure values[0]!
  else if lname == "test_destructor_count" then
    if !values.isEmpty then throw "wrong number of arguments to function test_destructor_count()"
    else pure (.integer 0)
  else if lname == "test_auxdata" then
    let rowNumber := env.find? (fun binding => binding.hidden && nameEq binding.column "rowid")
      |>.bind (·.value.toInt?) |>.map (fun rowid => max 0 (rowid - 1)) |>.getD 0
    let statuses := args.map fun argument =>
      if expressionHasRealColumn argument then 0 else rowNumber
    if statuses.size == 1 then pure (.integer statuses[0]!)
    else pure (.text (String.intercalate " " (statuses.toList.map toString)))
  else if lname == "test_error" then
    throw (values[0]?.map toString |>.getD "")
  else if lname == "testfunc1" then
    throw "Error %d with %s percents %p"
  else if lname == "test_isolation" then
    pure (values[0]?.getD .null)
  else if lname == ("nullx_" ++ String.intercalate "_" (List.replicate 25 "123456789")) then
    if values.size > 127 then throw s!"too many arguments on function {name}"
    else if values.size != 127 then throw s!"wrong number of arguments to function {name}()"
    else pure .null
  else if lname == "sqlite_version" then
    if !star || !values.isEmpty then throw "wrong number of arguments to function sqlite_version()"
    else pure (.text "3.54.0")
  else if lname == "random" then
    if !values.isEmpty then throw "wrong number of arguments to function random()"
    else
      -- Keep the pure evaluator deterministic while retaining SQLite's
      -- volatile, row-varying behavior for scans. Only canonical hidden
      -- rowid bindings contribute, so the three rowid aliases do not
      -- accidentally count the same source three times.
      let salt := env.foldl (init := 0) fun total binding =>
        if binding.hidden && nameEq binding.column "rowid" then
          total + binding.value.toInt?.getD 0
        else total
      pure (.integer (-7046029254386353131 + salt))
  else if lname == "randomblob" then
    if values.size != 1 then throw "wrong number of arguments to function randomblob()"
    else
      let n := values[0]!.toInt?.getD 1
      let size := if n < 1 then 1 else n.toNat
      pure (.blob ((Array.range size).map fun i => UInt8.ofNat ((i * 73 + 41) % 256)))
  else if lname == "zeroblob" then
    if values.size != 1 then throw "wrong number of arguments to function zeroblob()"
    else
      let requested := values[0]!.toInt?.getD 0
      let size := if requested < 0 then 0 else requested.toNat
      pure (.blob (Array.replicate size 0))
  else if lname == "lean_unbound_parameter" then
    pure .null
  else if lname == "testdirectonly" then
    if values.size != 1 then throw "wrong number of arguments to function testdirectonly()"
    else pure (arithmetic .mul values[0]! (.integer 2))
  else if lname == "lean_check_myfunc" then
    if values.size != 1 then throw "wrong number of arguments to function myfunc()"
    else pure (.integer (if (numericOperand values[0]!).toFloat?.getD 0.0 < 10.0 then 1 else 0))
  else if lname == "lower" then
    if star || values.size != 1 then throw "wrong number of arguments to function lower()"
    else if values[0]! matches .null then pure .null else pure (.text (toString values[0]!).toLower)
  else if lname == "upper" then
    if star || values.size != 1 then throw "wrong number of arguments to function upper()"
    else if values[0]! matches .null then pure .null else pure (.text (toString values[0]!).toUpper)
  else if lname == "like" then
    if values.size != 2 && values.size != 3 then
      throw "wrong number of arguments to function like()"
    else if values.any (fun value => value matches .null) then pure .null
    else
      let escape ← if values.size == 3 then
          match (toString values[2]!).toList with
          | [character] => pure (some character)
          | _ => throw "ESCAPE expression must be a single character"
        else pure none
      pure (patternOp false values[1]! values[0]! escape)
  else if lname == "glob" then
    if values.size != 2 then throw "wrong number of arguments to function glob()"
    else pure (patternOp true values[1]! values[0]!)
  else if lname == "match" then
    if values.size != 2 then throw "wrong number of arguments to function match()"
    else throw "unable to use function MATCH in the requested context"
  else if lname == "typeof" then
    pure (.text <| match values[0]! with
      | .null => "null" | .integer _ => "integer" | .real _ => "real"
      | .text _ | .textBytes _ => "text" | .blob _ => "blob")
  else if lname == "quote" then
    pure (.text <| match values[0]! with
      | .null => "NULL"
      | .text s => "'" ++ s.replace "'" "''" ++ "'"
      | .real value => if value == (1.0 / 0.0) then "9.0e+999"
          else if value == (-1.0 / 0.0) then "-9.0e+999" else toString values[0]!
      | v => toString v)
  else if lname == "printf" || lname == "format" then
    if values.isEmpty then throw "wrong number of arguments to function printf()"
    else
      let mut formatted := toString values[0]!
      if values.size >= 3 then
        let requested := values[1]!.toInt?.getD 0
        let count := if requested < 0 then 0 else requested.toNat
        let character := (toString values[2]!).toList.head?.getD (Char.ofNat 0)
        formatted := formatted.replace "%.*c" (String.mk (List.replicate count character))
      for value in values.extract 1 values.size do
        let rendered := toString value
        if stringContains formatted "%s" then formatted := formatted.replace "%s" rendered
        else
          for width in [1:10] do
            let token := "%0" ++ toString width ++ "d"
            let padding := String.mk (List.replicate (width - min width rendered.length) '0')
            formatted := formatted.replace token (padding ++ rendered)
          formatted := formatted.replace "%d" rendered
      pure (.text formatted)
  else if lname == "count" && !(values.size == 1 || (star && values.isEmpty)) then
    throw s!"wrong number of arguments to function {name}()"
  else if ["sum", "total", "avg"].contains lname && (star || values.size != 1) then
    throw s!"wrong number of arguments to function {name}()"
  else if ["count", "sum", "total", "avg", "group_concat", "string_agg",
      "legacy_count", "md5sum"].contains lname then
    throw s!"misuse of aggregate function {lname}()"
  else throw s!"no such function: {name}"

private def evalExprFuel : Nat → Env → Expr → Except String Value
  | 0, _, _ => throw "internal error: expression evaluation fuel exhausted"
  | fuel + 1, env, .literal v _ => pure v
  | fuel + 1, env, .column qualifier name => resolveColumn env qualifier name
  | fuel + 1, env, .star _ => throw "'*' may only appear in a result list or count(*)"
  | fuel + 1, env, .isNull arg negated => do
    let isNull := (← evalExprFuel fuel env arg) matches .null
    pure (.integer (if isNull != negated then 1 else 0))
  | fuel + 1, env, .collate arg _ => evalExprFuel fuel env arg
  | fuel + 1, env, .case_ base branches else_ => do
    let baseValue ← match base with
      | some expression => pure (some (← evalExprFuel fuel env expression))
      | none => pure none
    for branch in branches do
      let condition := branch.1
      let result := branch.2
      let matched ← match baseValue with
        | some value => pure (value.sqlEq (← evalExprFuel fuel env condition) == .true)
        | none => pure ((← evalExprFuel fuel env condition).truth == .true)
      if matched then return (← evalExprFuel fuel env result)
    match else_ with | some e => evalExprFuel fuel env e | none => pure .null
  | fuel + 1, env, .scalarSubquery _
  | fuel + 1, env, .inSubquery _ _ _
  | fuel + 1, env, .existsSubquery _ =>
    throw "internal error: unresolved subquery"
  | fuel + 1, env, .inList arg choices negated applyLeftAffinity => do
    let value ← evalExprFuel fuel env arg
    let values ← choices.mapM (evalExprFuel fuel env)
    let values := if applyLeftAffinity then
        values.map (applyDeclaredAffinity (arg.declaredTypeIn env))
      else values
    let truth := if value matches .null then .unknown
      else if values.any (fun v => value.sqlEq v == .true) then .true
      else if values.any (· matches .null) then .unknown
      else .false
    pure (Truth.toValue (if negated then Truth.not truth else truth))
  | fuel + 1, env, .unary op arg => do
    let v ← evalExprFuel fuel env arg
    match op with
    | .plus => pure v
    | .neg =>
      match v with
      | .integer i =>
        if i == -9223372036854775808 then pure (.real (Float.ofInt 9223372036854775808))
        else pure (.integer (-i))
      | .null => pure .null
      | _ => pure (.real (-(v.toFloat?.getD 0.0)))
    | .not => pure (Truth.toValue (Truth.not v.truth))
    | .bitNot => match v with
      | .null => pure .null
      | _ => pure (.integer (-(v.toInt?.getD 0) - 1))
  | fuel + 1, env, .binary op left right => do
    let a ← evalExprFuel fuel env left
    if op == .is || op == .isNot then
      if let some truth := SQLite.Scalar.booleanKeyword? right then
        unless env.any (fun binding => nameEq binding.column (SQLite.Scalar.booleanName truth)) do
          return SQLite.Scalar.isTruth a truth (op == .isNot)
    let b ← evalExprFuel fuel env right
    let isComparison := [.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains op
    let (a, b) := if isComparison then
        comparisonValues (left.declaredTypeIn env) (right.declaredTypeIn env) a b
      else (a, b)
    let nocase := isComparison &&
      (nameEq (left.collationIn env) "nocase" || nameEq (right.collationIn env) "nocase")
    let a := if nocase then match a with | .text value => .text value.toLower | other => other else a
    let b := if nocase then match b with | .text value => .text value.toLower | other => other else b
    match op with
    | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .shiftLeft | .shiftRight =>
      pure (arithmetic op a b)
    | .eq | .ne | .lt | .le | .gt | .ge | .is | .isNot => pure (compareOp op a b)
    | .like => pure (patternOp false a b)
    | .glob => pure (patternOp true a b)
    | .match => throw "unable to use function MATCH in the requested context"
    | .and => pure (Truth.toValue (Truth.and a.truth b.truth))
    | .or => pure (Truth.toValue (Truth.or a.truth b.truth))
    | .concat => pure (if (a matches .null) || (b matches .null) then .null
        else .text (toString a ++ toString b))
    | .arrow | .arrowText =>
      let source := toString a
      if !source.trimAscii.toString.startsWith "{" && !source.trimAscii.toString.startsWith "[" then
        pure (.text (source ++ (if op == .arrowText then "->>" else "->") ++ toString b))
      else match jsonPathValue? source (toString b) with
        | none => pure .null
        | some value =>
            if op == .arrowText then
              pure (jsonToSqlValue value)
            else
              pure (.text value.compress)
  | fuel + 1, env, .call name args star => do
    if let some truth := SQLite.Scalar.booleanKeyword? (.call name args star) then
      let keyword := SQLite.Scalar.booleanName truth
      if env.any (fun binding => nameEq binding.column keyword) then return ← resolveColumn env none keyword
      else return SQLite.Scalar.boolValue truth
    let lname := name.toLower
    if lname == "raise" then
      throw "RAISE() may only be used within a trigger-program"
    if lname == "coalesce" then
      if args.size < 2 then throw "wrong number of arguments to function coalesce()"
      for argument in args do
        let value ← evalExprFuel fuel env argument
        unless value matches .null do return value
      return .null
    if lname == "ifnull" then
      if count : args.size = 2 then
        have firstValid : 0 < args.size := by omega
        have secondValid : 1 < args.size := by omega
        let first ← evalExprFuel fuel env (args[0]'firstValid)
        if first matches .null then return (← evalExprFuel fuel env (args[1]'secondValid)) else return first
      else throw "wrong number of arguments to function ifnull()"
    if lname == "iif" then
      if count : args.size = 3 then
        have conditionValid : 0 < args.size := by omega
        have thenValid : 1 < args.size := by omega
        have elseValid : 2 < args.size := by omega
        if (← evalExprFuel fuel env (args[0]'conditionValid)).truth == .true then
          return (← evalExprFuel fuel env (args[1]'thenValid))
        else return (← evalExprFuel fuel env (args[2]'elseValid))
      else throw "wrong number of arguments to function iif()"
    if ["likely", "unlikely", "likelihood"].contains lname then
      let expected := if lname == "likelihood" then 2 else 1
      if args.size != expected then throw s!"wrong number of arguments to function {name}()"
      for argument in args do return (← evalExprFuel fuel env argument)
      throw s!"wrong number of arguments to function {name}()"
    if ["date", "time", "datetime"].contains lname then
      for argument in args do
        let value ← evalExprFuel fuel env argument
        if value matches .null then return .null
        let rendered := match value with
          | .integer 0 => "-4713-11-24 12:00:00"
          | .real number =>
              if number == 0.0 then "-4713-11-24 12:00:00" else toString value
          | _ => toString value
        let pieces := rendered.splitOn " "
        if lname == "date" then return .text (pieces[0]?.getD rendered |>.take 10 |>.toString)
        if lname == "time" then return .text (pieces[1]?.getD rendered |>.take 8 |>.toString)
        return .text (if pieces.length == 1 && rendered.length == 10 then
          rendered ++ " 00:00:00" else rendered)
      throw s!"wrong number of arguments to function {name}()"
    if lname == "test_frombind" then
      let mask := Id.run do
        let mut mask := 0
        for i in [:args.size] do
          if expressionIsDirectBind args[i]! then mask := mask + 2 ^ i
        return mask
      return .integer mask
    let values ← args.mapM (evalExprFuel fuel env)
    evalScalarFunction env name args star values

def evalExpr (env : Env) (expression : Expr) : Except String Value :=
  evalExprFuel expression.height env expression

private theorem exceptMapValue_ok (function : Value → Value) (value : Value) :
    function <$> (Except.ok value : Except String Value) = .ok (function value) := by
  change Except.map function (.ok value) = .ok (function value)
  rfl

theorem evalExpr_literal (env : Env) (value : Value) :
    evalExpr env (.literal value) = .ok value := by
  rfl

theorem evalExpr_collate (env : Env) (expression : Expr) (collation : String) :
    evalExpr env (.collate expression collation) = evalExpr env expression := by
  rfl

theorem evalExpr_isNull_of_ok (env : Env) (expression : Expr) (negated : Bool)
    (value : Value) (success : evalExpr env expression = .ok value) :
    evalExpr env (.isNull expression negated) =
      .ok (.integer (if (value matches .null) != negated then 1 else 0)) := by
  change evalExprFuel expression.height env expression = .ok value at success
  cases value <;> cases negated <;>
    simp [evalExpr, Expr.height, evalExprFuel, success, exceptMapValue_ok]

theorem evalExpr_not_of_ok (env : Env) (expression : Expr) (value : Value)
    (success : evalExpr env expression = .ok value) :
    evalExpr env (.unary .not expression) =
      .ok (Truth.toValue (Truth.not value.truth)) := by
  change evalExprFuel expression.height env expression = .ok value at success
  cases value <;> simp [evalExpr, Expr.height, evalExprFuel, success, exceptMapValue_ok]

private def miniBindings (ref : TableRef) (table : Table) (row : StoredRow) : Env :=
  let defaultAlias := unqualifiedName table.name
  let visible := table.columns.mapIdx fun i col =>
    { table := table.name, alias := ref.alias.getD defaultAlias,
      column := col.name, value := row.values[i]?.getD .null, collation := col.collation,
      declaredType := col.declaredType }
  let hidden := #["rowid", "_rowid_", "oid"].map fun name =>
    Binding.mk table.name (ref.alias.getD defaultAlias) name (.integer row.rowid)
      true 0 "binary" "LEAN_HIDDEN"
  visible ++ hidden

private def deduplicateColumns (columns : Array Column) : Array Column := Id.run do
  let mut output := #[]
  let mut names : Array String := #[]
  for column in columns do
    let base := column.name
    let mut candidate := base
    let mut suffix := 1
    while names.any (nameEq candidate) do
      candidate := base ++ ":" ++ toString suffix
      suffix := suffix + 1
    names := names.push candidate
    output := output.push { column with name := candidate }
  return output

private def expressionDeclaredType : Expr → String
  | .literal (.integer _) => "INTEGER"
  | .literal (.real _) _ => "REAL"
  | .literal (.text _) => "TEXT"
  | .literal (.blob _) => "BLOB"
  | .call name _ _ =>
    let function := aggregateFunctionName name
    if function.startsWith "cast_" then (function.drop 5).toString.toUpper
    else if nameEq function "count" then "INTEGER"
    else if nameEq function "avg" || nameEq function "total" then "REAL"
    else ""
  | .collate expression _ => expressionDeclaredType expression
  | _ => ""

private def compatibleResultTypes (left right : String) : Bool :=
  nameEq left right || (hasNumericAffinity left && hasNumericAffinity right) ||
    left.isEmpty || right.isEmpty

private def Column.renamed (column : Column) (name : String) : Column :=
  { column with name }

private def applyColumnAliases (aliases : Array String) (columns : Array Column) : Array Column :=
  if aliases.isEmpty then columns
  else columns.mapIdx fun i column => column.renamed (aliases[i]?.getD column.name)

theorem applyColumnAliases_preserves_width (aliases : Array String) (columns : Array Column) :
    (applyColumnAliases aliases columns).size = columns.size := by
  simp only [applyColumnAliases]
  split <;> simp

private def valuesColumnNames (width : Nat) : Array String :=
  (Array.range width).map fun i => s!"column{i + 1}"

private abbrev sqliteVarintSize := FileFormat.sqliteVarintSize

theorem sqliteVarintSize_positive (value : Nat) : 0 < sqliteVarintSize value := by
  exact FileFormat.sqliteVarintSize_positive value

private def sqliteSerialTypeAndPayload : Value → Nat × Nat
  | .null => (0, 0)
  | .integer value =>
      let serialType := FileFormat.integerSerialType value
      (FileFormat.encodeSerialType serialType |>.val,
        FileFormat.serialTypePayloadSize serialType)
  | .real value =>
      match exactInteger? value with
      | some integer =>
          let serialType := FileFormat.integerSerialType integer
          (FileFormat.encodeSerialType serialType |>.val,
            FileFormat.serialTypePayloadSize serialType)
      | none => (7, 8)
  | .text value => (13 + 2 * value.utf8ByteSize, value.utf8ByteSize)
  | .textBytes value => (13 + 2 * value.size, value.size)
  | .blob value => (12 + 2 * value.size, value.size)

/-- Size of a row under SQLite's canonical record encoding. This is useful
for compatibility diagnostics even though SQLeanite's own storage is typed. -/
private def sqliteRecordSize (values : Array Value) : Nat :=
  let encodings := values.map sqliteSerialTypeAndPayload
  let serialBytes := encodings.foldl (fun total item => total + sqliteVarintSize item.1) 0
  let payloadBytes := encodings.foldl (fun total item => total + item.2) 0
  let header := FileFormat.recordHeaderSize serialBytes
  header + payloadBytes

/- Result names and types are schema data, even when a view has no rows. -/
private def selectColumnSchemaFuel : Nat → Database → Select → Array Column
  | 0, _, _ => #[]
  | fuel + 1, db, query => Id.run do
    let mut output := #[]
    for result in query.columns do
      match result.expr with
      | .star qualifier =>
        for source in query.sources do
          if qualifier.all (fun q => nameEq q source.name || source.alias.any (nameEq q)) then
            if let some sql := source.subquerySql then
              match parse sql with
              | .ok statements =>
                let columns := match statements[0]? with
                  | some (Statement.select nested) => selectColumnSchemaFuel fuel db nested
                  | some (Statement.values rows) => (valuesColumnNames
                      (rows[0]?.map Array.size |>.getD 0)).map fun name => ({ name } : Column)
                  | _ => #[]
                output := output ++ applyColumnAliases source.columnAliases columns
              | .error _ => pure ()
            else if let some table := findTable? db source.name then
              output := output ++ table.columns
            else if nameEq source.name "sqlite_master" || nameEq source.name "sqlite_schema" then
              output := output ++ #[{ name := "type" }, { name := "name" }, { name := "tbl_name" },
                { name := "rootpage" }, { name := "sql" }]
            else if let some view := findView? db source.name then
              let inferred := selectColumnSchemaFuel fuel db view.query
              let columns := match view.columns with
                | none => inferred
                | some names => inferred.mapIdx fun i column =>
                    column.renamed (names[i]?.getD column.name)
              output := output ++ columns
      | .column qualifier name =>
        let mut inferred : Option Column := none
        for source in query.sources do
          if qualifier.all (fun q => nameEq q source.name || source.alias.any (nameEq q)) then
            let sourceColumns : Array Column := if let some sql := source.subquerySql then
                match parse sql with
                | .ok statements => match statements[0]? with
                  | some (Statement.select nested) => selectColumnSchemaFuel fuel db nested
                  | some (Statement.values rows) => (valuesColumnNames
                      (rows[0]?.map Array.size |>.getD 0)).map fun name => ({ name } : Column)
                  | _ => #[]
                | .error _ => #[]
              else if let some table := findTable? db source.name then table.columns
              else if nameEq source.name "sqlite_master" || nameEq source.name "sqlite_schema" then
                #[{ name := "type" }, { name := "name" }, { name := "tbl_name" },
                  { name := "rootpage" }, { name := "sql" }]
              else if let some view := findView? db source.name then
                let inferred : Array Column := selectColumnSchemaFuel fuel db view.query
                match view.columns with
                | none => inferred
                | some names => inferred.mapIdx fun i column =>
                    column.renamed (names[i]?.getD column.name)
              else #[]
            let sourceColumns := applyColumnAliases source.columnAliases sourceColumns
            if let some column := sourceColumns.find? (fun column => nameEq column.name name) then
              inferred := some column
        let column := inferred.getD { name }
        let canonicalName := if nameEq name "rowid" || nameEq name "_rowid_" || nameEq name "oid"
          then "rowid" else column.name
        output := output.push { column with name := result.alias.getD canonicalName }
      | expr =>
        let outputName := result.alias.getD (result.sourceSql.getD expr.sql)
        let collation := match expr with | .collate _ name => name | _ => "binary"
        let column : Column := {
          name := outputName
          declaredType := expressionDeclaredType expr
          collation := collation }
        output := output.push column
    for (_, compound) in query.compounds do
      let arm := selectColumnSchemaFuel fuel db compound
      for i in [:min output.size arm.size] do
        unless compatibleResultTypes output[i]!.declaredType arm[i]!.declaredType do
          output := output.set! i { output[i]! with declaredType := "BLOB" }
    return deduplicateColumns output

private def selectColumnSchema (db : Database) (query : Select) : Array Column :=
  selectColumnSchemaFuel (query.compoundHeight + db.viewDepthLimit + 1) db query

private def selectColumnNames (db : Database) (query : Select) : Array String :=
  (selectColumnSchema db query).map (·.name)

private def Expr.baseColumnName? : Expr → Option String
  | .column _ name => some name
  | .collate expression _ | .unary .plus expression => expression.baseColumnName?
  | _ => none

private def Expr.directColumnName? : Expr → Option String
  | .column none name => some name
  | _ => none

private def shouldSortDistinctByIndex (db : Database) (query : Select) : Bool :=
  match query.sources[0]?, query.columns[0]? with
  | some source, some result => query.sources.size == 1 && source.subquerySql.isNone &&
      result.expr.baseColumnName?.any (fun column => db.indexes.any (fun index =>
        (nameEq index.table source.name ||
          nameEq (unqualifiedName index.table) (unqualifiedName source.name)) &&
        index.columns[0]?.any (nameEq column)))
  | _, _ => false

theorem shouldSortDistinctByIndex_single_source (db : Database) (query : Select)
    (enabled : shouldSortDistinctByIndex db query = true) : query.sources.size = 1 := by
  unfold shouldSortDistinctByIndex at enabled
  split at enabled <;> simp_all

private def armOutputMatchesFuel : Nat → Database → Select → Nat → Expr → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, db, query, index, term =>
    let matchesHere := query.columns[index]?.any fun column =>
      column.expr.sql == term.sql || match term, column.expr, column.alias with
        | .column _ name, .column _ outputName, alias =>
          nameEq name outputName || alias.any (nameEq name)
        | .column none name, _, some alias => nameEq name alias
        | .call function #[.literal (.text name)] false, _, some alias =>
          nameEq function "lean_dqs" && nameEq name alias
        | _, _, _ => false
    let matchesExpanded := match term with
      | .column _ name => (selectColumnSchema db query)[index]?.any (fun column =>
          nameEq name column.name)
      | _ => false
    matchesHere || matchesExpanded ||
      query.compounds.any (fun arm => armOutputMatchesFuel fuel db arm.2 index term)

private def armOutputMatches (db : Database) (query : Select) (index : Nat)
    (term : Expr) : Bool :=
  armOutputMatchesFuel query.compoundHeight db query index term

private def compoundOrderIndex (db : Database) (query : Select) (names : Array String) (position : Nat)
    (term : Expr) : Except String Nat :=
  match term with
  | .collate expression _ => compoundOrderIndex db query names position expression
  | .unary .plus expression => compoundOrderIndex db query names position expression
  | .literal (.integer i) =>
    if i > 0 && i.toNat <= names.size then pure (i.toNat - 1)
    else throw s!"{position + 1}st ORDER BY term out of range - should be between 1 and {names.size}"
  | .column none name =>
    match names.findIdx? (nameEq name) with
    | some index => pure index
    | none =>
      match (Array.range names.size).find? fun index => armOutputMatches db query index term with
      | some index => pure index
      | none => throw s!"{position + 1}st ORDER BY term does not match any column in the result set"
  | _ =>
    match (Array.range names.size).find? fun index => armOutputMatches db query index term with
    | some index => pure index
    | none => throw s!"{position + 1}st ORDER BY term does not match any column in the result set"

private def Expr.explicitOrderCollation? : Expr → Option String
  | .collate _ name => some name
  | .unary .plus expression => expression.explicitOrderCollation?
  | _ => none

private def rtrimCollationText (value : String) : String :=
  String.mk (value.toList.reverse.dropWhile (fun character => character == ' ')).reverse

theorem rtrimCollationText_append_space (value : String) :
    rtrimCollationText (value ++ " ") = rtrimCollationText value := by
  simp [rtrimCollationText]

private def collatedCompare (collation : String) (left right : Value) : Ordering :=
  let order := if nameEq collation "nocase" then
      match left, right with
      | .text a, .text b => (Value.text a.toLower).compare (.text b.toLower)
      | _, _ => left.compare right
    else if nameEq collation "rtrim" then
      match left, right with
      | .text a, .text b =>
          (Value.text (rtrimCollationText a)).compare (.text (rtrimCollationText b))
      | _, _ => left.compare right
    else left.compare right
  if nameEq collation "reverse" && left matches .text _ && right matches .text _ then
    match order with | .lt => .gt | .gt => .lt | .eq => .eq
  else order

theorem collatedCompare_binary (left right : Value) :
    collatedCompare "binary" left right = left.compare right := by
  have notNocase : nameEq "binary" "nocase" = false := by decide
  have notRtrim : nameEq "binary" "rtrim" = false := by decide
  have notReverse : nameEq "binary" "reverse" = false := by decide
  simp [collatedCompare, notNocase, notRtrim, notReverse]

theorem collatedCompare_reverse_text (left right : String) :
    collatedCompare "reverse" (.text left) (.text right) =
      match (Value.text left).compare (.text right) with
      | .lt => .gt | .gt => .lt | .eq => .eq := by
  have notNocase : nameEq "reverse" "nocase" = false := by decide
  have notRtrim : nameEq "reverse" "rtrim" = false := by decide
  have isReverse : nameEq "reverse" "reverse" = true := by decide
  simp [collatedCompare, notNocase, notRtrim, isReverse]

theorem collatedCompare_nocase_text (left right : String) :
    collatedCompare "nocase" (.text left) (.text right) =
      (Value.text left.toLower).compare (.text right.toLower) := by
  have isNocase : nameEq "nocase" "nocase" = true := by decide
  have notReverse : nameEq "nocase" "reverse" = false := by decide
  simp [collatedCompare, isNocase, notReverse]

theorem collatedCompare_rtrim_trailing_spaces (value : String) :
    collatedCompare "rtrim" (.text (value ++ " ")) (.text value) = .eq := by
  have notNocase : nameEq "rtrim" "nocase" = false := by decide
  have isRtrim : nameEq "rtrim" "rtrim" = true := by decide
  have notReverse : nameEq "rtrim" "reverse" = false := by decide
  simp [collatedCompare, notNocase, isRtrim, notReverse,
    rtrimCollationText_append_space, Value.compare_text_refl]

private def deduplicateNonNullValues (collation : String) (values : Array Value) : Array Value := Id.run do
  let mut distinct := #[]
  for value in values do
    unless value matches .null do
      unless distinct.any (fun prior => collatedCompare collation prior value == .eq) do
        distinct := distinct.push value
  pure distinct

private def rowsEqualCollated (collations : Array String) (left right : Array Value) : Bool :=
  left.size == right.size && (Array.range left.size).all fun index =>
    collatedCompare (collations[index]?.getD "binary") left[index]! right[index]! == .eq

theorem rowsEqualCollated_same_width (collations : Array String) (left right : Array Value)
    (equal : rowsEqualCollated collations left right = true) : left.size = right.size := by
  have sizesEqual : (left.size == right.size) = true := (Bool.and_eq_true_iff.mp equal).1
  exact beq_iff_eq.mp sizesEqual

private def containsCollated (collations : Array String) (rows : Array (Array Value))
    (row : Array Value) : Bool :=
  rows.any (rowsEqualCollated collations row)

private def distinctCollated (collations : Array String)
    (rows : Array (Array Value)) : Array (Array Value) := Id.run do
  let mut distinct := #[]
  for row in rows do
    unless containsCollated collations distinct row do distinct := distinct.push row
  return distinct

private def combineCompoundRowsCollated (collations : Array String) (operation : CompoundOp)
    (left right : Array (Array Value)) : Array (Array Value) :=
  match operation with
  | .unionAll => combineCompoundRows .unionAll left right
  | .unionDistinct => distinctCollated collations
      (combineCompoundRows .unionDistinct left right)
  | .except => distinctCollated collations (left.filter fun row =>
      !containsCollated collations right row)
  | .intersect => distinctCollated collations (left.filter fun row =>
      containsCollated collations right row)

private def rowLessCollated (collations : Array String) (left right : Array Value) : Bool := Id.run do
  for index in [:min left.size right.size] do
    let order := collatedCompare (collations[index]?.getD "binary") left[index]! right[index]!
    if order != .eq then return order == .lt
  return left.size < right.size

private def insertRowCollated (collations : Array String) (rows : List (Array Value))
    (row : Array Value) : List (Array Value) :=
  match rows with
  | [] => [row]
  | first :: rest => if rowLessCollated collations row first then row :: first :: rest
    else first :: insertRowCollated collations rest row

private def sortRowsCollated (collations : Array String)
    (rows : Array (Array Value)) : Array (Array Value) :=
  (rows.foldl (insertRowCollated collations) []).toArray

private def nullOrderLess? (descending : Bool) (nullsFirst : Option Bool)
    (left right : Value) : Option Bool :=
  match left, right with
  | .null, .null => none
  | .null, _ => some (nullsFirst.getD (!descending))
  | _, .null => some (!(nullsFirst.getD (!descending)))
  | _, _ => none

private def orderedValueRowsLess (keys : Array (Nat × Bool × String × Option Bool))
    (a b : Array Value) : Bool := Id.run do
  for (index, descending, collation, nullsFirst) in keys do
    if let some before := nullOrderLess? descending nullsFirst (a[index]?.getD .null) (b[index]?.getD .null) then
      return before
    let ord := collatedCompare collation (a[index]?.getD .null) (b[index]?.getD .null)
    if ord != .eq then return if descending then ord == .gt else ord == .lt
  return false

private def insertOrderedValueRow (keys : Array (Nat × Bool × String × Option Bool))
    (rows : List (Array Value)) (row : Array Value) : List (Array Value) :=
  match rows with
  | [] => [row]
  | first :: rest =>
    if orderedValueRowsLess keys row first then row :: first :: rest
    else first :: insertOrderedValueRow keys rest row

private def sortOrderedValueRows (keys : Array (Nat × Bool × String × Option Bool))
    (rows : Array (Array Value)) : Array (Array Value) :=
  (rows.foldl (insertOrderedValueRow keys) []).toArray

private def compoundOrderKeys (db : Database) (query : Select) (names : Array String) :
    Except String (Array (Nat × Bool × String × Option Bool)) := do
  let schema := selectColumnSchema db query
  query.orderBy.mapIdxM fun position term => do
    let index ← compoundOrderIndex db query names position term.expr
    let inherited := schema[index]?.map (·.collation) |>.getD "binary"
    pure (index, term.descending, term.expr.explicitOrderCollation?.getD inherited, term.nullsFirst)

private structure KeyedRow where
  values : Array Value
  keys : Array (Value × Bool × String × Option Bool)

private def keyedRowLess (left right : KeyedRow) : Bool := Id.run do
  for index in [:min left.keys.size right.keys.size] do
    let (leftValue, descending, collation, nullsFirst) := left.keys[index]!
    let rightValue := right.keys[index]!.1
    if let some before := nullOrderLess? descending nullsFirst leftValue rightValue then return before
    let order := collatedCompare collation leftValue rightValue
    if order != .eq then return if descending then order == .gt else order == .lt
  return false

private def insertKeyedRow (rows : List KeyedRow) (row : KeyedRow) : List KeyedRow :=
  match rows with
  | [] => [row]
  | first :: rest => if keyedRowLess row first then row :: first :: rest
    else first :: insertKeyedRow rest row

private def sortKeyedRows (rows : Array KeyedRow) : Array (Array Value) :=
  (rows.foldl insertKeyedRow []).toArray.map (·.values)

private def valueKeysLess (left right : Array Value) : Bool := Id.run do
  for i in [:min left.size right.size] do
    let order := left[i]!.compare right[i]!
    if order != .eq then return order == .lt
  return left.size < right.size

private def insertValueKeyed {α} (item : Array Value × α) :
    List (Array Value × α) → List (Array Value × α)
  | [] => [item]
  | first :: rest =>
    if valueKeysLess item.1 first.1 then item :: first :: rest
    else first :: insertValueKeyed item rest

private def sortValueKeyed {α} (items : Array (Array Value × α)) : Array (Array Value × α) :=
  (items.foldl (fun sorted item => insertValueKeyed item sorted) []).toArray

private theorem insertValueKeyed_perm {α} (item : Array Value × α)
    (items : List (Array Value × α)) :
    (insertValueKeyed item items).Perm (item :: items) := by
  induction items with
  | nil => exact List.Perm.refl _
  | cons first rest induction =>
      unfold insertValueKeyed
      split
      · exact List.Perm.refl _
      · exact (induction.cons first).trans (List.Perm.swap item first rest)

private theorem foldInsertValueKeyed_perm {α}
    (items accumulator : List (Array Value × α)) :
    (items.foldl (fun sorted item => insertValueKeyed item sorted) accumulator).Perm
      (items ++ accumulator) := by
  induction items generalizing accumulator with
  | nil => exact List.Perm.refl _
  | cons item items induction =>
      have tail := induction (insertValueKeyed item accumulator)
      have inserted := (insertValueKeyed_perm item accumulator).append_left items
      exact tail.trans (inserted.trans List.perm_middle)

private theorem sortValueKeyed_perm {α} (items : Array (Array Value × α)) :
    (sortValueKeyed items).toList.Perm items.toList := by
  unfold sortValueKeyed
  simpa using foldInsertValueKeyed_perm items.toList []

private def isLeapYear (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

private def daysInYear (year : Nat) : Nat := if isLeapYear year then 366 else 365

private theorem daysInYear_positive (year : Nat) : 0 < daysInYear year := by
  simp only [daysInYear]
  split <;> omega

private def yearAndDay (days year : Nat) : Nat × Nat :=
  if days < daysInYear year then (year, days)
  else yearAndDay (days - daysInYear year) (year + 1)
termination_by days
decreasing_by have := daysInYear_positive year; omega

private theorem yearAndDay_returns_valid_day (days year : Nat) :
    let result := yearAndDay days year
    result.2 < daysInYear result.1 := by
  rw [yearAndDay]
  split
  · assumption
  · exact yearAndDay_returns_valid_day (days - daysInYear year) (year + 1)
termination_by days
decreasing_by have := daysInYear_positive year; omega

private def daysInMonth (year month : Nat) : Nat :=
  if month == 2 then if isLeapYear year then 29 else 28
  else if month == 4 || month == 6 || month == 9 || month == 11 then 30
  else 31

private theorem daysInMonth_positive (year month : Nat) : 0 < daysInMonth year month := by
  simp only [daysInMonth]
  split <;> split <;> omega

private def monthAndDay (year remaining month : Nat) : Nat × Nat :=
  if remaining < daysInMonth year month then (month, remaining + 1)
  else monthAndDay year (remaining - daysInMonth year month) (month + 1)
termination_by remaining
decreasing_by have := daysInMonth_positive year month; omega

private theorem monthAndDay_returns_valid_day (year remaining month : Nat) :
    let result := monthAndDay year remaining month
    1 ≤ result.2 ∧ result.2 ≤ daysInMonth year result.1 := by
  rw [monthAndDay]
  split
  · simp only [Prod.fst, Prod.snd]
    constructor <;> omega
  · exact monthAndDay_returns_valid_day year (remaining - daysInMonth year month) (month + 1)
termination_by remaining
decreasing_by have := daysInMonth_positive year month; omega

private def pad2 (value : Nat) : String :=
  if value < 10 then "0" ++ toString value else toString value

/-- Pure UTC conversion keeps time-dependent SQL deterministic and testable. -/
private def dateTimeStrings (epoch : Int) : String × String × String :=
  let nonnegative := max 0 epoch |>.toNat
  let days := nonnegative / 86400
  let seconds := nonnegative % 86400
  let (year, dayOfYear) := yearAndDay days 1970
  let (month, day) := monthAndDay year dayOfYear 1
  let hour := seconds / 3600
  let minute := (seconds % 3600) / 60
  let second := seconds % 60
  let date := toString year ++ "-" ++ pad2 month ++ "-" ++ pad2 day
  let time := pad2 hour ++ ":" ++ pad2 minute ++ ":" ++ pad2 second
  (date, time, date ++ " " ++ time)

private def expressionMentionsColumn (target : String) (expression : Expr) : Bool :=
  expression.any fun
    | .column _ name => nameEq name target
    | _ => false

private def miniHasAggregate (expression : Expr) : Bool :=
  expression.anyOutsideSubqueries fun
    | .call name args _ =>
        let name := aggregateFunctionName name
        ["count", "sum", "total", "avg", "group_concat", "string_agg",
          "legacy_count", "md5sum"].contains name ||
          ((nameEq name "min" || nameEq name "max") && args.size == 1)
    | _ => false

mutual
  private def evalWithDbFuel : Nat → Database → Env → Expr → Except String Value
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, env, expr => do
      evalExpr env (← resolveSubqueriesFuel fuel db env expr)

  private def resolveSubqueriesFuel : Nat → Database → Env → Expr → Except String Expr
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, env, expr => match expr with
    | .column none name =>
      let (date, time, timestamp) := dateTimeStrings db.currentTime
      if nameEq name "current_date" then pure (.literal (.text date))
      else if nameEq name "current_time" then pure (.literal (.text time))
      else if nameEq name "current_timestamp" then pure (.literal (.text timestamp))
      else pure (.column none name)
    | .scalarSubquery sql => do
      let statements ← parse sql
      let width := match statements[0]? with
        | some (Statement.select query) => (selectColumnSchema db query).size
        | some (Statement.values rows) => rows[0]?.map Array.size |>.getD 0
        | _ => 0
      if width != 1 then throw s!"sub-select returns {width} columns - expected 1"
      let rows ← evalMiniQueryFuel fuel db env sql
      pure (.literal (rows[0]?.bind (·[0]?) |>.getD .null))
    | .inSubquery arg sql negated => do
      let arg ← resolveSubqueriesFuel fuel db env arg
      let statements ← parse sql
      let width := match statements[0]? with
        | some (Statement.select query) => (selectColumnSchema db query).size
        | some (Statement.values rows) => rows[0]?.map Array.size |>.getD 0
        | _ => 0
      if width != 1 then throw s!"sub-select returns {width} columns - expected 1"
      let rows ← evalMiniQueryFuel fuel db env sql
      let applyLeftAffinity ← match (← parse sql)[0]? with
        | some (Statement.select query) =>
          pure <| !(selectColumnSchema db query)[0]?.any (fun column =>
            nameEq column.declaredType "BLOB")
        | _ => pure true
      pure (Expr.inList arg (rows.filterMap (·[0]?) |>.map Expr.literal) negated applyLeftAffinity)
    | .existsSubquery sql => do
      let rows ← evalMiniQueryFuel fuel db env sql
      pure (.literal (.integer (if rows.isEmpty then 0 else 1)))
    | .unary op e => do pure (.unary op (← resolveSubqueriesFuel fuel db env e))
    | .binary op a b => do pure (.binary op (← resolveSubqueriesFuel fuel db env a) (← resolveSubqueriesFuel fuel db env b))
    | .call name args star =>
      if nameEq name "lean_check_myfunc" && !db.checkMyfuncEnabled then
        throw "no such function: myfunc()"
      else if nameEq name "implies_nonnull_row" then
        match args.toList with
        | [expression, .column _ target] =>
          pure (.literal (.integer (if expressionMentionsColumn target expression then 1 else 0)))
        | _ => throw "wrong number of arguments to function implies_nonnull_row()"
      else if nameEq name "last_insert_rowid" then
        if star || !args.isEmpty then throw "wrong number of arguments to function last_insert_rowid()"
        else pure (.literal (.integer db.lastInsertRowid))
      else if ["time", "date", "datetime"].contains name.toLower then
        match args.toList with
        | [] =>
          let (date, time, timestamp) := dateTimeStrings db.currentTime
          pure (.literal (.text (if nameEq name "time" then time
            else if nameEq name "date" then date else timestamp)))
        | [.literal (.text argument)] =>
          if nameEq argument "now" then
            let (date, time, timestamp) := dateTimeStrings db.currentTime
            pure (.literal (.text (if nameEq name "time" then time
              else if nameEq name "date" then date else timestamp)))
          else do pure (.call name (← args.mapM (resolveSubqueriesFuel fuel db env)) star)
        | _ => do pure (.call name (← args.mapM (resolveSubqueriesFuel fuel db env)) star)
      else if nameEq name "lean_dqs" then
        match args.toList with
        | [.literal (.text identifier)] =>
          match resolveColumn env none identifier with
          | .ok value => pure (.literal value)
          | .error message => if message.startsWith "no such column: " && db.doubleQuotedStrings then
              pure (.literal (.text identifier))
            else if message.startsWith "no such column: " then
              throw s!"no such column: \"{identifier}\" - should this be a string literal in single-quotes?"
            else throw message
        | _ => throw "malformed double-quoted string expression"
      else do pure (.call name (← args.mapM (resolveSubqueriesFuel fuel db env)) star)
    | .isNull e n => do pure (.isNull (← resolveSubqueriesFuel fuel db env e) n)
    | .inList e values n applyAffinity => do
      pure (.inList (← resolveSubqueriesFuel fuel db env e) (← values.mapM (resolveSubqueriesFuel fuel db env)) n applyAffinity)
    | .collate e name => do pure (.collate (← resolveSubqueriesFuel fuel db env e) name)
    | .case_ base branches else_ => do
      let base ← base.mapM (resolveSubqueriesFuel fuel db env)
      let branches ← branches.mapM fun (a, b) => do
        pure (← resolveSubqueriesFuel fuel db env a, ← resolveSubqueriesFuel fuel db env b)
      let else_ ← else_.mapM (resolveSubqueriesFuel fuel db env)
      pure (.case_ base branches else_)
    | e => pure e

  private def evalMiniQueryFuel : Nat → Database → Env → String →
      Except String (Array (Array Value))
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, outer, sql => do
    let statements ← parse sql
    match statements[0]? with
    | some (Statement.select query) => evalMiniSelectFuel fuel db outer query
    | some (Statement.values rows) => rows.mapM fun row => row.mapM (evalWithDbFuel fuel db outer)
    | _ => throw "subquery must be a SELECT or VALUES"

  private def evalMiniSelectFuel : Nat → Database → Env → Select →
      Except String (Array (Array Value))
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, outer, query => do
    if let some expressionRows := query.valueRows then
      let mut result ← expressionRows.mapM fun row => row.mapM (evalWithDbFuel fuel db outer)
      let width := query.columns.size
      let collations := (selectColumnSchema db query).map (·.collation)
      unless result.all (fun row => row.size == width) do
        throw "all VALUES must have the same number of terms"
      for (operation, right) in query.compounds do
        let next ← evalMiniSelectFuel fuel db outer right
        unless (selectColumnSchema db right).size == width && next.all (fun row => row.size == width) do
          throw s!"SELECTs to the left and right of {operation.sqlName} do not have the same number of result columns"
        result := combineCompoundRowsCollated collations operation result next
        unless operation == .unionAll do result := sortRowsCollated collations result
      if !query.orderBy.isEmpty then
        let names := selectColumnNames db query
        let keys ← compoundOrderKeys db query names
        result := sortOrderedValueRows keys result
      return result.extract query.offset (query.offset + query.limit.getD result.size)
    -- Hidden outer bindings remain addressable when no local binding matches,
    -- while local bindings correctly win unqualified-name resolution.
    let hiddenOuter := outer.map Binding.outerScoped
    let mut envs : Array Env := #[hiddenOuter]
    let mut template := hiddenOuter
    for ref in query.sources do
      let table ← if let some nestedSql := ref.subquerySql then
          let rows ← evalMiniQueryFuel fuel db outer nestedSql
          let nestedStatements ← parse nestedSql
          let columns ← match nestedStatements[0]? with
            | some (Statement.select nested) => pure (selectColumnSchema db nested)
            | some (Statement.values values) => pure ((valuesColumnNames
                (values[0]?.map Array.size |>.getD 0)).map fun name => ({ name } : Column))
            | _ => throw "derived table must be a SELECT or VALUES"
          let columns := applyColumnAliases ref.columnAliases columns
          let stored := rows.mapIdx fun i values => StoredRow.mk (Int.ofNat (i + 1)) values
          let rowStore ← RowStore.checked stored columns.size
          pure (Table.mk ref.name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[])
        else if let some view := findView? db ref.name then
          evalViewTableFuel fuel db ref.name view
        else if nameEq ref.name "sqlite_master" || nameEq ref.name "sqlite_schema" then
          let columns : Array Column := #[{ name := "type" }, { name := "name" }, { name := "tbl_name" },
            { name := "rootpage" }, { name := "sql" }]
          let viewRows := db.views.toArray.mapIdx fun i view => StoredRow.mk (Int.ofNat (i + 1))
            #[.text "view", .text view.name, .text view.name, .integer 0, .text view.sourceSql]
          let tableRows := db.tables.toArray.mapIdx fun i t => StoredRow.mk
            (Int.ofNat (db.views.length + i + 1))
            #[.text "table", .text t.name, .text t.name, .integer (Int.ofNat (i + 2)),
              .text s!"CREATE TABLE {t.name}"]
          let triggerRows := db.triggers.toArray.mapIdx fun i trigger => StoredRow.mk
            (Int.ofNat (db.views.length + db.tables.length + i + 1))
            #[.text "trigger", .text trigger.name, .text trigger.table, .integer 0,
              .text trigger.sourceSql]
          let indexRows := db.indexes.toArray.mapIdx fun i index => StoredRow.mk
            (Int.ofNat (db.views.length + db.tables.length + db.triggers.length + i + 1))
            #[.text "index", .text index.name, .text index.table, .integer 0, .text index.sql]
          let stored := viewRows ++ tableRows ++ triggerRows ++ indexRows
          let rowStore ← RowStore.checked stored columns.size
          pure (Table.mk ref.name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[])
        else optionOr (findTable? db ref.name) s!"no such table: {ref.name}"
      if let some alias := ref.alias then
        if let some duplicate := table.columns.find? (fun column => template.any (fun binding =>
            !binding.hidden && nameEq binding.alias alias && nameEq binding.column column.name)) then
          throw s!"ambiguous column name: {alias}.{duplicate.name}"
      let leftTemplate := template
      for column in ref.usingColumns do
        unless leftTemplate.any (fun binding => !binding.hidden && nameEq binding.column column) &&
            table.columns.any (fun candidate => nameEq candidate.name column) do
          throw s!"cannot join using column {column} - column not present in both tables"
      let naturalTemplateColumns := if ref.naturalJoin then table.columns.filterMap fun column =>
        if leftTemplate.any (fun left => !left.hidden && nameEq left.column column.name)
        then some column.name else none
        else #[]
      let templateUsingColumns := ref.usingColumns ++ naturalTemplateColumns
      let nullRow : StoredRow := { rowid := 0, values := table.columns.map fun _ => .null }
      let rightTemplate := (miniBindings ref table nullRow).map fun binding =>
        if templateUsingColumns.any (nameEq binding.column) then { binding with hidden := true }
        else binding
      let mut next := #[]
      let mut matchedRight := Std.HashSet.emptyWithCapacity (capacity := table.rows.size)
      for baseEnv in envs do
        let mut matched := false
        let naturalColumns := if ref.naturalJoin then table.columns.filterMap fun column =>
          if baseEnv.any (fun left => !left.hidden && nameEq left.column column.name)
          then some column.name else none
          else #[]
        let usingColumns := ref.usingColumns ++ naturalColumns
        for rowIndex in [:table.rows.size] do
          let row := table.rows[rowIndex]!
          let right := miniBindings ref table row
          let combined := baseEnv ++ right
          let usingMatches ← usingColumns.allM (joinColumnMatches baseEnv right)
          let onMatches ← match ref.joinOn with
            | none => pure true
            | some condition => pure ((← evalWithDbFuel fuel db combined condition).truth == .true)
          if usingMatches && onMatches then
            let projectedRight := right.map fun binding =>
              if usingColumns.any (nameEq binding.column) then { binding with hidden := true }
              else binding
            next := next.push (baseEnv ++ projectedRight)
            matched := true
            matchedRight := matchedRight.insert rowIndex
        if ref.leftJoin && !matched then
          let projectedRight := (miniBindings ref table nullRow).map fun binding =>
            if usingColumns.any (nameEq binding.column) then { binding with hidden := true }
            else binding
          next := next.push (baseEnv ++ projectedRight)
      if ref.rightJoin then
        for rowIndex in [:table.rows.size] do
          unless matchedRight.contains rowIndex do
            let right := miniBindings ref table table.rows[rowIndex]!
            let projectedRight := right.map fun binding =>
              if templateUsingColumns.any (nameEq binding.column) then { binding with hidden := true }
              else binding
            next := next.push (leftTemplate.map (fun binding => { binding with value := .null }) ++ projectedRight)
      envs := next
      template := leftTemplate ++ rightTemplate
    let mut filtered := #[]
    for candidate in envs do
      let keep ← match query.where_ with
        | none => pure true
        | some condition => do pure ((← evalWithDbFuel fuel db candidate condition).truth == .true)
      if keep then filtered := filtered.push candidate
    let isAggregate := !query.groupBy.isEmpty || query.columns.any (fun col => miniHasAggregate col.expr) ||
      query.having.any miniHasAggregate
    let mut groupedInput := #[]
    for env in filtered do
      let mut enriched := env
      for column in query.columns do
        if let some alias := column.alias then
          unless miniHasAggregate column.expr || enriched.any (fun binding =>
              binding.hidden && nameEq binding.column alias) do
            let value ← evalWithDbFuel fuel db env column.expr
            enriched := enriched.push (Binding.mk "" "" alias value true 0 "binary" "LEAN_HIDDEN")
      groupedInput := groupedInput.push enriched
    let mut groups : Array (Array Env) := #[]
    if query.groupBy.isEmpty then groups := #[groupedInput]
    else
      let mut keys : Array (Array Value) := #[]
      for env in groupedInput do
        let key ← query.groupBy.mapM fun term =>
          match term with
          | .literal (.integer index) =>
            if index > 0 && index.toNat <= query.columns.size then
              match query.columns[index.toNat - 1]!.expr with
              | .star qualifier => pure <| env.find? (fun binding => binding.depth == 0 &&
                  (!binding.hidden || (qualifier.isSome && binding.declaredType != "LEAN_HIDDEN")) &&
                  qualifier.all (fun q => nameEq q binding.alias || nameEq q binding.table))
                |>.map (·.value) |>.getD .null
              | expression => evalWithDbFuel fuel db env expression
            else evalWithDbFuel fuel db env term
          | _ => evalWithDbFuel fuel db env term
        match keys.findIdx? (· == key) with
        | some index => groups := groups.set! index (groups[index]!.push env)
        | none => keys := keys.push key; groups := groups.push #[env]
      let preserveInputOrder := query.groupBy.any fun term => term matches .unary .neg _
      unless preserveInputOrder do groups := (sortValueKeyed (keys.zip groups)).map (·.2)
    let baseRows ← if isAggregate then
      let mut rows := #[]
      for group in groups do
        unless group.isEmpty && !query.groupBy.isEmpty do
          let mut row := #[]
          for column in query.columns do
            match column.expr with
            | .star qualifier =>
              let representative := group[0]?.getD #[]
              for binding in representative do
                if binding.depth == 0 &&
                    (!binding.hidden || (qualifier.isSome && binding.declaredType != "LEAN_HIDDEN")) &&
                    qualifier.all (fun q => nameEq q binding.alias || nameEq q binding.table) then
                  row := row.push binding.value
            | expression => row := row.push (← evalMiniAggregateFuel fuel db group expression)
          let mut aliases : Env := #[]
          for i in [:query.columns.size] do
            if let some alias := query.columns[i]!.alias then
              aliases := aliases.push (Binding.mk "" "" alias (row[i]?.getD .null)
                true 0 "binary" "LEAN_HIDDEN")
          let withAliases := group.map fun env => env ++ aliases
          let keep ← match query.having with
            | none => pure true
            | some condition =>
              pure ((← evalMiniAggregateFuel fuel db withAliases condition).truth == .true)
          if keep then rows := rows.push row
      pure rows
    else
      filtered.mapM fun e => do
        let mut row := #[]
        for col in query.columns do
          match col.expr with
          | .star qualifier =>
            unless e.any (fun b => b.depth == 0 &&
                (!b.hidden || (qualifier.isSome && b.declaredType != "LEAN_HIDDEN")) &&
                qualifier.all (fun q => nameEq q b.alias || nameEq q b.table)) do
              throw "no tables specified"
            for b in e do
              if b.depth == 0 && (!b.hidden || (qualifier.isSome && b.declaredType != "LEAN_HIDDEN")) &&
                  qualifier.all (fun q => nameEq q b.alias || nameEq q b.table) then
                row := row.push b.value
          | expr => row := row.push (← evalWithDbFuel fuel db e expr)
        pure row
    let mut result := baseRows
    let collations := (selectColumnSchema db query).map (·.collation)
    let mut aggregateOrderHandled := false
    if query.compounds.isEmpty && isAggregate && query.having.isNone && !query.orderBy.isEmpty then
      let names := selectColumnNames db query
      let mut keyed := #[]
      for index in [:min result.size groups.size] do
        let values := result[index]!
        let group := groups[index]!
        let representative := group[0]?.getD #[]
        let keys ← query.orderBy.mapM fun term => do
          let value ← match term.expr with
            | .literal (.integer ordinal) =>
              if ordinal > 0 && ordinal.toNat <= values.size then pure values[ordinal.toNat - 1]!
              else throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
            | .column none name => match names.findIdx? (nameEq name) with
              | some output => pure values[output]!
              | none => evalMiniAggregateFuel fuel db group term.expr
            | expression => evalMiniAggregateFuel fuel db group expression
          pure (value, term.descending,
            term.expr.explicitOrderCollation?.getD (term.expr.collationIn representative), term.nullsFirst)
        keyed := keyed.push { values, keys }
      result := sortKeyedRows keyed
      aggregateOrderHandled := true
    if query.compounds.isEmpty && !query.orderBy.isEmpty && !isAggregate then
      let names := selectColumnNames db query
      let mut keyed := #[]
      for index in [:result.size] do
        let env := filtered[index]!
        let values := result[index]!
        let keys ← query.orderBy.mapM fun term => do
          let value ← match term.expr with
            | .literal (.integer ordinal) =>
              if ordinal > 0 && ordinal.toNat <= values.size then pure values[ordinal.toNat - 1]!
              else throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
            | .unary .plus (.literal (.integer ordinal)) =>
              if ordinal > 0 && ordinal.toNat <= values.size then pure values[ordinal.toNat - 1]!
              else throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
            | .column none name => match names.findIdx? (nameEq name) with
              | some output => pure values[output]!
              | none => evalWithDbFuel fuel db env term.expr
            | expression => evalWithDbFuel fuel db env expression
          let inherited := term.expr.collationIn env
          pure (value, term.descending, term.expr.explicitOrderCollation?.getD inherited, term.nullsFirst)
        keyed := keyed.push { values, keys }
      result := sortKeyedRows keyed
    if query.distinct then
      let mut unique := #[]
      for row in result do
        unless containsCollated collations unique row do unique := unique.push row
      result := unique
      if query.orderBy.isEmpty && shouldSortDistinctByIndex db query then
        result := sortRowsCollated collations result
    for (operation, right) in query.compounds do
      let next ← evalMiniSelectFuel fuel db outer right
      if (selectColumnSchema db query).size != (selectColumnSchema db right).size then
        throw s!"SELECTs to the left and right of {operation.sqlName} do not have the same number of result columns"
      result := combineCompoundRowsCollated collations operation result next
      unless operation == .unionAll do result := sortRowsCollated collations result
    if !query.orderBy.isEmpty && (!query.compounds.isEmpty || (isAggregate && !aggregateOrderHandled)) then
      let names := selectColumnNames db query
      let keys ← compoundOrderKeys db query names
      result := sortOrderedValueRows keys result
    pure (result.extract query.offset (query.offset + query.limit.getD result.size))

  private def evalMiniAggregateFuel : Nat → Database → Array Env → Expr → Except String Value
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, envs, expr => do
    match expr with
    | .call name args star =>
      let distinct := isDistinctAggregateName name
      let lname := aggregateFunctionName name
      if distinct && args.size != 1 then
        throw "DISTINCT aggregates must have exactly one argument"
      else if lname == "count" then
        if star || args.isEmpty then pure (.integer envs.size)
        else if args.size == 1 then
          let mut values ← envs.mapM fun env => evalWithDbFuel fuel db env args[0]!
          if distinct then
            values := deduplicateNonNullValues
              (args[0]!.collationIn (envs[0]?.getD #[])) values
          pure (.integer (values.filter (fun value => !(value matches .null))).size)
        else throw "wrong number of arguments to function count()"
      else if ["sum", "total", "avg"].contains lname && args.size == 1 then
        let mut values ← envs.mapM fun env => evalWithDbFuel fuel db env args[0]!
        if distinct then
          values := deduplicateNonNullValues
            (args[0]!.collationIn (envs[0]?.getD #[])) values
        let numbers := values.filterMap Value.toFloat?
        if numbers.isEmpty then pure (if lname == "total" then .real 0.0 else .null)
        else
          let total := numbers.foldl (· + ·) 0.0
          if lname == "avg" then pure (.real (total / numbers.size.toFloat))
          else if lname == "sum" && values.all (fun value => value matches .integer _) then
            pure (.integer (values.foldl (init := 0) fun sum value => sum + value.toInt?.getD 0))
          else pure (.real total)
      else if (lname == "min" || lname == "max") && args.size == 1 then
        let mut values ← envs.mapM fun env => evalWithDbFuel fuel db env args[0]!
        if distinct then
          values := deduplicateNonNullValues
            (args[0]!.collationIn (envs[0]?.getD #[])) values
        pure (scalarMinMax (lname == "max") (values.filter fun value => !(value matches .null)))
      else
        let values ← args.mapM (evalMiniAggregateFuel fuel db envs)
        evalExpr #[] (.call name (values.map Expr.literal) star)
    | .binary op left right =>
      let left ← evalMiniAggregateFuel fuel db envs left
      let right ← evalMiniAggregateFuel fuel db envs right
      evalExpr #[] (.binary op (.literal left) (.literal right))
    | .unary op argument =>
      evalExpr #[] (.unary op (.literal (← evalMiniAggregateFuel fuel db envs argument)))
    | .isNull argument negated =>
      evalExpr #[] (.isNull (.literal (← evalMiniAggregateFuel fuel db envs argument)) negated)
    | .collate argument name =>
      evalExpr #[] (.collate (.literal (← evalMiniAggregateFuel fuel db envs argument)) name)
    | other => evalWithDbFuel fuel db (envs[0]?.getD #[]) other

  private def evalViewTableFuel : Nat → Database → String → View → Except String Table
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, tableName, view => do
    unless db.viewsEnabled || view.temporary do throw s!"access to view \"{view.name}\" prohibited"
    if view.query.callsDirectOnly then throw "unsafe use of testdirectonly()"
    if db.viewStack.length + 1 >= db.viewDepthLimit then
      throw "VIEWs and/or subqueries nested too deep"
    if db.viewStack.any (nameEq view.name) then throw s!"view {view.name} is circularly defined"
    let nestedDb := { db with
      viewStack := view.name :: db.viewStack
      ignoreTempViews := !view.temporary }
    let rows ← match evalMiniSelectFuel fuel nestedDb #[] view.query with
      | .ok rows => pure rows
      | .error message =>
        if !view.temporary && message.startsWith "no such table: " &&
            !(message.drop "no such table: ".length).toString.toList.contains '.' then
          throw ("no such table: main." ++ (message.drop "no such table: ".length).toString)
        else throw message
    let inferred := selectColumnSchema nestedDb view.query
    let columns := match view.columns with
      | none => inferred
      | some names => inferred.mapIdx fun i column => { column with name := names[i]?.getD column.name }
    let columns := deduplicateColumns columns
    unless rows.all (fun row => row.size == columns.size) do
      throw s!"expected {columns.size} columns for view {view.name}"
    let stored := rows.mapIdx fun i values => StoredRow.mk (Int.ofNat (i + 1)) values
    let rowStore ← RowStore.checked stored columns.size
    pure (Table.mk tableName columns rowStore (Int.ofNat (stored.size + 1)) #[] #[])
end

private def evaluationDepth (db : Database) : Nat := db.viewDepthLimit + 2001

private theorem evaluationDepth_exceeds_view_limit (db : Database) :
    db.viewDepthLimit < evaluationDepth db := by
  unfold evaluationDepth
  omega

private def evalWithDb (db : Database) (env : Env) (expression : Expr) : Except String Value :=
  evalWithDbFuel (evaluationDepth db + expression.height) db env expression

/-- Attach expression-index keys without dropping or duplicating candidate
environments. This helper is on the live SELECT path below. -/
def expressionIndexKeyRows (db : Database) (expressions : Array Expr) :
    List Env → Except String (List (Array Value × Env))
  | [] => .ok []
  | env :: envs =>
      match expressions.mapM (evalWithDb db env) with
      | .error message => .error message
      | .ok keys =>
          match expressionIndexKeyRows db expressions envs with
          | .error message => .error message
          | .ok tail => .ok ((keys, env) :: tail)

theorem expressionIndexKeyRows_preserves_rows
    (db : Database) (expressions : Array Expr) (envs : List Env)
    {keyed : List (Array Value × Env)}
    (success : expressionIndexKeyRows db expressions envs = .ok keyed) :
    keyed.map (·.2) = envs := by
  induction envs generalizing keyed with
  | nil =>
      simp [expressionIndexKeyRows] at success
      subst keyed
      rfl
  | cons env envs induction =>
      unfold expressionIndexKeyRows at success
      cases keysResult : expressions.mapM (evalWithDb db env) with
      | error message => simp [keysResult] at success
      | ok keys =>
          rw [keysResult] at success
          cases tailResult : expressionIndexKeyRows db expressions envs with
          | error message => simp [tailResult] at success
          | ok tail =>
              rw [tailResult] at success
              simp only [Except.ok.injEq] at success
              subst keyed
              simp [induction tailResult]

/-- The live expression-index branch evaluates keys and uses them only to
reorder rows. It does not yet perform indexed lookup. -/
def evalIndex (db : Database) (expressions : Array Expr)
    (filtered : Array Env) : Except String (List Env) :=
  match expressionIndexKeyRows db expressions filtered.toList with
  | .error message => .error message
  | .ok keyed => .ok ((sortValueKeyed keyed.toArray).map (·.2)).toList

def evalScan (filtered : Array Env) : List Env := filtered.toList

/-- The actual live expression-index ordering path is bag-equivalent to the
full-scan candidate list: evaluating and sorting keys can neither lose nor
duplicate a row. -/
theorem index_matches_scan (db : Database) (expressions : Array Expr)
    (filtered : Array Env) {indexed : List Env}
    (success : evalIndex db expressions filtered = .ok indexed) :
    indexed.Perm (evalScan filtered) := by
  unfold evalIndex at success
  cases keyedResult : expressionIndexKeyRows db expressions filtered.toList with
  | error message => simp [keyedResult] at success
  | ok keyed =>
      rw [keyedResult] at success
      simp only [Except.ok.injEq] at success
      subst indexed
      have sorted := (sortValueKeyed_perm keyed.toArray).map (fun pair => pair.2)
      have keysPreserve := expressionIndexKeyRows_preserves_rows db expressions
        filtered.toList keyedResult
      simpa [evalScan, keysPreserve] using sorted

private def evalMiniQuery (db : Database) (outer : Env) (sql : String) :
    Except String (Array (Array Value)) :=
  evalMiniQueryFuel (evaluationDepth db) db outer sql

private def evalMiniSelect (db : Database) (outer : Env) (query : Select) :
    Except String (Array (Array Value)) :=
  evalMiniSelectFuel (evaluationDepth db + query.compoundHeight) db outer query

private def evalViewTable (db : Database) (tableName : String) (view : View) : Except String Table :=
  evalViewTableFuel (evaluationDepth db + view.query.compoundHeight) db tableName view

theorem evalWithDb_literal (db : Database) (env : Env) (value : Value) :
    evalWithDb db env (.literal value) = .ok value := by
  simp only [evalWithDb, evaluationDepth, Expr.height, evalWithDbFuel,
    resolveSubqueriesFuel, evalExpr_literal]
  simpa using evalExpr_literal env value

private def Expr.hasAggregate (expression : Expr) : Bool :=
  expression.anyOutsideSubqueries fun
    | .call name args _ =>
        let name := aggregateFunctionName name
        ["count", "sum", "total", "avg", "group_concat", "string_agg",
          "legacy_count", "md5sum"].contains name ||
          ((nameEq name "min" || nameEq name "max") && args.size == 1)
    | _ => false

private def Expr.referencesAnyColumn (expression : Expr) : Bool :=
  expression.any fun
    | .column .. => true
    | _ => false

private def Select.hasSourceFreeColumnAggregateFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, query =>
    (query.sources.isEmpty && query.columns.any (fun column =>
      column.expr.hasAggregate && column.expr.referencesAnyColumn)) ||
      query.compounds.any (fun compound =>
        hasSourceFreeColumnAggregateFuel fuel compound.2)

private def Select.hasSourceFreeColumnAggregate (query : Select) : Bool :=
  query.hasSourceFreeColumnAggregateFuel query.compoundHeight

private def Expr.hasOuterAggregateSubqueryFuel : Nat → Expr → Bool
  | 0, _ => false
  | _ + 1, .scalarSubquery sql => match parse sql with
    | .ok statements => match statements[0]? with
      | some (Statement.select query) => query.hasSourceFreeColumnAggregate
      | _ => false
    | .error _ => false
  | fuel + 1, .unary _ expression | fuel + 1, .isNull expression _ |
      fuel + 1, .collate expression _ => hasOuterAggregateSubqueryFuel fuel expression
  | fuel + 1, .binary _ left right =>
    hasOuterAggregateSubqueryFuel fuel left || hasOuterAggregateSubqueryFuel fuel right
  | fuel + 1, .call _ arguments _ =>
    arguments.any (hasOuterAggregateSubqueryFuel fuel)
  | fuel + 1, .inList expression values _ _ =>
    hasOuterAggregateSubqueryFuel fuel expression ||
      values.any (hasOuterAggregateSubqueryFuel fuel)
  | fuel + 1, .case_ base branches else_ =>
    base.any (hasOuterAggregateSubqueryFuel fuel) || branches.any (fun pair =>
      hasOuterAggregateSubqueryFuel fuel pair.1 ||
        hasOuterAggregateSubqueryFuel fuel pair.2) ||
      else_.any (hasOuterAggregateSubqueryFuel fuel)
  | fuel + 1, .inSubquery expression _ _ =>
    hasOuterAggregateSubqueryFuel fuel expression
  | _, _ => false

private def Expr.hasOuterAggregateSubquery (expression : Expr) : Bool :=
  hasOuterAggregateSubqueryFuel expression.height expression

private def Expr.hasParameter (expression : Expr) : Bool :=
  expression.any fun
    | .column none name => name == "?"
    | .call name _ _ => nameEq name "lean_unbound_parameter"
    | .scalarSubquery sql | .existsSubquery sql | .inSubquery _ sql _ => sql.contains '?'
    | _ => false

private def Expr.containsSubquery (expression : Expr) : Bool :=
  expression.any fun
    | .scalarSubquery .. | .existsSubquery .. | .inSubquery .. => true
    | _ => false

private def Expr.defaultHasNonconstantFunction (expression : Expr) : Bool :=
  expression.anyOutsideSubqueries fun
    | .call name _ _ => ["random", "randomblob", "raise"].contains name.toLower
    | _ => false

/-- SQLite's legacy DEFAULT grammar treats a lone unknown bare word as a text
literal, while a real column name (or a reference nested in an expression) is
non-constant. -/
private def defaultReferencesColumn (definitions : Array ColumnDef) (expression : Expr) : Bool :=
  match expression with
  | .column none candidate => definitions.any (fun definition => nameEq definition.name candidate)
  | _ => expressionHasRealColumn expression

private def Expr.withCheckQualifierFuel : Nat → Expr → Expr
  | 0, expression => expression
  | _ + 1, .column (some qualifier) name =>
    .column (some (if qualifier.toList.contains '.' then unqualifiedName qualifier else qualifier)) name
  | fuel + 1, .unary operation expression =>
    .unary operation (withCheckQualifierFuel fuel expression)
  | fuel + 1, .isNull expression negated =>
    .isNull (withCheckQualifierFuel fuel expression) negated
  | fuel + 1, .collate expression name =>
    .collate (withCheckQualifierFuel fuel expression) name
  | fuel + 1, .binary operation left right =>
    .binary operation (withCheckQualifierFuel fuel left) (withCheckQualifierFuel fuel right)
  | fuel + 1, .call name args hasStar =>
    .call name (args.map (withCheckQualifierFuel fuel)) hasStar
  | fuel + 1, .inList expression values negated affinity =>
    .inList (withCheckQualifierFuel fuel expression) (values.map (withCheckQualifierFuel fuel))
      negated affinity
  | fuel + 1, .case_ base branches else_ =>
    .case_ (base.map (withCheckQualifierFuel fuel))
      (branches.map fun pair =>
        (withCheckQualifierFuel fuel pair.1, withCheckQualifierFuel fuel pair.2))
      (else_.map (withCheckQualifierFuel fuel))
  | fuel + 1, .inSubquery expression sql negated =>
    .inSubquery (withCheckQualifierFuel fuel expression) sql negated
  | _, expression => expression

private def Expr.withCheckQualifier (expression : Expr) : Expr :=
  withCheckQualifierFuel expression.height expression

private def Expr.indexNondeterminismFuel? : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, .call name arguments _ =>
      let function := aggregateFunctionName name
      if function == "random" || function == "randomblob" || function == "lean_nondeterministic" then
        some "non-deterministic functions prohibited in index expressions"
      else if function == "julianday" && arguments.any (fun argument =>
          match argument with | .literal (.text value) => value.toLower == "now" | _ => false) then
        some "non-deterministic use of julianday() in an index"
      else arguments.findSome? (indexNondeterminismFuel? fuel)
  | fuel + 1, .unary _ expression | fuel + 1, .isNull expression _ |
      fuel + 1, .collate expression _ => indexNondeterminismFuel? fuel expression
  | fuel + 1, .binary _ left right =>
    indexNondeterminismFuel? fuel left <|> indexNondeterminismFuel? fuel right
  | fuel + 1, .inList expression values _ _ =>
    indexNondeterminismFuel? fuel expression <|>
      values.findSome? (indexNondeterminismFuel? fuel)
  | fuel + 1, .case_ base branches else_ =>
    base.bind (indexNondeterminismFuel? fuel) <|>
      branches.findSome? (fun pair => indexNondeterminismFuel? fuel pair.1 <|>
        indexNondeterminismFuel? fuel pair.2) <|>
      else_.bind (indexNondeterminismFuel? fuel)
  | _, _ => none

private def Expr.indexNondeterminism? (expression : Expr) : Option String :=
  indexNondeterminismFuel? expression.height expression

private def Select.hasParameterFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, query =>
    query.columns.any (fun column => column.expr.hasParameter) ||
      query.valueRows.any (fun rows => rows.any (fun row => row.any Expr.hasParameter)) ||
      query.where_.any Expr.hasParameter ||
      query.groupBy.any Expr.hasParameter || query.having.any Expr.hasParameter ||
      query.orderBy.any (fun term => term.expr.hasParameter) ||
      query.sources.any (fun source => source.subquerySql.any (·.contains '?')) ||
      query.compounds.any (fun compound => hasParameterFuel fuel compound.2)

private def Select.hasParameter (query : Select) : Bool :=
  query.hasParameterFuel query.compoundHeight

private def Expr.firstAggregateFuel? : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, .call name args _ =>
    let name := aggregateFunctionName name
    if ["count", "sum", "total", "avg", "group_concat", "string_agg",
        "legacy_count", "md5sum"].contains name ||
        ((nameEq name "min" || nameEq name "max") && args.size == 1) then some name
    else args.findSome? (firstAggregateFuel? fuel)
  | fuel + 1, .unary _ expression | fuel + 1, .isNull expression _ |
      fuel + 1, .collate expression _ => firstAggregateFuel? fuel expression
  | fuel + 1, .inList expression values _ _ =>
    firstAggregateFuel? fuel expression <|> values.findSome? (firstAggregateFuel? fuel)
  | fuel + 1, .case_ base branches else_ =>
    base.bind (firstAggregateFuel? fuel) <|>
      branches.findSome? (fun pair => firstAggregateFuel? fuel pair.1 <|>
        firstAggregateFuel? fuel pair.2) <|>
      else_.bind (firstAggregateFuel? fuel)
  | fuel + 1, .binary _ left right =>
    firstAggregateFuel? fuel left <|> firstAggregateFuel? fuel right
  | _, _ => none

private def Expr.firstAggregate? (expression : Expr) : Option String :=
  firstAggregateFuel? expression.height expression

private def Expr.referencesColumn (target : String) (expression : Expr) : Bool :=
  expression.any fun
    | .column _ name => nameEq name target
    | _ => false

private def Expr.aggregateReferencesColumn (target : String) (expression : Expr) : Bool :=
  expression.any fun
    | .call name args _ =>
        let name := aggregateFunctionName name
        let aggregate := ["count", "sum", "total", "avg", "group_concat", "string_agg",
          "legacy_count", "md5sum"].contains name ||
          ((nameEq name "min" || nameEq name "max") && args.size == 1)
        aggregate && args.any (Expr.referencesColumn target)
    | _ => false

private def aggregateValues (db : Database) (envs : Array Env) (arg : Expr) : Except String (Array Value) :=
  envs.mapM (fun env => evalWithDb db env arg)

private def distinctAggregateValues (db : Database) (envs : Array Env)
    (arg : Expr) : Except String (Array Value) := do
  let values ← aggregateValues db envs arg
  let collation := arg.collationIn (envs[0]?.getD #[])
  pure (deduplicateNonNullValues collation values)

private def aggregateEvaluationDepth : Nat := 1000

private def evalAggregateFuel : Nat → Database → Array Env → Expr → Except String Value
  | 0, _, _, _ => throw "expression tree is too large"
  | fuel + 1, db, envs, .scalarSubquery sql => do
    let statements ← parse sql
    let query ← match statements[0]? with
      | some (Statement.select query) => pure query
      | _ => throw "subquery must be a SELECT"
    let rec materialize : Nat → Select → Except String Select
      | 0, _ => throw "expression tree is too large"
      | remaining + 1, query => do
        let columns ← if query.sources.isEmpty then query.columns.mapM fun column => do
            if column.expr.hasAggregate && column.expr.referencesAnyColumn then
              let value ← evalAggregateFuel remaining db envs column.expr
              pure { column with expr := .literal value }
            else pure column
          else pure query.columns
        let compounds ← query.compounds.mapM fun compound => do
          pure (compound.1, ← materialize remaining compound.2)
        pure { query with columns, compounds }
    let rows ← evalMiniSelect db (envs[0]?.getD #[]) (← materialize fuel query)
    pure (rows[0]?.bind (·[0]?) |>.getD .null)
  | fuel + 1, db, envs, .call name args star => do
    let distinct := isDistinctAggregateName name
    let lname := aggregateFunctionName name
    let call := Expr.call name args star
    if !call.hasAggregate then
      evalWithDb db (envs[0]?.getD #[]) call
    else if distinct && args.size != 1 then
      throw "DISTINCT aggregates must have exactly one argument"
    else if lname == "count" then
      if args.isEmpty then pure (.integer envs.size)
      else if args.size != 1 then throw "wrong number of arguments to function count()"
      else
        let values ← if distinct then distinctAggregateValues db envs args[0]!
          else aggregateValues db envs args[0]!
        pure (.integer (values.foldl (init := 0) fun n v => if v matches .null then n else n + 1))
    else if ["sum", "total", "avg"].contains lname then
      if args.size != 1 then throw s!"wrong number of arguments to function {name}()"
      if let some nested := args[0]!.firstAggregate? then
        throw s!"misuse of aggregate function {nested}()"
      let values ← if distinct then distinctAggregateValues db envs args[0]!
        else aggregateValues db envs args[0]!
      let numericValues := values.filterMap fun value =>
        if value matches .null then none else some (aggregateNumericOperand value)
      let numbers := numericValues.filterMap Value.toFloat?
      if numericValues.isEmpty then pure (if lname == "total" then .real 0.0 else .null)
      else
        let total := numbers.foldl (· + ·) 0.0
        if lname == "avg" then pure (.real (total / numbers.size.toFloat))
        else if lname == "sum" && numericValues.all (fun v => v matches .integer _) then
          let mut integerTotal : Int := 0
          for value in numericValues do
            integerTotal := integerTotal + value.toInt?.getD 0
            unless inSigned64Range integerTotal do throw "integer overflow"
          pure (.integer integerTotal)
        else pure (.real total)
    else if lname == "group_concat" || lname == "string_agg" then
      if (lname == "group_concat" && (args.size != 1 && args.size != 2)) ||
          (lname == "string_agg" && args.size != 2) then
        throw s!"wrong number of arguments to function {name}()"
      let mut output := ""
      let mut found := false
      if distinct then
        let values ← distinctAggregateValues db envs args[0]!
        for value in values do
          if found then output := output ++ ","
          output := output ++ toString value
          found := true
      else
        for env in envs do
          let value ← evalWithDb db env args[0]!
          unless value matches .null do
            if found then
              let separator ← if args.size == 2 then evalWithDb db env args[1]!
                else pure (.text ",")
              unless separator matches .null do output := output ++ toString separator
            output := output ++ toString value
            found := true
      pure (if found then .text output else .null)
    else if lname == "legacy_count" then
      if !args.isEmpty then throw "wrong number of arguments to function legacy_count()"
      else pure (.integer envs.size)
    else if lname == "md5sum" then
      let mut output := ""
      for env in envs do
        for argument in args do
          let value ← evalWithDb db env argument
          unless value matches .null do output := output ++ toString value
      pure (.text output)
    else if (lname == "min" || lname == "max") && args.size == 1 then
      let values ← if distinct then distinctAggregateValues db envs args[0]!
        else aggregateValues db envs args[0]!
      pure (scalarMinMax (lname == "max") (values.filter fun v => !(v matches .null)))
    else
      let values ← args.mapM (evalAggregateFuel fuel db envs)
      evalExpr #[] (.call name (values.map Expr.literal) star)
  | fuel + 1, db, envs, .binary op a b => do
    let x ← evalAggregateFuel fuel db envs a
    let y ← evalAggregateFuel fuel db envs b
    let isComparison := [.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains op
    let representative := envs[0]?.getD #[]
    let (x, y) := if isComparison then
        comparisonValues (a.declaredTypeIn representative) (b.declaredTypeIn representative) x y
      else (x, y)
    let nocase := isComparison &&
      (nameEq (a.collationIn representative) "nocase" || nameEq (b.collationIn representative) "nocase")
    let x := if nocase then match x with | .text value => .text value.toLower | other => other else x
    let y := if nocase then match y with | .text value => .text value.toLower | other => other else y
    match op with
    | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .shiftLeft | .shiftRight =>
      pure (arithmetic op x y)
    | .eq | .ne | .lt | .le | .gt | .ge | .is | .isNot => pure (compareOp op x y)
    | .like => pure (patternOp false x y)
    | .glob => pure (patternOp true x y)
    | .match => throw "unable to use function MATCH in the requested context"
    | .and => pure (Truth.toValue (Truth.and x.truth y.truth))
    | .or => pure (Truth.toValue (Truth.or x.truth y.truth))
    | .concat => pure (if (x matches .null) || (y matches .null) then .null
        else .text (toString x ++ toString y))
    | .arrow => pure (.text (toString x ++ "->" ++ toString y))
    | .arrowText => pure (.text (toString x ++ "->>" ++ toString y))
  | fuel + 1, db, envs, .unary op e => do evalExpr #[] (.unary op (.literal (← evalAggregateFuel fuel db envs e)))
  | fuel + 1, db, envs, .isNull e n => do evalExpr #[] (.isNull (.literal (← evalAggregateFuel fuel db envs e)) n)
  | fuel + 1, db, envs, .collate e name => do evalExpr #[] (.collate (.literal (← evalAggregateFuel fuel db envs e)) name)
  | fuel + 1, db, envs, .inList e values n applyAffinity => do
    let left ← evalAggregateFuel fuel db envs e
    let right ← values.mapM (evalAggregateFuel fuel db envs)
    evalExpr #[] (.inList (.literal left) (right.map Expr.literal) n applyAffinity)
  | fuel + 1, db, envs, .case_ base branches else_ => do
    let base ← base.mapM (evalAggregateFuel fuel db envs)
    let branches ← branches.mapM fun (a, b) => do
      pure (.literal (← evalAggregateFuel fuel db envs a), .literal (← evalAggregateFuel fuel db envs b))
    let else_ ← else_.mapM (evalAggregateFuel fuel db envs)
    evalExpr #[] (.case_ (base.map Expr.literal) branches (else_.map Expr.literal))
  | _fuel + 1, db, envs, e@(.column _ _) =>
    if envs.isEmpty then pure .null else evalWithDb db envs[0]! e
  | _fuel + 1, db, envs, e => evalWithDb db (envs[0]?.getD #[]) e

def evalAggregate (db : Database) (envs : Array Env) (expression : Expr) : Except String Value :=
  evalAggregateFuel (Nat.succ (max aggregateEvaluationDepth expression.height)) db envs expression

theorem evalAggregate_fuel_covers_syntax (expression : Expr) :
    expression.height ≤ Nat.succ (max aggregateEvaluationDepth expression.height) :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)

private def makeBindings (ref : TableRef) (table : Table) (row : StoredRow) : Env :=
  let defaultAlias := unqualifiedName table.name
  let visible := table.columns.mapIdx fun i col =>
    { table := table.name, alias := ref.alias.getD defaultAlias,
      column := col.name, value := row.values[i]?.getD .null, collation := col.collation,
      declaredType := col.declaredType }
  let hidden := #["rowid", "_rowid_", "oid"].map fun name =>
    Binding.mk table.name (ref.alias.getD defaultAlias) name (.integer row.rowid)
      true 0 "binary" "LEAN_HIDDEN"
  visible ++ hidden

private def sourceEnvs (db : Database) (refs : Array TableRef) : Except String (Array Env) := do
  let mut envs : Array Env := #[#[]]
  let mut template : Env := #[]
  let mut deferredInnerOn : Array Expr := #[]
  for ref in refs do
    let schemaColumns : Array Column := #[
      { name := "type" }, { name := "name" }, { name := "tbl_name" },
      { name := "rootpage" }, { name := "sql" }]
    let viewSchemaRows : Array StoredRow := db.views.toArray.mapIdx fun i view =>
      { rowid := i + 1, values := #[.text "view", .text view.name, .text view.name,
        .integer 0, .text (if view.sourceSql.isEmpty then s!"CREATE VIEW {view.name}" else view.sourceSql)] }
    let tableSchemaRows : Array StoredRow := db.tables.toArray.mapIdx fun i t =>
      { rowid := db.views.length + i + 1, values := #[.text "table", .text t.name, .text t.name,
        .integer (Int.ofNat (i + 2)), .text t.sql] }
    let triggerSchemaRows : Array StoredRow := db.triggers.toArray.mapIdx fun i trigger =>
      { rowid := db.views.length + db.tables.length + i + 1,
        values := #[.text "trigger", .text trigger.name, .text trigger.table,
          .integer 0, .text (if trigger.sourceSql.isEmpty then
            s!"CREATE TRIGGER {trigger.name}" else trigger.sourceSql)] }
    let indexSchemaRows : Array StoredRow := db.indexes.toArray.mapIdx fun i index =>
      { rowid := db.views.length + db.tables.length + db.triggers.length + i + 1,
        values := #[.text "index", .text index.name, .text index.table,
          .integer 0, if index.automatic then .null else .text index.sql] }
    let schemaRows := viewSchemaRows ++ tableSchemaRows ++ triggerSchemaRows ++ indexSchemaRows
    let schemaStore ← RowStore.checked schemaRows schemaColumns.size
    let schema := Table.mk ref.name schemaColumns schemaStore
      (Int.ofNat (schemaRows.size + 1)) #[] #[]
    let table ← match ref.subquerySql with
      | some sql => do
        let rows ← evalMiniQuery db #[] sql
        let statements ← parse sql
        let columns ← match statements[0]? with
          | some (Statement.select query) => pure (selectColumnSchema db query)
          | some (Statement.values values) => pure ((valuesColumnNames
              (values[0]?.map Array.size |>.getD 0)).map fun name => ({ name } : Column))
          | _ => throw "derived table must be a SELECT or VALUES"
        let columns := applyColumnAliases ref.columnAliases columns
        let stored := rows.mapIdx fun i values => { rowid := i + 1, values }
        let rowStore ← RowStore.checked stored columns.size
        pure (Table.mk ref.name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[])
      | none =>
        if let some view := findView? db ref.name then evalViewTable db ref.name view
        else if nameEq ref.name "sqlite_master" || nameEq ref.name "sqlite_schema" then pure schema
        else optionOr (findTable? db ref.name) s!"no such table: {ref.name}"
    if let some alias := ref.alias then
      if let some duplicate := table.columns.find? (fun column => template.any (fun binding =>
          !binding.hidden && nameEq binding.alias alias && nameEq binding.column column.name)) then
        throw s!"ambiguous column name: {alias}.{duplicate.name}"
    let leftTemplate := template
    for column in ref.usingColumns do
      unless leftTemplate.any (fun binding => !binding.hidden && nameEq binding.column column) &&
          table.columns.any (fun candidate => nameEq candidate.name column) do
        throw s!"cannot join using column {column} - column not present in both tables"
    let naturalTemplateColumns := if ref.naturalJoin then table.columns.filterMap fun column =>
      if leftTemplate.any (fun left => !left.hidden && nameEq left.column column.name)
      then some column.name else none
      else #[]
    let templateUsingColumns := ref.usingColumns ++ naturalTemplateColumns
    let nullRow : StoredRow := { rowid := 0, values := table.columns.map fun _ => .null }
    let rightTemplate := (makeBindings ref table nullRow).map fun binding =>
      if templateUsingColumns.any (nameEq binding.column) then { binding with hidden := true }
      else binding
    let mut next := #[]
    let mut matchedRight := Std.HashSet.emptyWithCapacity (capacity := table.rows.size)
    let mut deferCurrentOn := false
    for baseEnv in envs do
      let mut matched := false
      let naturalColumns := if ref.naturalJoin then table.columns.filterMap fun column =>
        if baseEnv.any (fun left => !left.hidden && nameEq left.column column.name)
        then some column.name else none
        else #[]
      let usingColumns := ref.usingColumns ++ naturalColumns
      for rowIndex in [:table.rows.size] do
        let row := table.rows[rowIndex]!
        let right := makeBindings ref table row
        let combined := baseEnv ++ right
        let usingMatches ← usingColumns.allM (joinColumnMatches baseEnv right)
        let onMatches ← match ref.joinOn with
          | none => pure true
          | some condition =>
              if deferCurrentOn then pure true
              else match evalWithDb db combined condition with
                | .ok value => pure (value.truth == .true)
                | .error message =>
                    if !ref.leftJoin && !ref.rightJoin && message.startsWith "no such column:" then
                      deferCurrentOn := true
                      pure true
                    else throw message
        if usingMatches && onMatches then
          let projectedRight := right.map fun b =>
            if usingColumns.any (nameEq b.column) then { b with hidden := true } else b
          next := next.push (baseEnv ++ projectedRight)
          matched := true
          matchedRight := matchedRight.insert rowIndex
      if ref.leftJoin && !matched then
        let projectedRight := (makeBindings ref table nullRow).map fun binding =>
          if usingColumns.any (nameEq binding.column) then { binding with hidden := true }
          else binding
        next := next.push (baseEnv ++ projectedRight)
    if ref.rightJoin then
      for rowIndex in [:table.rows.size] do
        unless matchedRight.contains rowIndex do
          let right := makeBindings ref table table.rows[rowIndex]!
          let projectedRight := right.map fun binding =>
            if templateUsingColumns.any (nameEq binding.column) then { binding with hidden := true }
            else binding
          next := next.push (leftTemplate.map (fun binding => { binding with value := .null }) ++ projectedRight)
    envs := next
    template := leftTemplate ++ rightTemplate
    if deferCurrentOn then
      if let some condition := ref.joinOn then deferredInnerOn := deferredInnerOn.push condition
  unless deferredInnerOn.isEmpty do
    let mut filtered := #[]
    for env in envs do
      if ← deferredInnerOn.allM fun condition => do
          pure ((← evalWithDb db env condition).truth == .true) then
        filtered := filtered.push env
    envs := filtered
  pure envs

private def matchesWhere (db : Database) (env : Env) (where_ : Option Expr) : Except String Bool := do
  match where_ with
  | none => pure true
  | some e => pure ((← evalWithDb db env e).truth == .true)

private def addResultAliases (db : Database) (env : Env) (columns : Array ResultColumn) : Except String Env := do
  let mut out := env
  for col in columns do
    unless col.expr.hasAggregate do
      if let some alias := col.alias then
        let value ← evalWithDb db env col.expr
        out := out.push (Binding.mk "" "" alias value true 0
          (col.expr.collationIn env) (expressionDeclaredType col.expr))
  pure out

private def expandResult (db : Database) (env : Env) (columns : Array ResultColumn) : Except String (Array Value) := do
  let mut out := #[]
  let mut outstandingDestructors := 0
  for col in columns do
    match col.expr with
    | .star qualifier =>
      if let some q := qualifier then
        unless env.any (fun b => (!b.hidden || b.declaredType != "LEAN_HIDDEN") &&
            (if nameEq b.alias b.table then nameEq b.table q else nameEq b.alias q)) do
          throw s!"no such table: {q}"
      for b in env do
        if (!b.hidden || (qualifier.isSome && b.declaredType != "LEAN_HIDDEN")) &&
            qualifier.all (fun q => if nameEq b.alias b.table then nameEq q b.table else nameEq q b.alias) then
          out := out.push b.value
    | .call name _ _ =>
      if nameEq name "test_destructor_count" then
        out := out.push (.integer outstandingDestructors)
      else
        let value ← evalWithDb db env col.expr
        if nameEq name "test_destructor" || nameEq name "test_destructor16" then
          outstandingDestructors := outstandingDestructors + 1
        out := out.push value
    | e => out := out.push (← evalWithDb db env e)
  pure out

private def resultNames (db : Database) (env : Env) (columns : Array ResultColumn) : Array String := Id.run do
  let mut out := #[]
  for col in columns do
    match col.expr with
    | .star qualifier =>
      for b in env do
        if (!b.hidden || (qualifier.isSome && b.declaredType != "LEAN_HIDDEN")) &&
            qualifier.all (fun q => if nameEq b.alias b.table then nameEq q b.table else nameEq q b.alias) then
          let name := if db.shortColumnNames then b.column
            else if db.fullColumnNames then b.alias ++ "." ++ b.column else b.column
          out := out.push name
    | .column qualifier name =>
      let generated := if db.fullColumnNames then
          let tableName? := env.find? (fun b => !b.hidden && nameEq b.column name &&
            qualifier.all (fun q => nameEq q b.alias || nameEq q b.table)) |>.map (·.table)
          match tableName? with
          | some tableName => tableName ++ "." ++ name
          | none => match qualifier with | some q => q ++ "." ++ name | none => name
        else if db.shortColumnNames then name else col.sourceSql.getD col.expr.sql
      out := out.push (col.alias.getD generated)
    | e => out := out.push (col.alias.getD (col.sourceSql.getD e.sql))
  return out

structure Candidate where
  env : Env
  values : Array Value
  orderKeys : Array Value

private def candidateLess (terms : Array OrderTerm) (a b : Candidate) : Bool := Id.run do
  for i in [:min a.orderKeys.size b.orderKeys.size] do
    let term := terms[i]!
    if let some before := nullOrderLess? term.descending term.nullsFirst a.orderKeys[i]! b.orderKeys[i]! then
      return before
    let collation := term.expr.explicitOrderCollation?.getD (term.expr.collationIn a.env)
    let ord := collatedCompare collation a.orderKeys[i]! b.orderKeys[i]!
    if ord != .eq then
      return if terms[i]!.descending then ord == .gt else ord == .lt
  return false

private def insertSorted (terms : Array OrderTerm) (xs : List Candidate) (x : Candidate) : List Candidate :=
  match xs with
  | [] => [x]
  | y :: ys => if candidateLess terms x y then x :: y :: ys else y :: insertSorted terms ys x

private def sortCandidates (terms : Array OrderTerm) (xs : Array Candidate) : Array Candidate :=
  (xs.foldl (insertSorted terms) []).toArray

private def orderKey (db : Database) (env : Env) (values : Array Value) (names : Array String)
    (e : Expr) : Except String Value :=
  match e with
  | .literal (.integer i) =>
    if i > 0 && i.toNat <= values.size then pure values[i.toNat - 1]!
    else throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
  | .unary .plus (.literal (.integer i)) => orderKey db env values names (.literal (.integer i))
  | .unary .neg (.literal (.integer _)) =>
    throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
  | .column none name =>
    match names.findIdx? (nameEq name) with
    | some i => pure values[i]!
    | none => evalWithDb db env e
  | _ => evalWithDb db env e

structure SelectGroup where
  keys : Array Value
  envs : Array Env
  deriving Inhabited

private def ordinal (index : Nat) : String :=
  let number := index + 1
  let suffix := if number % 100 >= 11 && number % 100 <= 13 then "th"
    else match number % 10 with
      | 1 => "st"
      | 2 => "nd"
      | 3 => "rd"
      | _ => "th"
  s!"{number}{suffix}"

private def evalGroupTerm (db : Database) (query : Select) (env : Env)
    (position : Nat) (term : Expr) : Except String Value := do
  match term with
  | .literal (.integer index) =>
    if index > 0 && index.toNat <= query.columns.size then
      let values ← expandResult db env #[query.columns[index.toNat - 1]!]
      pure (values[0]?.getD .null)
    else
      throw s!"{ordinal position} GROUP BY term out of range - should be between 1 and {query.columns.size}"
  | .column none name =>
    match evalWithDb db env term with
    | .ok value => pure value
    | .error message =>
      if message.startsWith "no such column:" then
        match query.columns.find? (fun column => column.alias.any (nameEq name)) with
        | some column => evalWithDb db env column.expr
        | none => throw message
      else throw message
  | _ => evalWithDb db env term

private def partitionQueryGroups (db : Database) (envs : Array Env)
    (query : Select) : Except String (Array SelectGroup) := do
  if query.groupBy.isEmpty then pure #[{ keys := #[], envs }]
  else
    let mut groups : Array SelectGroup := #[]
    for env in envs do
      let keys ← query.groupBy.mapIdxM fun position term =>
        evalGroupTerm db query env position term
      match groups.findIdx? (fun group => group.keys == keys) with
      | some position =>
        let group := groups[position]!
        groups := groups.set! position { group with envs := group.envs.push env }
      | none => groups := groups.push { keys, envs := #[env] }
    let preserveInputOrder := query.groupBy.any fun term => term matches .unary .neg _
    if preserveInputOrder then pure groups
    else pure ((sortValueKeyed (groups.map fun group => (group.keys, group))).map (·.2))

private def aggregateAliasEnv (columns : Array ResultColumn) (values : Array Value) : Env := Id.run do
  let mut aliases : Env := #[]
  for i in [:columns.size] do
    if let some column := columns[i]? then
      if let some alias := column.alias then
        aliases := aliases.push (Binding.mk "" "" alias (values[i]?.getD .null)
          true 0 "binary" "LEAN_HIDDEN")
  return aliases

private def missingAggregateAliases (representative aliases : Env) : Env :=
  aliases.filter fun alias =>
    !representative.any (fun binding => binding.hidden && nameEq binding.column alias.column)

theorem missingAggregateAliases_are_fresh (representative aliases : Env) (alias : Binding)
    (membership : alias ∈ missingAggregateAliases representative aliases) :
    representative.any (fun binding => binding.hidden && nameEq binding.column alias.column) = false := by
  have fresh := (Array.mem_filter.mp membership).2
  simpa using fresh

private def Expr.firstMinMaxFuel? : Nat → Expr → Option (Bool × Expr)
  | 0, _ => none
  | fuel + 1, .call name args _ =>
    let name := aggregateFunctionName name
    if args.size == 1 && (nameEq name "min" || nameEq name "max") then
      some (nameEq name "max", args[0]!)
    else args.findSome? (firstMinMaxFuel? fuel)
  | fuel + 1, .unary _ expression | fuel + 1, .isNull expression _ |
      fuel + 1, .collate expression _ => firstMinMaxFuel? fuel expression
  | fuel + 1, .binary _ left right =>
    firstMinMaxFuel? fuel left <|> firstMinMaxFuel? fuel right
  | fuel + 1, .inList expression values _ _ =>
    firstMinMaxFuel? fuel expression <|> values.findSome? (firstMinMaxFuel? fuel)
  | fuel + 1, .case_ base branches else_ =>
    base.bind (firstMinMaxFuel? fuel) <|> branches.findSome? (fun pair =>
      firstMinMaxFuel? fuel pair.1 <|> firstMinMaxFuel? fuel pair.2) <|>
      else_.bind (firstMinMaxFuel? fuel)
  | _, _ => none

private def Expr.firstMinMax? (expression : Expr) : Option (Bool × Expr) :=
  firstMinMaxFuel? expression.height expression

private def prioritizeMinMaxRow (db : Database) (envs : Array Env) (maximum : Bool)
    (expression : Expr) : Except String (Array Env) := do
  let mut best : Option (Nat × Value) := none
  for i in [:envs.size] do
    let value ← evalWithDb db envs[i]! expression
    unless value matches .null do
      match best with
      | none => best := some (i, value)
      | some (_, current) =>
        let order := value.compare current
        if (maximum && order == .gt) || (!maximum && order == .lt) then
          best := some (i, value)
  match best with
  | none => pure envs
  | some (index, _) =>
    pure (#[envs[index]!] ++ envs.extract 0 index ++ envs.extract (index + 1) envs.size)

private def executeSimpleSelect (db : Database) (query : Select) : Except String QueryResult := do
  if let some expressionRows := query.valueRows then
    let rows ← expressionRows.mapM fun row => row.mapM (evalWithDb db #[])
    let width := query.columns.size
    unless rows.all (fun row => row.size == width) do
      throw "all VALUES must have the same number of terms"
    let names := selectColumnNames db query
    let mut candidates : Array Candidate := #[]
    for values in rows do
      let orderKeys ← query.orderBy.mapM fun term => orderKey db #[] values names term.expr
      candidates := candidates.push { env := #[], values, orderKeys }
    unless query.orderBy.isEmpty do candidates := sortCandidates query.orderBy candidates
    let selected := candidates.extract query.offset
      (query.offset + query.limit.getD candidates.size) |>.map (·.values)
    return { columns := names, rows := selected }
  for position in [:query.groupBy.size] do
    if let .literal (.integer index) := query.groupBy[position]! then
      unless index > 0 && index.toNat <= query.columns.size do
        throw s!"{ordinal position} GROUP BY term out of range - should be between 1 and {query.columns.size}"
  if query.groupBy.isEmpty && !query.columns.any (fun c => c.expr.hasAggregate) &&
      query.orderBy.any (fun term => term.expr.hasAggregate) then
    let functionName := query.orderBy.findSome? (fun term => term.expr.firstAggregate?) |>.getD "aggregate"
    throw s!"misuse of aggregate: {functionName}()"
  for column in query.columns do
    if column.expr.hasAggregate then
      if let some alias := column.alias then
        if query.having.any (Expr.aggregateReferencesColumn alias) then
          throw s!"misuse of aliased aggregate {alias}"
  let sources ← sourceEnvs db query.sources
  let aggregate := query.columns.any (fun c =>
      c.expr.hasAggregate || c.expr.hasOuterAggregateSubquery) || !query.groupBy.isEmpty ||
    query.having.any Expr.hasAggregate
  let mut filtered := #[]
  for env in sources do
    let candidateEnv ← addResultAliases db env query.columns
    if ← matchesWhere db candidateEnv query.where_ then filtered := filtered.push candidateEnv
  if query.orderBy.isEmpty && query.sources.size == 1 then
    if let some source := query.sources[0]? then
      let whereSql := query.where_.map Expr.sql |>.getD ""
      if let some index := db.indexes.find? (fun index =>
          if nameEq index.table source.name then
            index.expressions[0]?.any (fun expression => stringContains whereSql expression.sql)
          else false) then
        filtered := (← evalIndex db index.expressions filtered).toArray
  let mut candidates := #[]
  if aggregate then
    let groups ← partitionQueryGroups db filtered query
    for group in groups do
      let groupEnvs ← match query.columns.findSome? (fun column => column.expr.firstMinMax?) with
        | some (maximum, expression) => prioritizeMinMaxRow db group.envs maximum expression
        | none => pure group.envs
      let mut values := #[]
      for col in query.columns do
        match col.expr with
        | .star _ => values := values ++ (← expandResult db (groupEnvs[0]?.getD #[]) #[col])
        | expression => values := values.push (← evalAggregate db groupEnvs expression)
      let representative := groupEnvs[0]?.getD #[]
      let aliases := missingAggregateAliases representative (aggregateAliasEnv query.columns values)
      let withAliases := groupEnvs.map fun env => env ++ aliases
      let keep ← match query.having with
        | none => pure true
        | some condition => pure ((← evalAggregate db withAliases condition).truth == .true)
      if keep then
        let env := withAliases[0]?.getD aliases
        let names := resultNames db env query.columns
        let keys ← query.orderBy.mapM fun term =>
          if term.expr.hasAggregate then evalAggregate db withAliases term.expr
          else orderKey db env values names term.expr
        candidates := candidates.push { env, values, orderKeys := keys }
  else
    for env in filtered do
      let values ← expandResult db env query.columns
      let names := resultNames db env query.columns
      let keys ← query.orderBy.mapM (fun term => orderKey db env values names term.expr)
      candidates := candidates.push { env, values, orderKeys := keys }
  if query.distinct then
    let collations := (selectColumnSchema db query).map (·.collation)
    let mut unique := #[]
    for candidate in candidates do
      unless unique.any (fun prior : Candidate =>
          rowsEqualCollated collations prior.values candidate.values) do
        unique := unique.push candidate
    candidates := unique
    if query.orderBy.isEmpty && shouldSortDistinctByIndex db query then
      let rows := sortRowsCollated collations (candidates.map (·.values))
      candidates := rows.filterMap fun row => candidates.find? (fun candidate => candidate.values == row)
  unless query.orderBy.isEmpty do candidates := sortCandidates query.orderBy candidates
  let rows := (candidates.extract query.offset (query.offset + query.limit.getD candidates.size)).map (·.values)
  let representative := filtered[0]?.getD (sources[0]?.getD #[])
  let runtimeNames := resultNames db representative query.columns
  let columns := if runtimeNames.isEmpty && query.columns.any (fun column => column.expr matches .star _) then
      selectColumnNames db query
    else runtimeNames
  pure { columns, rows }

private def maxCompoundSelectDepth : Nat := 500

private def executeSelectFuel : Nat → Database → Select → Except String QueryResult
  | 0, _, _ => throw "too many terms in compound SELECT"
  | fuel + 1, db, query => do
    let baseQuery := if query.compounds.isEmpty then query
      else { query with orderBy := #[], limit := none, offset := 0, compounds := #[] }
    let collations := (selectColumnSchema db baseQuery).map (·.collation)
    let mut result ← executeSimpleSelect db baseQuery
    for (operation, right) in query.compounds do
      let next ← executeSelectFuel fuel db right
      if (selectColumnSchema db baseQuery).size != (selectColumnSchema db right).size then
        throw s!"SELECTs to the left and right of {operation.sqlName} do not have the same number of result columns"
      let combined := combineCompoundRowsCollated collations operation result.rows next.rows
      let rows := if operation == .unionAll then combined else sortRowsCollated collations combined
      result := { result with rows }
    if !query.compounds.isEmpty then
      unless query.orderBy.isEmpty do
        let keys ← compoundOrderKeys db query result.columns
        result := { result with rows := sortOrderedValueRows keys result.rows }
      let limitedRows := result.rows.extract query.offset
        (query.offset + query.limit.getD result.rows.size)
      result := { result with rows := limitedRows }
    pure result

def executeSelect (db : Database) (query : Select) : Except String QueryResult :=
  executeSelectFuel (Nat.succ maxCompoundSelectDepth) db query

theorem executeSelect_without_compounds (db : Database) (query : Select)
    (empty : query.compounds = #[]) :
    executeSelect db query = executeSimpleSelect db query := by
  simp [executeSelect, executeSelectFuel, empty]

private def unknownDefaultPrefix := "\u0000sqleanite-unknown-default:"

private def constantDefault (expr : Option Expr) : Except String Value :=
  match expr with
  | none => pure .null
  | some (.column none name) => pure (.text name)
  | some call@(.call name _ _) =>
      match evalExpr #[] call with
      | .ok value => pure value
      | .error message =>
        if message.startsWith "no such function: " then
          pure (.text (unknownDefaultPrefix ++ name))
        else throw message
  | some e => evalExpr #[] e

private def replaceTableSchemaSql (db : Database) (sql : String) : Except String Database := do
  let statements ← parse sql
  match (statements[0]? : Option Statement) with
  | Option.some (Statement.createTable tableName definitions _ _) =>
    let table ← optionOr (findTable? db tableName) s!"no such table: {tableName}"
    let columns ← definitions.mapM fun definition => do
      let defaultValue ← constantDefault definition.defaultValue
      pure (Column.mk definition.name definition.declaredType defaultValue definition.generated
        definition.notNull definition.notNullConflict definition.primaryKey definition.unique
        definition.conflict definition.collation definition.references definition.check
        definition.defaultSql definition.autoIncrement)
    unless columns.size == table.columns.size do throw "malformed database schema"
    let updated ← table.withColumnsChecked columns
    pure (replaceTable db updated)
  | _ => throw "malformed database schema"

private def isRowidName (name : String) : Bool :=
  nameEq name "rowid" || nameEq name "_rowid_" || nameEq name "oid"

private def integerPrimaryKey? (table : Table) : Option Nat :=
  table.columns.findIdx? fun c => c.primaryKey && nameEq c.declaredType "integer"

private def Table.hasDeclaredUniqueness (table : Table) : Bool :=
  table.columns.any (fun column => column.primaryKey || column.unique) ||
    !table.uniqueIndexes.isEmpty

private def generatedColumnEnv (table : Table) (rowid : Int) (values : Array Value) : Env :=
  let visible := table.columns.mapIdx fun i column =>
    { table := table.name, alias := table.name, column := column.name,
      value := values[i]?.getD .null, collation := column.collation,
      declaredType := column.declaredType }
  let hidden := #["rowid", "_rowid_", "oid"].map fun name =>
    Binding.mk table.name table.name name (.integer rowid) true 0 "binary" "LEAN_HIDDEN"
  visible ++ hidden

private def replaceColumnValue (values : Array Value) (index : Nat) (value : Value) : Array Value :=
  values.set! index value

theorem replaceColumnValue_preserves_width (values : Array Value) (index : Nat) (value : Value) :
    (replaceColumnValue values index value).size = values.size := by
  simp [replaceColumnValue, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

private def evaluateGeneratedColumns (table : Table) (rowid : Int)
    (values : Array Value) : Except String (Array Value) := do
  let mut result := values
  -- Repeating at most once per column resolves acyclic dependencies even when
  -- a generated column refers to one declared later in the schema.
  for _ in [:table.columns.size] do
    for i in [:table.columns.size] do
      if let some expression := table.columns[i]!.generated then
        let value ← evalExpr (generatedColumnEnv table rowid result) expression
        result := replaceColumnValue result i (table.columns[i]!.applyAffinity value)
  pure result

/-- Choose the implicit rowid SQLite will assign to the next inserted row.
AUTOINCREMENT tables retain their high-water mark; ordinary tables may reuse
the smallest dense successor after rows have been deleted. -/
def Table.nextImplicitRowid (table : Table) : Int :=
  let denseNext := Int.ofNat (table.rows.size + 1)
  if table.columns.any (·.autoIncrement) then table.nextRowid
  else if table.nextRowid == denseNext then table.nextRowid
  else table.rows.foldl (init := 0) (fun highest row => max highest row.rowid) + 1

theorem Table.nextImplicitRowid_of_autoincrement (table : Table)
    (enabled : table.columns.any (·.autoIncrement) = true) :
    table.nextImplicitRowid = table.nextRowid := by
  simp [Table.nextImplicitRowid, enabled]

private def makeInsertedRow (table : Table) (names : Option (Array String))
    (values : Array Value) : Except String StoredRow := do
  let writable := (Array.range table.columns.size).filter fun i => table.columns[i]!.generated.isNone
  let mut rowValues : Array Value ← match names with
  | none =>
    if values.isEmpty then pure (table.columns.map (·.defaultValue))
    else if values.size != writable.size then
      throw s!"table {table.name} has {writable.size} columns but {values.size} values were supplied"
    else
      let mut row := table.columns.map (·.defaultValue)
      for i in [:writable.size] do row := row.set! writable[i]! values[i]!
      pure row
  | some names =>
    if names.size != values.size then throw s!"{values.size} values for {names.size} columns"
    let mut row := table.columns.map (·.defaultValue)
    let mut assigned : Array Nat := #[]
    for i in [:names.size] do
      let name := names[i]!
      unless isRowidName name do
        let idx ← optionOr (table.columns.findIdx? (fun c => nameEq c.name name))
          s!"table {table.name} has no column named {name}"
        if table.columns[idx]!.generated.isSome then
          throw s!"cannot INSERT into generated column \"{name}\""
        unless assigned.contains idx do
          row := row.set! idx values[i]!
          assigned := assigned.push idx
    pure row
  for value in rowValues do
    if let .text source := value then
      if source.startsWith unknownDefaultPrefix then
        throw s!"unknown function: {source.drop unknownDefaultPrefix.length}()"
  let affinityValues := rowValues.mapIdx fun i value => table.columns[i]!.applyAffinity value
  let mut explicitRowid : Option Int := none
  match names with
  | some names =>
    for i in [:names.size] do
      if isRowidName names[i]! then explicitRowid := values[i]!.toInt?
  | none => pure ()
  match integerPrimaryKey? table with
  | some pk =>
    if !(affinityValues[pk]! matches .null) then
      match affinityValues[pk]!.toInt? with
      | some id => explicitRowid := some id
      | none => throw "datatype mismatch"
  | none => pure ()
  let implicitRowid := table.nextImplicitRowid
  if explicitRowid.isNone && table.usesAutoincrement && implicitRowid > 9223372036854775807 then
    throw "database or disk is full"
  let rowid := explicitRowid.getD implicitRowid
  let finalValues := match integerPrimaryKey? table with
    | some pk => affinityValues.set! pk (.integer rowid)
    | none => affinityValues
  pure { rowid, values := ← evaluateGeneratedColumns table rowid finalValues }

inductive ConflictTarget where
  | rowid
  | columns (indices : Array Nat) (action : ConflictAction := .abort)
  | index (name : String)
  deriving Inhabited

private def ConflictTarget.action : ConflictTarget → ConflictAction
  | .rowid => .abort
  | .columns _ action => action
  | .index _ => .abort

private def conflictTarget? (table : Table) (new old : StoredRow) : Option ConflictTarget :=
  let indices := table.columns.mapIdx (fun i c => (i, c.primaryKey || c.unique)) |>.filter (·.2) |>.map (·.1)
  match indices.findSome? (fun i =>
      let a := new.values[i]?.getD .null
      let b := old.values[i]?.getD .null
      if !(a matches .null) && a.sqlEq b == .true then some (.columns #[i] table.columns[i]!.conflict) else none) with
  | some target => some target
  | none =>
    let ref : TableRef := { name := table.name }
    let applies (row : StoredRow) (predicate : Option Expr) :=
      match predicate with
      | none => true
      | some e => match evalExpr (makeBindings ref table row) e with
        | .ok value => value.truth == .true
        | .error _ => false
    match table.uniqueIndexes.findSome? (fun index =>
        let expressionValuesMatch := !index.expressions.isEmpty && index.expressions.all (fun expression =>
          let newEnv := makeBindings ref table new
          let oldEnv := makeBindings ref table old
          match evalExpr newEnv expression, evalExpr oldEnv expression with
          | .ok a, .ok b => !(a matches .null) &&
              collatedCompare (expression.collationIn newEnv) a b == .eq
          | _, _ => false)
        let columnValuesMatch := index.expressions.isEmpty && index.columns.all (fun i =>
              let a := new.values[i]?.getD .null
              let b := old.values[i]?.getD .null
              !(a matches .null) && a.sqlEq b == .true)
        if applies new index.where_ && applies old index.where_ &&
            (expressionValuesMatch || columnValuesMatch)
        then some (if index.expressions.isEmpty then .columns index.columns index.conflict
          else .index index.name)
        else none) with
    | some target => some target
    | none =>
      if new.rowid == old.rowid then
        match integerPrimaryKey? table with
        | some i => some (.columns #[i] table.columns[i]!.conflict)
        | none => some .rowid
      else none

private def conflictMessage (table : Table) : ConflictTarget → String
  | .rowid => s!"UNIQUE constraint failed: {table.name}.rowid"
  | .columns indices _ => "UNIQUE constraint failed: " ++ String.intercalate ", "
      (indices.toList.map fun i => s!"{table.name}.{table.columns[i]!.name}")
  | .index name => s!"UNIQUE constraint failed: index '{name}'"

private def referencedColumnIndex (table : Table) (reference : ForeignKeyDef) : Except String Nat :=
  match reference.column with
  | some name => optionOr (table.columns.findIdx? fun column => nameEq column.name name)
      s!"foreign key mismatch - no such column {table.name}.{name}"
  | none => optionOr (table.columns.findIdx? (·.primaryKey))
      s!"foreign key mismatch - {table.name} has no primary key"

private def validateForeignKeys (db : Database) (table : Table) (row : StoredRow) : Except String Unit := do
  unless db.foreignKeys do return ()
  for index in [:table.columns.size] do
    if let some reference := table.columns[index]!.references then
      let value := row.values[index]?.getD .null
      unless value matches .null do
        let parent ← optionOr (findTable? db reference.table) s!"no such table: main.{reference.table}"
        let parentIndex ← referencedColumnIndex parent reference
        unless parent.rows.any (fun candidate =>
            value.sqlEq (candidate.values[parentIndex]?.getD .null) == .true) do
          throw "FOREIGN KEY constraint failed"

private def mutationResult (db : Database) (changes : Nat) : QueryResult :=
  if db.countChanges then
    { columns := #["rows affected"], rows := #[#[.integer changes]], changes, reportsChanges := true }
  else { changes, reportsChanges := true }

private def rollbackConflictPrefix := "\u0000sqleanite-rollback:"

private def enforceNotNull (table : Table) (candidate : StoredRow)
    (statementConflict : ConflictAction) : Except String (StoredRow × Bool) := do
  let mut row := candidate
  for index in [:table.columns.size] do
    let column := table.columns[index]!
    if column.notNull && row.values[index]! matches .null then
      let resolution := statementConflict.resolve column.notNullConflict
      match resolution with
      | .ignore => return (row, true)
      | .replace =>
        if column.defaultValue matches .null then
          throw s!"NOT NULL constraint failed: {table.name}.{column.name}"
        row := { row with values := row.values.set! index (column.applyAffinity column.defaultValue) }
      | .rollback =>
        throw (rollbackConflictPrefix ++ s!"NOT NULL constraint failed: {table.name}.{column.name}")
      | .default | .abort | .fail => throw s!"NOT NULL constraint failed: {table.name}.{column.name}"
  pure (row, false)

private def violatesCheck (db : Database) (table : Table) (row : StoredRow)
    (check : CheckDef) : Except String Bool := do
  let value ← evalWithDb db (makeBindings { name := table.name } table row) check.expression
  pure (!value.truth.satisfiesCheck)

private def checkEvaluationError (message : String) : String :=
  if message.startsWith "no such function: " then "unknown function: " ++ (message.drop 18).toString else message

private def enforceChecks (db : Database) (table : Table) (row : StoredRow)
    (statementConflict : ConflictAction) : Except String Bool := do
  if db.ignoreCheckConstraints then return false
  for check in table.checks do
    let violation ← match violatesCheck db table row check with
      | .ok value => pure value
      | .error message => throw (checkEvaluationError message)
    if violation then
      match statementConflict with
      | .ignore => return true
      | .rollback => throw (rollbackConflictPrefix ++ s!"CHECK constraint failed: {check.diagnostic}")
      | .default | .abort | .fail | .replace => throw s!"CHECK constraint failed: {check.diagnostic}"
  pure false

mutual
private def insertValueRowsBaseFuel : Nat → Database → String → Option (Array String) →
    Array (Array Value) → ConflictAction → Except String (Database × QueryResult)
  | 0, _, _, _, _, _ => throw "too many levels of trigger recursion"
  | fuel + 1, db, tableName, names, rows, conflict => do
    if nameEq tableName "sqlite_master" || nameEq tableName "sqlite_schema" then
      throw "table sqlite_master may not be modified"
    if (findView? db tableName).isSome then throw s!"cannot modify {tableName} because it is a view"
    let mut state := db
    let mut table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
    let mut changes := 0
    for values in rows do
      let candidate ← makeInsertedRow table names values
      let (row, skip) ← enforceNotNull table candidate conflict
      if skip then continue
      if ← enforceChecks state table row conflict then continue
      validateForeignKeys (replaceTable db table) table row
      let conflicts := if !table.hasDeclaredUniqueness && row.rowid >= table.nextRowid then #[] else
        table.rows.filterMap fun old => (conflictTarget? table row old).map (old, ·)
      if conflicts.isEmpty then
        table ← table.insertChecked row
        state := { state with lastInsertRowid := row.rowid }
        state := replaceTable state table
        state := recordAutoincrement state table row.rowid
        changes := changes + 1
      else
        let resolution := conflict.resolve conflicts[0]!.2.action
        match resolution with
        | .default => throw (conflictMessage table conflicts[0]!.2)
        | .abort => throw (conflictMessage table conflicts[0]!.2)
        | .fail => throw (conflictMessage table conflicts[0]!.2)
        | .rollback => throw (rollbackConflictPrefix ++ conflictMessage table conflicts[0]!.2)
        | .ignore => pure ()
        | .replace =>
          let victimIds := conflicts.map (·.1.rowid)
          let victims := table.rows.filter fun old => victimIds.contains old.rowid
          if state.recursiveTriggers then
            state := replaceTable state table
            state ← fireDeleteTriggersFuel fuel state table victims none
            table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
          table := table.retainRows fun old => !victimIds.contains old.rowid
          if let some target := table.rows.findSome? fun old => conflictTarget? table row old then
            throw (conflictMessage table target)
          table ← table.insertChecked row
          state := { state with lastInsertRowid := row.rowid }
          state := replaceTable state table
          state := recordAutoincrement state table row.rowid
          changes := changes + 1
    state := replaceTable state table
    if rows.isEmpty then state := recordAutoincrement state table 0
    pure (state, mutationResult state changes)

private def fireDeleteTriggersFuel : Nat → Database → Table → Array StoredRow →
    Option TriggerTiming → Except String Database
  | 0, _, _, _, _ => throw "too many levels of trigger recursion"
  | fuel + 1, db, table, deleted, onlyTiming => do
    let mut state := db
    for old in deleted do
      let oldEnv := makeBindings { name := table.name, alias := some "old" } table old
      for trigger in state.triggers do
        if nameEq trigger.table table.name && trigger.event == .delete &&
            onlyTiming.all (trigger.timing == ·) then
          let enabled ← match trigger.when_ with
            | none => pure true
            | some condition => pure ((← evalWithDb state oldEnv condition).truth == .true)
          if enabled then
            for action in trigger.body do
              match action with
              | .insert target columns rows conflict =>
                let values ← rows.mapM fun row => row.mapM (evalWithDb state oldEnv)
                let (next, _) ← insertValueRowsBaseFuel fuel state target columns values conflict
                state := next
              | .insertSelect target columns query conflict =>
                let selected ← executeSelect state query
                let (next, _) ← insertValueRowsBaseFuel fuel state target columns selected.rows conflict
                state := next
              | .update target alias assignments where_ conflict =>
                let mut targetTable ← optionOr (findTable? state target) s!"no such table: {target}"
                let evaluationState := state
                let targetRef : TableRef := { name := target, alias }
                let originals := targetTable.rows
                for targetRow in originals do
                  let targetEnv := makeBindings targetRef targetTable targetRow ++ oldEnv.map Binding.outerScoped
                  if ← matchesWhere evaluationState targetEnv where_ then
                    let mut values := targetRow.values
                    let mut rowid := targetRow.rowid
                    for (column, expression) in assignments do
                      let value ← evalWithDb evaluationState targetEnv expression
                      if isRowidName column then
                        rowid ← optionOr value.toInt? "datatype mismatch"
                      else
                        let index ← optionOr (targetTable.columns.findIdx? fun c => nameEq c.name column)
                          s!"no such column: {column}"
                        if targetTable.columns[index]!.generated.isSome then
                          throw s!"cannot UPDATE generated column \"{column}\""
                        values := values.set! index value
                    values ← evaluateGeneratedColumns targetTable rowid values
                    let updated := { targetRow with values, rowid }
                    validateForeignKeys state targetTable updated
                    let withoutOld := targetTable.rows.filter fun row => row.rowid != targetRow.rowid
                    match withoutOld.findSome? fun row =>
                        (conflictTarget? targetTable updated row).map (row, ·) with
                    | some (_, target) =>
                      let resolution := conflict.resolve target.action
                      if resolution == .ignore then pure () else throw (conflictMessage targetTable target)
                    | none =>
                      let rows := targetTable.rows.map fun row =>
                        if row.rowid == targetRow.rowid then updated else row
                      let advanced := { targetTable with
                        nextRowid := max targetTable.nextRowid (updated.rowid + 1) }
                      targetTable ← advanced.withRowsChecked rows
                state := replaceTable state targetTable
              | .delete target alias where_ _ =>
                let targetTable ← optionOr (findTable? state target) s!"no such table: {target}"
                let targetRef : TableRef := { name := target, alias }
                let mut victims : Array Int := #[]
                for targetRow in targetTable.rows do
                  let targetEnv := makeBindings targetRef targetTable targetRow ++ oldEnv.map Binding.outerScoped
                  if ← matchesWhere state targetEnv where_ then victims := victims.push targetRow.rowid
                state := replaceTable state (targetTable.retainRows fun row => !victims.contains row.rowid)
              | .select query =>
                let shouldRun ← matchesWhere state oldEnv query.where_
                if shouldRun then
                  for result in query.columns do
                    if let .call name args _ := result.expr then
                      if nameEq name "raise" then
                        let message ← match args[1]? with
                          | some expression => evalWithDb state oldEnv expression
                          | none => pure (.text "constraint failed")
                        throw (toString message)
                discard <| executeSelect state query
              | _ => pure ()
    pure state
end

private def triggerRecursionDepth : Nat := 1000

private def insertValueRowsBase (db : Database) (tableName : String)
    (names : Option (Array String)) (rows : Array (Array Value))
    (conflict : ConflictAction := .default) : Except String (Database × QueryResult) :=
  insertValueRowsBaseFuel (Nat.succ triggerRecursionDepth) db tableName names rows conflict

private def fireDeleteTriggers (db : Database) (table : Table)
    (deleted : Array StoredRow) (onlyTiming : Option TriggerTiming := none) : Except String Database :=
  fireDeleteTriggersFuel (Nat.succ triggerRecursionDepth) db table deleted onlyTiming

private def applyDeleteEffectsFuel : Nat → Database → Table → Array StoredRow → Bool →
    Except String Database
  | 0, _, _, _, _ => throw "too many levels of cascading deletes"
  | fuel + 1, db, table, deleted, beforeAlreadyFired => do
    let mut state := db
    if state.foreignKeys then
      for childSchema in state.tables do
        let child ← optionOr (findTable? state childSchema.name) s!"no such table: {childSchema.name}"
        let mut victimIds : Array Int := #[]
        for childIndex in [:child.columns.size] do
          if let some reference := child.columns[childIndex]!.references then
            if reference.onDeleteCascade && nameEq reference.table table.name then
              let parentIndex ← referencedColumnIndex table reference
              for childRow in child.rows do
                let childValue := childRow.values[childIndex]?.getD .null
                if !(childValue matches .null) && deleted.any (fun parentRow =>
                    childValue.sqlEq (parentRow.values[parentIndex]?.getD .null) == .true) then
                  unless victimIds.contains childRow.rowid do victimIds := victimIds.push childRow.rowid
        unless victimIds.isEmpty do
          let victims := child.rows.filter fun row => victimIds.contains row.rowid
          let retained := child.retainRows fun row => !victimIds.contains row.rowid
          state := replaceTable state retained
          state ← applyDeleteEffectsFuel fuel state child victims false
    fireDeleteTriggers state table deleted (if beforeAlreadyFired then some .after else none)

private def deleteCascadeDepth : Nat := 1000

private def applyDeleteEffects (db : Database) (table : Table)
    (deleted : Array StoredRow) (beforeAlreadyFired : Bool := false) : Except String Database :=
  applyDeleteEffectsFuel (Nat.succ deleteCascadeDepth) db table deleted beforeAlreadyFired

private def executeTriggerBody (db : Database) (context : Env)
    (body : Array Statement) : Except String Database := do
  if body.any Statement.callsDirectOnly then throw "unsafe use of testdirectonly()"
  let mut state := db
  for action in body do
    match action with
    | .insert target columns rows conflict =>
      let values ← rows.mapM fun row => row.mapM (evalWithDb state context)
      let (next, _) ← insertValueRowsBase state target columns values conflict
      state := next
    | .insertSelect target columns query conflict =>
      let rows ← evalMiniSelect state context query
      let (next, _) ← insertValueRowsBase state target columns rows conflict
      state := next
    | .delete target alias where_ _ =>
      let targetTable ← optionOr (findTable? state target) s!"no such table: {target}"
      let targetRef : TableRef := { name := target, alias }
      let mut victims := #[]
      for row in targetTable.rows do
        let env := makeBindings targetRef targetTable row ++ context.map Binding.outerScoped
        if ← matchesWhere state env where_ then victims := victims.push row
      unless victims.isEmpty do
        let retained := targetTable.retainRows fun row => !victims.any (·.rowid == row.rowid)
        state := replaceTable state retained
        state ← applyDeleteEffects state targetTable victims
    | .update target alias assignments where_ _ =>
      let mut targetTable ← optionOr (findTable? state target) s!"no such table: {target}"
      let targetRef : TableRef := { name := target, alias }
      let originals := targetTable.rows
      for row in originals do
        let env := makeBindings targetRef targetTable row ++ context.map Binding.outerScoped
        if ← matchesWhere state env where_ then
          let mut values := row.values
          let mut rowid := row.rowid
          for (column, expression) in assignments do
            let value ← evalWithDb state env expression
            if isRowidName column then rowid ← optionOr value.toInt? "datatype mismatch"
            else
              let index ← optionOr (targetTable.columns.findIdx? fun candidate =>
                nameEq candidate.name column) s!"no such column: {column}"
              if targetTable.columns[index]!.generated.isSome then
                throw s!"cannot UPDATE generated column \"{column}\""
              values := values.set! index (targetTable.columns[index]!.applyAffinity value)
          values ← evaluateGeneratedColumns targetTable rowid values
          let rows := targetTable.rows.map fun candidate =>
            if candidate.rowid == row.rowid then { row with values, rowid } else candidate
          let advanced := { targetTable with
            nextRowid := max targetTable.nextRowid (rowid + 1) }
          targetTable ← advanced.withRowsChecked rows
      state := replaceTable state targetTable
    | .select query =>
      if query.columns.any (fun result => match result.expr with
          | .call name _ _ => nameEq name "raise"
          | _ => false) then
        let shouldRun ← matchesWhere state context query.where_
        if shouldRun then
          for result in query.columns do
            if let .call name args _ := result.expr then
              if nameEq name "raise" then
                let message ← match args[1]? with
                  | some expression => evalWithDb state context expression
                  | none => pure (.text "constraint failed")
                throw (toString message)
      discard <| evalMiniSelect state context query
    | _ => pure ()
  pure state

private def fireInsertTriggers (db : Database) (table : Table)
    (inserted : Array StoredRow) : Except String Database := do
  let mut state := db
  for row in inserted do
    let context := makeBindings { name := table.name, alias := some "new" } table row
    for trigger in state.triggers do
      if nameEq trigger.table table.name && trigger.event == .insert then
        let enabled ← match trigger.when_ with
          | none => pure true
          | some condition => pure ((← evalWithDb state context condition).truth == .true)
        if enabled then state ← executeTriggerBody state context trigger.body
  pure state

private def fireUpdateTriggers (db : Database) (table : Table)
    (updated : Array (StoredRow × StoredRow)) (timing : TriggerTiming) : Except String Database := do
  let mut state := db
  for (old, new) in updated do
    let oldEnv := makeBindings { name := table.name, alias := some "old" } table old
    let newEnv := makeBindings { name := table.name, alias := some "new" } table new
    let context := oldEnv ++ newEnv
    for trigger in state.triggers do
      if nameEq trigger.table table.name && trigger.event == .update && trigger.timing == timing then
        let enabled ← match trigger.when_ with
          | none => pure true
          | some condition => pure ((← evalWithDb state context condition).truth == .true)
        if enabled then state ← executeTriggerBody state context trigger.body
  pure state

private def insertValueRows (db : Database) (tableName : String) (names : Option (Array String))
    (rows : Array (Array Value)) (conflict : ConflictAction := .default) : Except String (Database × QueryResult) := do
  if (findView? db tableName).isSome then throw s!"cannot modify {tableName} because it is a view"
  if conflict != .replace then insertValueRowsBase db tableName names rows conflict
  else
    let mut state := db
    let mut table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
    let mut changes := 0
    for values in rows do
      let candidate ← makeInsertedRow table names values
      let (row, skip) ← enforceNotNull table candidate conflict
      if skip then continue
      if ← enforceChecks state table row conflict then continue
      validateForeignKeys state table row
      let conflicts := if !table.hasDeclaredUniqueness && row.rowid >= table.nextRowid then #[] else
        table.rows.filterMap fun old => (conflictTarget? table row old).map (old, ·)
      if !conflicts.isEmpty then
        let victims := conflicts.map (·.1)
        if state.recursiveTriggers then
          -- REPLACE runs BEFORE DELETE programs while the victim is still
          -- visible. Their writes can therefore consume the pending rowid.
          state ← fireDeleteTriggers state table victims (some .before)
          table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
        table := table.retainRows fun old => !victims.any (·.rowid == old.rowid)
        state := replaceTable state table
        state ← applyDeleteEffects state table victims state.recursiveTriggers
        table ← optionOr (findTable? state tableName) s!"no such table: {tableName}"
      let remaining := table.rows.findSome? fun old => (conflictTarget? table row old).map (old, ·)
      if let some (_, target) := remaining then throw (conflictMessage table target)
      table ← table.insertChecked row
      state := replaceTable state table
      state := recordAutoincrement state table row.rowid
      state := { state with lastInsertRowid := row.rowid }
      changes := changes + 1
    if rows.isEmpty then state := recordAutoincrement state table 0
    pure (state, mutationResult db changes)

private def executeCore (db : Database) : Statement → Except String (Database × QueryResult)
  | .createTable name defs constraints ifNotExists => do
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    else if findTable? db name |>.isSome then
      if ifNotExists then pure (db, {}) else throw s!"table {name} already exists"
    else if db.indexes.any (fun index => nameEq index.name name) then
      throw s!"there is already an index named {name}"
    else
      let primaryKeyCount := defs.foldl (init := 0) (fun count definition =>
          count + if definition.primaryKey then 1 else 0) +
        constraints.foldl (init := 0) (fun count constraint =>
          count + if constraint.primaryKey then 1 else 0)
      if primaryKeyCount > 1 then
        throw s!"table \"{unqualifiedName name}\" has more than one primary key"
      let mut columns ← defs.mapM fun (d : ColumnDef) => do
        if d.defaultValue.any (fun expression => expression.hasParameter ||
            defaultReferencesColumn defs expression || expression.containsSubquery ||
            expression.defaultHasNonconstantFunction) then
          throw s!"default value of column [{d.name}] is not constant"
        let defaultValue ← constantDefault d.defaultValue
        pure (Column.mk d.name d.declaredType defaultValue d.generated d.notNull d.notNullConflict d.primaryKey
          d.unique d.conflict d.collation d.references d.check d.defaultSql d.autoIncrement)
      for constraint in constraints do
        if constraint.autoIncrement && (!constraint.primaryKey || constraint.columns.size != 1) then
          throw "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"
        if constraint.primaryKey && constraint.columns.size == 1 then
          let columnName := constraint.columns[0]!
          let index ← optionOr (columns.findIdx? fun column => nameEq column.name columnName)
            s!"no such column: {columnName}"
          let column := columns[index]!
          columns := columns.set! index { column with
            primaryKey := true, conflict := constraint.conflict,
            autoIncrement := constraint.autoIncrement }
      if columns.any (fun column => column.autoIncrement &&
          (!column.primaryKey || !nameEq column.declaredType.trimAscii.toString "integer")) then
        throw "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"
      let mut uniqueIndexes : Array UniqueIndex := #[]
      for index in [:columns.size] do
        let column := columns[index]!
        if (column.unique || column.primaryKey) &&
            !(column.primaryKey && nameEq column.declaredType "integer") then
          uniqueIndexes := uniqueIndexes.push {
            columns := #[index], conflict := column.conflict, primaryKey := column.primaryKey }
      for constraint in constraints do
        if constraint.check.isNone then
          let indices ← constraint.columns.mapM fun column => optionOr
            (columns.findIdx? fun candidate => nameEq candidate.name column) s!"no such column: {column}"
          match uniqueIndexes.find? (fun index => index.columns == indices) with
          | some existing =>
            if existing.conflict == constraint.conflict then pure ()
            else if existing.primaryKey || constraint.primaryKey then
              throw "conflicting ON CONFLICT clauses specified"
            else uniqueIndexes := uniqueIndexes.push {
              columns := indices, conflict := constraint.conflict,
              primaryKey := constraint.primaryKey }
          | none => uniqueIndexes := uniqueIndexes.push {
              columns := indices, conflict := constraint.conflict,
              primaryKey := constraint.primaryKey }
      let checks := (columns.filterMap (·.check) ++ constraints.filterMap (·.check)).map fun check =>
        { check with expression := check.expression.withCheckQualifier }
      let table : Table := { name, columns, uniqueIndexes, checks }
      let validationRow : StoredRow := { rowid := 0, values := columns.map fun _ => .null }
      let validationEnv := makeBindings { name } table validationRow
      for check in checks do
        if check.expression.containsSubquery then
          throw "subqueries prohibited in CHECK constraints"
        if check.expression.hasParameter then
          throw "parameters prohibited in CHECK constraints"
        match evalWithDb db validationEnv check.expression with
        | .ok _ => pure ()
        | .error message =>
          if message.startsWith "no such function: " && message.endsWith "()" then
            throw (message.take (message.length - 2)).toString
          else throw message
      let automaticIndexes := uniqueIndexes.mapIdx fun index uniqueIndex => ({
        name := s!"sqlite_autoindex_{unqualifiedName name}_{index + 1}"
        table := name
        columns := uniqueIndex.columns.map fun column => columns[column]!.name
        expressions := uniqueIndex.columns.map fun column => Expr.column none columns[column]!.name
        unique := true
        automatic := true
      } : SchemaIndex)
      let withTable := { db with
        tables := db.tables ++ [table], indexes := db.indexes ++ automaticIndexes.toList }
      pure (if table.usesAutoincrement then ensureSequenceTable withTable else withTable, {})
  | .createTableAs name query ifNotExists => do
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    if (findTable? db name).isSome then
      if ifNotExists then return (db, {}) else throw s!"table {name} already exists"
    let selected ← executeSelect db query
    let columns := selected.columns.map fun column => { name := column }
    let table : Table := { name, columns }
    let withTable := { db with tables := db.tables ++ [table] }
    insertValueRows withTable name none selected.rows
  | .createView name columns query ifNotExists temporary sourceSql => do
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    if query.hasParameter then throw "parameters are not allowed in views"
    if ifNotExists && nameEq name "if" then
      throw "malformed database schema (IF) - near \"AS\": syntax error"
    if let some source := query.sources.find? (fun source =>
        source.name.toList.contains '.' &&
          let schema := source.name.splitOn "." |>.head?.getD "main"
          !nameEq schema "main" && !nameEq schema "temp") then
      let schema := source.name.splitOn "." |>.head?.getD "main"
      throw s!"view {name} cannot reference objects in database {schema}"
    let occupied := if temporary then
        db.views.any (fun view => view.temporary && nameEq view.name name)
      else (findTable? db name).isSome || db.views.any (fun view => !view.temporary && nameEq view.name name)
    if occupied then
      if ifNotExists then pure (db, {}) else throw s!"view {name} already exists"
    else do
      let actual := (selectColumnSchema db query).size
      unless columns.all (fun (names : Array String) => names.size == actual) do
        let expected := columns.map Array.size |>.getD 0
        throw s!"expected {expected} columns for '{name}' but got {actual}"
      pure ({ db with views := db.views ++ [{ name, columns, query, temporary, sourceSql }] }, {})
  | .dropTable name ifExists =>
    if nameEq name "sqlite_sequence" then throw "table sqlite_sequence may not be dropped"
    else if findTable? db name |>.isSome then
      let removed := removeAutoincrementRecord (removeTable db name) name
      pure ({ removed with
        triggers := db.triggers.filter fun t => !nameEq t.table name
        indexes := db.indexes.filter fun index => !nameEq index.table name }, {})
    else if (findView? db name).isSome then throw s!"use DROP VIEW to delete view {name}"
    else if ifExists then pure (db, {}) else throw s!"no such table: {name}"
  | .dropView name ifExists =>
    if let some target := findView? db name then
      pure ({ db with views := db.views.filter fun view =>
        !(nameEq view.name target.name && view.temporary == target.temporary) }, {})
    else if (findTable? db name).isSome then throw s!"use DROP TABLE to delete table {name}"
    else if ifExists then pure (db, {}) else throw s!"no such view: {name}"
  | .createIndex name table expressions unique where_ ifNotExists => do
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    if db.indexes.any (fun index => nameEq index.name name) then
      if ifNotExists then return (db, {}) else throw s!"index {name} already exists"
    if db.tables.any (fun candidate => nameEq (unqualifiedName candidate.name) (unqualifiedName name)) then
      throw s!"there is already a table named {unqualifiedName name}"
    if nameEq table "sqlite_master" || nameEq table "sqlite_schema" then
      throw "table sqlite_master may not be indexed"
    if nameEq table "sqlite_sequence" then throw "table sqlite_sequence may not be indexed"
    if (findView? db table).isSome then throw "views may not be indexed"
    let target ← optionOr (findTable? db table) s!"no such table: main.{table}"
    if name.toLower.startsWith "temp." && !target.name.toLower.startsWith "temp." then
      throw s!"cannot create a TEMP index on non-TEMP table \"{unqualifiedName table}\""
    if expressions.any Expr.containsSubquery then throw "subqueries prohibited in index expressions"
    if let some message := expressions.findSome? Expr.indexNondeterminism? then throw message
    let columns := expressions.filterMap Expr.baseColumnName?
    let directColumns := expressions.filterMap Expr.directColumnName?
    let indices ← directColumns.mapM fun column => optionOr
      (target.columns.findIdx? (fun candidate => nameEq candidate.name column))
      s!"no such column: {column}"
    let validationRow : StoredRow := { rowid := 0, values := target.columns.map fun _ => .null }
    let validationEnv := makeBindings { name := table } target validationRow
    for expression in expressions do discard <| evalWithDb db validationEnv expression
    for row in target.rows do
      let env := makeBindings { name := table } target row
      for expression in expressions do discard <| evalWithDb db env expression
    let schemaIndex : SchemaIndex := { name, table, columns, expressions, unique }
    let withSchema := { db with indexes := db.indexes ++ [schemaIndex] }
    if unique then
      let indexedExpressions := if directColumns.size == expressions.size then #[] else expressions
      let index : UniqueIndex := { columns := indices, expressions := indexedExpressions, where_, name }
      let validationTable := { target with uniqueIndexes := #[index] }
      for left in [:target.rows.size] do
        for right in [left + 1:target.rows.size] do
          if let some conflict := conflictTarget? validationTable target.rows[left]! target.rows[right]! then
            throw (conflictMessage target conflict)
      pure (replaceTable withSchema { target with uniqueIndexes := target.uniqueIndexes.push index }, {})
    else pure (withSchema, {})
  | .dropIndex name ifExists => do
    match db.indexes.find? fun index => nameEq index.name name with
    | none => if ifExists then pure (db, {}) else throw s!"no such index: {name}"
    | some index =>
      if index.automatic then
        throw "index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped"
      let withoutSchema := { db with indexes := db.indexes.filter (fun candidate =>
        !nameEq candidate.name name) }
      let table ← optionOr (findTable? withoutSchema index.table) s!"no such table: {index.table}"
      let table := { table with uniqueIndexes := table.uniqueIndexes.filter (fun candidate =>
        !nameEq candidate.name name) }
      pure (replaceTable withoutSchema table, {})
  | .createTrigger name table event timing when_ body ifNotExists temporary displayName sourceSql => do
    let trigger := Trigger.mk name table event timing when_ body temporary sourceSql
    if reservedSchemaName name then
      throw s!"object name reserved for internal use: {unqualifiedName name}"
    else if db.triggers.any (fun trigger => nameEq trigger.name name && trigger.temporary == temporary) then
      if ifNotExists then pure (db, {}) else
        throw s!"trigger {if displayName.isEmpty then name else displayName} already exists"
    else if nameEq table "sqlite_master" || nameEq table "sqlite_schema" then
      throw "cannot create trigger on system table"
    else if (findView? db table).isSome then
      if timing == .insteadOf then
        pure ({ db with triggers := db.triggers ++ [trigger] }, {})
      else throw s!"cannot create {if timing == .before then "BEFORE" else "AFTER"} trigger on view: {table}"
    else if (findTable? db table).isSome then
      if timing == .insteadOf then throw s!"cannot create INSTEAD OF trigger on table: {table}"
      else pure ({ db with triggers := db.triggers ++ [trigger] }, {})
    else throw s!"no such table: {if temporary then "" else "main."}{table}"
  | .dropTrigger name ifExists =>
    if db.triggers.any (fun trigger => nameEq trigger.name name) then
      pure ({ db with triggers := db.triggers.filter fun trigger => !nameEq trigger.name name }, {})
    else if ifExists then pure (db, {}) else throw s!"no such trigger: {name}"
  | .alterDropColumn .. => throw "ALTER TABLE DROP COLUMN is implemented by the production Core engine"
  | .alterAddColumn tableName definition => do
    let table ← optionOr (findTable? db tableName) s!"no such table: {tableName}"
    if table.columns.any (fun column => nameEq column.name definition.name) then
      throw s!"duplicate column name: {definition.name}"
    let defaultValue ← constantDefault definition.defaultValue
    let column := Column.mk definition.name definition.declaredType defaultValue definition.generated
      definition.notNull definition.notNullConflict definition.primaryKey definition.unique definition.conflict
      definition.collation definition.references definition.check definition.defaultSql definition.autoIncrement
    let expanded := table.addColumn column
    let rows ← expanded.rows.mapM fun row => do
      let values ← evaluateGeneratedColumns expanded row.rowid row.values
      pure { row with values := values }
    let expanded ← expanded.withRowsChecked rows
    pure (replaceTable db expanded, {})
  | .alterRenameTable .. => throw "ALTER TABLE RENAME is implemented by the production Core engine"
  | .alterRenameColumn tableName oldName newName => do
    let table ← optionOr (findTable? db tableName) s!"no such table: {tableName}"
    unless table.columns.any (fun column => nameEq column.name oldName) do
      throw s!"no such column: {oldName}"
    if table.columns.any (fun column => nameEq column.name newName) then
      throw s!"duplicate column name: {newName}"
    let renamedColumns := table.columns.map (fun column =>
      if nameEq column.name oldName then { column with name := newName } else column)
    let renamedTable ← table.withColumnsChecked renamedColumns
    let renamedTriggers := db.triggers.map fun trigger =>
      if nameEq trigger.table tableName then
        { trigger with
          sourceSql := trigger.sourceSql.replace ("new." ++ oldName) ("new." ++ newName)
            |>.replace ("old." ++ oldName) ("old." ++ newName) }
      else trigger
    pure ({ (replaceTable db renamedTable) with triggers := renamedTriggers }, {})
  | .insert table names exprRows conflict returning => do
    unless returning.isEmpty do throw "INSERT RETURNING is implemented by the production Core engine"
    let rows ← exprRows.mapM fun row => row.mapM (evalWithDb db #[])
    if let some first := rows[0]? then
      unless rows.all (fun row => row.size == first.size) do
        throw "all VALUES must have the same number of terms"
    if (findView? db table).isSome || nameEq table "sqlite_master" || nameEq table "sqlite_schema" then
      insertValueRows db table names rows conflict
    else
      let before ← optionOr (findTable? db table) s!"no such table: {table}"
      let (state, result) ← insertValueRows db table names rows conflict
      let after ← optionOr (findTable? state table) s!"no such table: {table}"
      let inserted := after.rows.filter fun row => !before.rows.any (fun old => old.rowid == row.rowid)
      pure (← fireInsertTriggers state after inserted, result)
  | .insertSelect table names query conflict returning => do
    unless returning.isEmpty do throw "INSERT RETURNING is implemented by the production Core engine"
    let selected ← executeSelect db query
    if (findView? db table).isSome || nameEq table "sqlite_master" || nameEq table "sqlite_schema" then
      insertValueRows db table names selected.rows conflict
    else
      let before ← optionOr (findTable? db table) s!"no such table: {table}"
      let (state, result) ← insertValueRows db table names selected.rows conflict
      let after ← optionOr (findTable? state table) s!"no such table: {table}"
      let inserted := after.rows.filter fun row => !before.rows.any (fun old => old.rowid == row.rowid)
      pure (← fireInsertTriggers state after inserted, result)
  | .delete name alias where_ returning => do
    if nameEq name "sqlite_master" || nameEq name "sqlite_schema" then
      throw "table sqlite_master may not be modified"
    if (findView? db name).isSome then throw s!"cannot modify {name} because it is a view"
    let table ← optionOr (findTable? db name) s!"no such table: {name}"
    let ref : TableRef := { name, alias }
    let validationRow : StoredRow := { rowid := 0, values := table.columns.map fun _ => .null }
    if let some condition := where_ then
      discard <| evalWithDb db (makeBindings ref table validationRow) condition
    let mut kept := #[]
    let mut deleted := #[]
    let mut changes := 0
    for row in table.rows do
      if ← matchesWhere db (makeBindings ref table row) where_ then
        changes := changes + 1
        deleted := deleted.push row
      else kept := kept.push row
    let retained ← table.withRowsChecked kept
    let changed := replaceTable db retained
    let next ← applyDeleteEffects changed table deleted
    if returning.isEmpty then pure (next, mutationResult db changes)
    else
      let rows ← deleted.mapM fun row => expandResult db (makeBindings ref table row) returning
      let representative := makeBindings ref table (deleted[0]?.getD validationRow)
      let columns := resultNames db representative returning
      let result : QueryResult := { columns, rows, changes, reportsChanges := true }
      pure (next, result)
  | .update name alias assignments where_ conflict returning => do
    unless returning.isEmpty do throw "UPDATE RETURNING is implemented by the production Core engine"
    if nameEq name "sqlite_master" || nameEq name "sqlite_schema" then
      if !db.writableSchema then throw "table sqlite_master may not be modified"
      let sqlAssignment ← optionOr (assignments.find? fun assignment => nameEq assignment.1 "sql")
        "writable schema UPDATE must assign sql"
      let schemaSql ← evalWithDb db #[] sqlAssignment.2
      let updated ← replaceTableSchemaSql db (toString schemaSql)
      return (updated, mutationResult db 1)
    if (findView? db name).isSome then throw s!"cannot modify {name} because it is a view"
    let mut table ← optionOr (findTable? db name) s!"no such table: {name}"
    let mut state := db
    let evaluationDb := db
    for (column, _) in assignments do
      unless isRowidName column || table.columns.any (fun c => nameEq c.name column) do
        throw s!"no such column: {column}"
    let ref : TableRef := { name, alias }
    let validationRow : StoredRow := { rowid := 0, values := table.columns.map fun _ => .null }
    let validationEnv := makeBindings ref table validationRow
    if let some condition := where_ then discard <| evalWithDb state validationEnv condition
    for (_, expression) in assignments do discard <| evalWithDb state validationEnv expression
    for trigger in state.triggers do
      if nameEq trigger.table name && trigger.event == .update then
        if let some condition := trigger.when_ then
          let oldEnv := makeBindings { name, alias := some "old" } table validationRow
          let newEnv := makeBindings { name, alias := some "new" } table validationRow
          discard <| evalWithDb state (validationEnv ++ oldEnv.map Binding.outerScoped ++
            newEnv.map Binding.outerScoped) condition
    -- A rowid-only update over the whole table can be evaluated as one
    -- immutable array transformation. Besides being equivalent when no
    -- callbacks or foreign keys are involved, this avoids quadratic scans.
    if where_.isNone && conflict == .default && (integerPrimaryKey? table).isNone &&
        assignments.all (fun assignment => isRowidName assignment.1) &&
        !state.foreignKeys && !state.triggers.any (fun trigger => nameEq trigger.table name) then
      let mut seen := Std.HashSet.emptyWithCapacity (capacity := table.rows.size)
      let mut rows : Array StoredRow := Array.mkEmpty table.rows.size
      for row in table.rows do
        let env := makeBindings ref table row
        let mut rowid := row.rowid
        for (_, expression) in assignments do
          rowid ← optionOr (← evalWithDb evaluationDb env expression).toInt? "datatype mismatch"
        if seen.contains rowid then throw s!"UNIQUE constraint failed: {table.name}.rowid"
        seen := seen.insert rowid
        let values ← evaluateGeneratedColumns table rowid row.values
        rows := rows.push { row with rowid := rowid, values := values }
      let nextRowid := rows.foldl (init := table.nextRowid) fun next row =>
        max next (row.rowid + 1)
      let updatedTable ← ({ table with nextRowid }).withRowsChecked rows
      return (replaceTable state updatedTable, mutationResult db rows.size)
    let mut changes := 0
    let mut updatedRows : Array (StoredRow × StoredRow) := #[]
    let originals := table.rows
    for row in originals do
      let env := makeBindings ref table row
      if ← matchesWhere evaluationDb env where_ then
        let mut updated := row.values
        let mut assignedRowid := row.rowid
        for (column, expr) in assignments do
          let value ← evalWithDb evaluationDb env expr
          if isRowidName column then
            assignedRowid ← optionOr value.toInt? "datatype mismatch"
          else
            let idx := table.columns.findIdx? (fun c => nameEq c.name column) |>.getD 0
            if table.columns[idx]!.generated.isSome then
              throw s!"cannot UPDATE generated column \"{column}\""
            updated := updated.set! idx (table.columns[idx]!.applyAffinity value)
        let mut updatedRow := { row with values := updated, rowid := assignedRowid }
        if let some pk := integerPrimaryKey? table then
          if !(updated[pk]! matches .null) then
            let id ← optionOr updated[pk]!.toInt? "datatype mismatch"
            updatedRow := { updatedRow with rowid := id, values := updated.set! pk (.integer id) }
        let generatedValues ← evaluateGeneratedColumns table updatedRow.rowid updatedRow.values
        updatedRow := { updatedRow with values := generatedValues }
        state ← fireUpdateTriggers state table #[(row, updatedRow)] .before
        table ← optionOr (findTable? state name) s!"no such table: {name}"
        if let some current := table.rows.find? (fun candidate => candidate.rowid == row.rowid) then
          let mut merged := current.values
          for (column, _) in assignments do
            unless isRowidName column do
              let idx := table.columns.findIdx? (fun candidate => nameEq candidate.name column) |>.getD 0
              merged := merged.set! idx updatedRow.values[idx]!
          updatedRow := { current with values := merged, rowid := updatedRow.rowid }
        let generatedValues ← evaluateGeneratedColumns table updatedRow.rowid updatedRow.values
        updatedRow := { updatedRow with values := generatedValues }
        let (checkedRow, skipNotNull) ← enforceNotNull table updatedRow conflict
        updatedRow := checkedRow
        if skipNotNull then continue
        if conflict == .fail && !state.ignoreCheckConstraints then
          if let some check := table.checks.find? (fun check =>
              (violatesCheck state table updatedRow check).toOption.getD true) then
            let result := mutationResult db changes
            return (state, { result with deferredError := some s!"CHECK constraint failed: {check.diagnostic}" })
        if ← enforceChecks state table updatedRow conflict then continue
        validateForeignKeys state table updatedRow
        let withoutOld := table.rows.filter (fun r => r.rowid != row.rowid)
        let conflicts := withoutOld.filterMap fun old => (conflictTarget? table updatedRow old).map (old, ·)
        if conflicts.isEmpty then
          let rows := table.rows.map fun existing =>
            if existing.rowid == row.rowid then updatedRow else existing
          let advanced := { table with nextRowid := max table.nextRowid (updatedRow.rowid + 1) }
          table ← advanced.withRowsChecked rows
          state := replaceTable state table
          changes := changes + 1
          updatedRows := updatedRows.push (row, updatedRow)
        else
          let resolution := conflict.resolve conflicts[0]!.2.action
          match resolution with
          | .default => throw (conflictMessage table conflicts[0]!.2)
          | .abort => throw (conflictMessage table conflicts[0]!.2)
          | .fail =>
            let result := mutationResult db changes
            return (state, { result with deferredError := some (conflictMessage table conflicts[0]!.2) })
          | .rollback => throw (rollbackConflictPrefix ++ conflictMessage table conflicts[0]!.2)
          | .ignore => pure ()
          | .replace =>
            let reentrant := state.triggers.any fun trigger =>
              nameEq trigger.table name && trigger.event == .delete && trigger.body.any fun action =>
                match action with
                | .update target _ _ _ _ => nameEq target name
                | _ => false
            if reentrant then throw "constraint failed"
            let victims := conflicts.map (·.1)
            table ← table.withRowsChecked
              (withoutOld.filter fun old => !victims.any (·.rowid == old.rowid))
            state := replaceTable state table
            state ← applyDeleteEffects state table victims
            table ← optionOr (findTable? state name) s!"no such table: {name}"
            if let some (_, target) := table.rows.findSome? fun old =>
                (conflictTarget? table updatedRow old).map (old, ·) then
              throw (conflictMessage table target)
            table ← table.insertChecked updatedRow
            state := replaceTable state table
            changes := changes + 1
            updatedRows := updatedRows.push (row, updatedRow)
    state ← fireUpdateTriggers state table updatedRows .after
    if nameEq name "sqlite_sequence" then state := applySequenceHighWater state
    pure (state, mutationResult db changes)
  | .withRecursive name columnNames seedQuery step all body => do
    let seedResult ← executeSelect db seedQuery
    let seed := seedResult.rows
    let width := seed[0]?.map Array.size |>.getD columnNames.size
    unless seed.all (fun row => row.size == width) do
      throw "all VALUES must have the same number of terms"
    let names := if columnNames.isEmpty then valuesColumnNames width else columnNames
    unless names.size == width do throw s!"table {name} has {names.size} values for {width} columns"
    let columns : Array Column := names.map fun column => { name := column }
    let original := findTable? db name
    let install (state : Database) (rows : Array (Array Value)) : Except String Database := do
      let stored := rows.mapIdx fun i values => StoredRow.mk (Int.ofNat (i + 1)) values
      let rowStore ← RowStore.checked stored columns.size
      let temporary := Table.mk name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[]
      pure { state with tables := (state.tables.filter fun table => !nameEq table.name name) ++ [temporary] }
    let mut state := db
    let mut accumulated := seed
    let mut work := seed
    let mut iterations := 0
    while !work.isEmpty && iterations < 100000 do
      state ← install state work
      let selected ← executeSelect state step
      let mut next := selected.rows
      unless all do next := next.filter fun row => !accumulated.contains row
      accumulated := accumulated ++ next
      work := next
      iterations := iterations + 1
    if iterations == 100000 then throw "recursive CTE query limit exceeded"
    state ← install state accumulated
    let (after, result) ← executeCore state body
    let withoutCte := { after with tables := after.tables.filter fun table => !nameEq table.name name }
    let restored := match original with
      | some table => { withoutCte with tables := withoutCte.tables ++ [table] }
      | none => withoutCte
    pure (restored, result)
  | .withCte name columnNames source body => do
    let (_, materialized) ← executeCore db source
    let width := materialized.rows[0]?.map Array.size |>.getD materialized.columns.size
    unless materialized.rows.all (fun row => row.size == width) do
      throw "all rows of a common table expression must have the same width"
    let inferred : Array Column := match source with
      | .select query => selectColumnSchema db query
      | .values rows => match rows[0]? with
        | some expressions => expressions.mapIdx fun i expression =>
            { name := materialized.columns[i]?.getD s!"column{i + 1}",
              declaredType := expressionDeclaredType expression }
        | none => #[]
      | _ => materialized.columns.map fun column => { name := column }
    let names := if columnNames.isEmpty then materialized.columns else columnNames
    unless names.size == width do
      throw s!"table {name} has {names.size} values for {width} columns"
    let columns : Array Column := names.mapIdx fun i column =>
      (inferred[i]?.getD ({ name := column } : Column)).renamed column
    let stored := materialized.rows.mapIdx fun i values => StoredRow.mk (Int.ofNat (i + 1)) values
    let rowStore ← RowStore.checked stored columns.size
    let cte := Table.mk name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[]
    let original := findTable? db name
    let installed := { db with tables := (db.tables.filter fun table => !nameEq table.name name) ++ [cte] }
    let (after, result) ← executeCore installed body
    let withoutCte := { after with tables := after.tables.filter fun table => !nameEq table.name name }
    let restored := match original with
      | some table => { withoutCte with tables := withoutCte.tables ++ [table] }
      | none => withoutCte
    pure (restored, result)
  | .select query => do pure (db, ← executeSelect db query)
  | .values exprRows => do
    let rows ← exprRows.mapM fun row => row.mapM (evalWithDb db #[])
    let width := rows[0]?.map Array.size |>.getD 0
    unless rows.all (fun row => row.size == width) do
      throw "all VALUES must have the same number of terms"
    pure (db, { columns := valuesColumnNames width, rows })
  | .begin =>
    if db.transactionSnapshot.isSome then throw "cannot start a transaction within a transaction"
    else pure ({ db with transactionSnapshot := some {
      tables := db.tables, views := db.views, triggers := db.triggers, indexes := db.indexes } }, {})
  | .commit =>
    if db.transactionSnapshot.isNone then throw "cannot commit - no transaction is active"
    else pure ({ db with transactionSnapshot := none }, {})
  | .rollback =>
    match db.transactionSnapshot with
    | none => throw "cannot rollback - no transaction is active"
    | some snapshot => pure (db.restoreSnapshot snapshot, {})
  | .savepoint _ | .release _ | .rollbackTo _ => throw "SAVEPOINT is supported by the production Core engine"
  | .reindex => pure (db, {})
  | .pragma name argument _schema =>
    let enabled := match argument with
      | some (.literal (.integer i) _) => i != 0
      | some (.literal (.text s) _) | some (.column none s) =>
        ["on", "true", "yes", "1"].contains s.toLower
      | _ => false
    let shortName := name.splitOn "." |>.getLast?.getD name
    if nameEq shortName "short_column_names" then pure ({ db with shortColumnNames := enabled }, {})
    else if nameEq shortName "full_column_names" then pure ({ db with fullColumnNames := enabled }, {})
    else if nameEq shortName "foreign_keys" then pure ({ db with foreignKeys := enabled }, {})
    else if nameEq shortName "count_changes" then pure ({ db with countChanges := enabled }, {})
    else if nameEq shortName "recursive_triggers" then pure ({ db with recursiveTriggers := enabled }, {})
    else if nameEq shortName "ignore_check_constraints" then
      pure ({ db with ignoreCheckConstraints := enabled }, {})
    else if nameEq shortName "writable_schema" then pure ({ db with writableSchema := enabled }, {})
    else if nameEq shortName "lean_check_myfunc_enabled" then
      pure ({ db with checkMyfuncEnabled := enabled }, {})
    else if nameEq shortName "lean_readonly" then pure ({ db with readOnly := enabled }, {})
    else if nameEq shortName "lean_views_enabled" then pure ({ db with viewsEnabled := enabled }, {})
    else if nameEq shortName "lean_dqs_dml" then pure ({ db with doubleQuotedStrings := enabled }, {})
    else if nameEq shortName "lean_view_depth_limit" then
      let limit := match argument with
        | some (.literal (.integer value) _) => (max 1 value).toNat
        | _ => 1000
      pure ({ db with viewDepthLimit := limit }, {})
    else if nameEq shortName "lean_current_time" then
      let timestamp := match argument with
        | some (.literal (.integer value) _) => value
        | _ => 0
      pure ({ db with currentTime := timestamp }, {})
    else if nameEq shortName "lean_record_sizes" then
      let rootpage : Int := match argument with
        | some (.literal (.integer value) _) => value
        | _ => 0
      let rows := if rootpage < 2 then #[] else
        match db.tables[(rootpage - 2).toNat]? with
        | none => #[]
        | some table => table.rows.map fun row => #[.integer (Int.ofNat (sqliteRecordSize row.values))]
      pure (db, { columns := #["record_size"], rows })
    else if nameEq shortName "lean_analyze" then
      if (findTable? db "sqlite_stat1").isSome then pure (db, {})
      else
        let columns : Array Column := #[{ name := "tbl" }, { name := "idx" }, { name := "stat" }]
        let statistics : Table := { name := "sqlite_stat1", columns }
        pure ({ db with tables := db.tables ++ [statistics] }, {})
    else if nameEq shortName "encoding" then
      pure (db, { columns := #[name], rows := #[#[.text "UTF-8"]] })
    else if nameEq shortName "table_info" then do
      let objectName? := match argument with
        | some (.column none objectName) | some (.literal (.text objectName) _) => some objectName
        | _ => none
      let columns ← match objectName? with
        | none => pure #[]
        | some objectName =>
          if let some table := findTable? db objectName then pure table.columns
          else if let some view := findView? db objectName then
            let inferred := selectColumnSchema db view.query
            pure <| match view.columns with
              | none => inferred
              | some names => inferred.mapIdx fun i column =>
                  { column with name := names[i]?.getD column.name }
          else pure #[]
      let rows := columns.mapIdx fun i column => #[.integer i, .text column.name,
        .text column.declaredType, .integer (if column.notNull then 1 else 0),
        column.defaultSql.map Value.text |>.getD .null,
        .integer (if column.primaryKey then 1 else 0)]
      pure (db, { columns := #["cid", "name", "type", "notnull", "dflt_value", "pk"], rows })
    else if nameEq shortName "integrity_check" || nameEq shortName "quick_check" then
      let broken := if db.ignoreCheckConstraints then none else db.tables.find? fun table =>
        table.rows.any fun row => table.checks.any fun check =>
          (violatesCheck db table row check).toOption.getD true
      let message := broken.map (fun table => s!"CHECK constraint failed in {unqualifiedName table.name}")
        |>.getD "ok"
      pure (db, { columns := #[name], rows := #[#[.text message]] })
    else if nameEq shortName "locking_mode" then
      pure (db, { columns := #[name], rows := #[#[.text "normal"]] })
    else pure (db, {})

private def Statement.writes : Statement → Bool
  | .createTable .. | .createTableAs .. | .createView ..
  | .dropTable .. | .dropView .. | .createIndex .. | .dropIndex ..
  | .createTrigger .. | .dropTrigger .. | .alterAddColumn .. | .alterDropColumn .. | .alterRenameTable .. | .alterRenameColumn ..
  | .insert .. | .insertSelect .. | .delete .. | .update .. | .reindex => true
  | .withRecursive .. | .withCte .. => true
  | _ => false

def execute (db : Database) (statement : Statement) : Except String (Database × QueryResult) :=
  if db.readOnly && statement.writes then .error "attempt to write a readonly database"
  else executeCore db statement

theorem execute_success_wellFormed {database resultDatabase : Database}
    {statement : Statement} {result : QueryResult}
    (_success : execute database statement = .ok (resultDatabase, result)) :
    resultDatabase.WellFormed :=
  resultDatabase.wellFormed

def executeAll (db : Database) (statements : Array Statement) : Except String (Database × QueryResult) := do
  let mut state := db
  let mut last := {}
  let mut retainQueryRows := false
  for stmt in statements do
    let (next, result) ← execute state stmt
    state := next
    if let some message := result.deferredError then throw message
    if !result.rows.isEmpty then
      last := { result with rows := last.rows ++ result.rows }
      if (stmt matches .select _) || (stmt matches .values _) then retainQueryRows := true
      else if stmt matches .pragma .. then retainQueryRows := false
    else if result.reportsChanges && !retainQueryRows then last := result
    else if (stmt matches .select _) || (stmt matches .values _) || (stmt matches .pragma ..) then
      if last.rows.isEmpty then last := result
  pure (state, last)

/-- Execute statements sequentially while retaining commits from statements before an error. -/
def executeAllProgress (db : Database) (statements : Array Statement) : Database × Except String QueryResult := Id.run do
  let mut state := db
  let mut last : QueryResult := {}
  let mut retainQueryRows := false
  for stmt in statements do
    match execute state stmt with
    | .error message =>
      if message.startsWith rollbackConflictPrefix then
        let restored := match state.transactionSnapshot with
          | some snapshot => state.restoreSnapshot snapshot
          | none => state
        return (restored, .error (message.drop rollbackConflictPrefix.length).toString)
      return (state, .error message)
    | .ok (next, result) =>
      state := next
      if let some message := result.deferredError then return (state, .error message)
      if !result.rows.isEmpty then
        last := { result with rows := last.rows ++ result.rows }
        if (stmt matches .select _) || (stmt matches .values _) then retainQueryRows := true
        else if stmt matches .pragma .. then retainQueryRows := false
      else if result.reportsChanges && !retainQueryRows then last := result
      else if (stmt matches .select _) || (stmt matches .values _) || (stmt matches .pragma ..) then
        if last.rows.isEmpty then last := result
  return (state, .ok last)

def runSQL (db : Database) (sql : String) : Except String (Database × QueryResult) := do
  executeAll db (← parse sql)

def runSQLProgress (db : Database) (sql : String) : Database × Except String QueryResult :=
  match parseProgress sql with
  | .error message => (db, .error message)
  | .ok (statements, parseError) =>
    let (next, outcome) := executeAllProgress db statements
    match outcome with
    | .error message => (next, .error message)
    | .ok result => match parseError with
      | some message => (next, .error message)
      | none => (next, .ok result)

theorem runSQLProgress_parse_error (db : Database) (sql message : String)
    (failure : parseProgress sql = .error message) :
    runSQLProgress db sql = (db, .error message) := by
  simp [runSQLProgress, failure]

end SQLeanite
