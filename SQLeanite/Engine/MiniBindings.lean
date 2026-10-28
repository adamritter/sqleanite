import SQLeanite.Engine.TrimValue
import SQLeanite.Parser.ParseTrigger

namespace SQLeanite

def miniBindings (ref : TableRef) (table : Table) (row : StoredRow) : Env :=
  let defaultAlias := unqualifiedName table.name
  let visible := table.columns.mapIdx fun i col =>
    { table := ref.name, alias := ref.alias.getD defaultAlias,
      column := col.name, value := row.values[i]?.getD .null, collation := col.collation,
      declaredType := col.declaredType }
  let hidden := #["rowid", "_rowid_", "oid"].map fun name =>
    Binding.mk ref.name (ref.alias.getD defaultAlias) name (.integer row.rowid)
      true 0 "binary" "LEAN_HIDDEN"
  visible ++ hidden

def deduplicateColumns (columns : Array Column) : Array Column := Id.run do
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

def expressionDeclaredType : Expr → String
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

def compatibleResultTypes (left right : String) : Bool :=
  nameEq left right || (hasNumericAffinity left && hasNumericAffinity right) ||
    left.isEmpty || right.isEmpty

def Column.renamed (column : Column) (name : String) : Column :=
  { column with name }

def applyColumnAliases (aliases : Array String) (columns : Array Column) : Array Column :=
  if aliases.isEmpty then columns
  else columns.mapIdx fun i column => column.renamed (aliases[i]?.getD column.name)

theorem applyColumnAliases_preserves_width (aliases : Array String) (columns : Array Column) :
    (applyColumnAliases aliases columns).size = columns.size := by
  simp only [applyColumnAliases]
  split <;> simp

def valuesColumnNames (width : Nat) : Array String :=
  (Array.range width).map fun i => s!"column{i + 1}"

abbrev sqliteVarintSize := FileFormat.sqliteVarintSize

theorem sqliteVarintSize_positive (value : Nat) : 0 < sqliteVarintSize value := by
  exact FileFormat.sqliteVarintSize_positive value

def sqliteSerialTypeAndPayload : Value → Nat × Nat
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
def sqliteRecordSize (values : Array Value) : Nat :=
  let encodings := values.map sqliteSerialTypeAndPayload
  let serialBytes := encodings.foldl (fun total item => total + sqliteVarintSize item.1) 0
  let payloadBytes := encodings.foldl (fun total item => total + item.2) 0
  let header := FileFormat.recordHeaderSize serialBytes
  header + payloadBytes

def selectColumnSchemaFuel : Nat → Database → Select → Array Column
  | 0, _, _ => #[]
  | fuel + 1, db, query => Id.run do
    let mut output := #[]
    for result in query.columns do
      match result.expr with
      | .star qualifier =>
        for source in query.sources do
          if qualifier.all (fun q => nameEq q source.name || source.alias.any (nameEq q)) then
            if let some sql := source.subquerySql then
              match parseLegacy sql with
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
                match parseLegacy sql with
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

def selectColumnSchema (db : Database) (query : Select) : Array Column :=
  selectColumnSchemaFuel (query.compoundHeight + db.viewDepthLimit + 1) db query

def selectColumnNames (db : Database) (query : Select) : Array String :=
  (selectColumnSchema db query).map (·.name)

def Expr.baseColumnName? : Expr → Option String
  | .column _ name => some name
  | .collate expression _ | .unary .plus expression => expression.baseColumnName?
  | _ => none

def Expr.directColumnName? : Expr → Option String
  | .column none name => some name
  | _ => none

def shouldSortDistinctByIndex (db : Database) (query : Select) : Bool :=
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

def armOutputMatchesFuel : Nat → Database → Select → Nat → Expr → Bool
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

def armOutputMatches (db : Database) (query : Select) (index : Nat)
    (term : Expr) : Bool :=
  armOutputMatchesFuel query.compoundHeight db query index term

def compoundOrderIndex (db : Database) (query : Select) (names : Array String) (position : Nat)
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

def Expr.explicitOrderCollation? : Expr → Option String
  | .collate _ name => some name
  | .unary .plus expression => expression.explicitOrderCollation?
  | _ => none

def rtrimCollationText (value : String) : String :=
  String.mk (value.toList.reverse.dropWhile (fun character => character == ' ')).reverse

theorem rtrimCollationText_append_space (value : String) :
    rtrimCollationText (value ++ " ") = rtrimCollationText value := by
  simp [rtrimCollationText]

def collatedCompare (collation : String) (left right : Value) : Ordering :=
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

def deduplicateNonNullValues (collation : String) (values : Array Value) : Array Value := Id.run do
  let mut distinct := #[]
  for value in values do
    unless value matches .null do
      unless distinct.any (fun prior => collatedCompare collation prior value == .eq) do
        distinct := distinct.push value
  pure distinct

def rowsEqualCollated (collations : Array String) (left right : Array Value) : Bool :=
  left.size == right.size && (Array.range left.size).all fun index =>
    collatedCompare (collations[index]?.getD "binary") left[index]! right[index]! == .eq

theorem rowsEqualCollated_same_width (collations : Array String) (left right : Array Value)
    (equal : rowsEqualCollated collations left right = true) : left.size = right.size := by
  have sizesEqual : (left.size == right.size) = true := (Bool.and_eq_true_iff.mp equal).1
  exact beq_iff_eq.mp sizesEqual

def containsCollated (collations : Array String) (rows : Array (Array Value))
    (row : Array Value) : Bool :=
  rows.any (rowsEqualCollated collations row)

def distinctCollated (collations : Array String)
    (rows : Array (Array Value)) : Array (Array Value) := Id.run do
  let mut distinct := #[]
  for row in rows do
    unless containsCollated collations distinct row do distinct := distinct.push row
  return distinct

def combineCompoundRowsCollated (collations : Array String) (operation : CompoundOp)
    (left right : Array (Array Value)) : Array (Array Value) :=
  match operation with
  | .unionAll => combineCompoundRows .unionAll left right
  | .unionDistinct => distinctCollated collations
      (combineCompoundRows .unionDistinct left right)
  | .except => distinctCollated collations (left.filter fun row =>
      !containsCollated collations right row)
  | .intersect => distinctCollated collations (left.filter fun row =>
      containsCollated collations right row)

def rowLessCollated (collations : Array String) (left right : Array Value) : Bool := Id.run do
  for index in [:min left.size right.size] do
    let order := collatedCompare (collations[index]?.getD "binary") left[index]! right[index]!
    if order != .eq then return order == .lt
  return left.size < right.size

def insertRowCollated (collations : Array String) (rows : List (Array Value))
    (row : Array Value) : List (Array Value) :=
  match rows with
  | [] => [row]
  | first :: rest => if rowLessCollated collations row first then row :: first :: rest
    else first :: insertRowCollated collations rest row

def sortRowsCollated (collations : Array String)
    (rows : Array (Array Value)) : Array (Array Value) :=
  (rows.foldl (insertRowCollated collations) []).toArray

def nullOrderLess? (descending : Bool) (nullsFirst : Option Bool)
    (left right : Value) : Option Bool :=
  match left, right with
  | .null, .null => none
  | .null, _ => some (nullsFirst.getD (!descending))
  | _, .null => some (!(nullsFirst.getD (!descending)))
  | _, _ => none

def orderedValueRowsLess (keys : Array (Nat × Bool × String × Option Bool))
    (a b : Array Value) : Bool := Id.run do
  for (index, descending, collation, nullsFirst) in keys do
    if let some before := nullOrderLess? descending nullsFirst (a[index]?.getD .null) (b[index]?.getD .null) then
      return before
    let ord := collatedCompare collation (a[index]?.getD .null) (b[index]?.getD .null)
    if ord != .eq then return if descending then ord == .gt else ord == .lt
  return false

def insertOrderedValueRow (keys : Array (Nat × Bool × String × Option Bool))
    (rows : List (Array Value)) (row : Array Value) : List (Array Value) :=
  match rows with
  | [] => [row]
  | first :: rest =>
    if orderedValueRowsLess keys row first then row :: first :: rest
    else first :: insertOrderedValueRow keys rest row

def sortOrderedValueRows (keys : Array (Nat × Bool × String × Option Bool))
    (rows : Array (Array Value)) : Array (Array Value) :=
  (rows.foldl (insertOrderedValueRow keys) []).toArray

def compoundOrderKeys (db : Database) (query : Select) (names : Array String) :
    Except String (Array (Nat × Bool × String × Option Bool)) := do
  let schema := selectColumnSchema db query
  query.orderBy.mapIdxM fun position term => do
    let index ← compoundOrderIndex db query names position term.expr
    let inherited := schema[index]?.map (·.collation) |>.getD "binary"
    pure (index, term.descending, term.expr.explicitOrderCollation?.getD inherited, term.nullsFirst)

structure KeyedRow where
  values : Array Value
  keys : Array (Value × Bool × String × Option Bool)

def keyedRowLess (left right : KeyedRow) : Bool := Id.run do
  for index in [:min left.keys.size right.keys.size] do
    let (leftValue, descending, collation, nullsFirst) := left.keys[index]!
    let rightValue := right.keys[index]!.1
    if let some before := nullOrderLess? descending nullsFirst leftValue rightValue then return before
    let order := collatedCompare collation leftValue rightValue
    if order != .eq then return if descending then order == .gt else order == .lt
  return false

def insertKeyedRow (rows : List KeyedRow) (row : KeyedRow) : List KeyedRow :=
  match rows with
  | [] => [row]
  | first :: rest => if keyedRowLess row first then row :: first :: rest
    else first :: insertKeyedRow rest row

def sortKeyedRows (rows : Array KeyedRow) : Array (Array Value) :=
  (rows.foldl insertKeyedRow []).toArray.map (·.values)

def valueKeysLess (left right : Array Value) : Bool := Id.run do
  for i in [:min left.size right.size] do
    let order := left[i]!.compare right[i]!
    if order != .eq then return order == .lt
  return left.size < right.size

def insertValueKeyed {α} (item : Array Value × α) :
    List (Array Value × α) → List (Array Value × α)
  | [] => [item]
  | first :: rest =>
    if valueKeysLess item.1 first.1 then item :: first :: rest
    else first :: insertValueKeyed item rest

def sortValueKeyed {α} (items : Array (Array Value × α)) : Array (Array Value × α) :=
  (items.foldl (fun sorted item => insertValueKeyed item sorted) []).toArray

theorem insertValueKeyed_perm {α} (item : Array Value × α)
    (items : List (Array Value × α)) :
    (insertValueKeyed item items).Perm (item :: items) := by
  induction items with
  | nil => exact List.Perm.refl _
  | cons first rest induction =>
      unfold insertValueKeyed
      split
      · exact List.Perm.refl _
      · exact (induction.cons first).trans (List.Perm.swap item first rest)

theorem foldInsertValueKeyed_perm {α}
    (items accumulator : List (Array Value × α)) :
    (items.foldl (fun sorted item => insertValueKeyed item sorted) accumulator).Perm
      (items ++ accumulator) := by
  induction items generalizing accumulator with
  | nil => exact List.Perm.refl _
  | cons item items induction =>
      have tail := induction (insertValueKeyed item accumulator)
      have inserted := (insertValueKeyed_perm item accumulator).append_left items
      exact tail.trans (inserted.trans List.perm_middle)

theorem sortValueKeyed_perm {α} (items : Array (Array Value × α)) :
    (sortValueKeyed items).toList.Perm items.toList := by
  unfold sortValueKeyed
  simpa using foldInsertValueKeyed_perm items.toList []

def isLeapYear (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

def daysInYear (year : Nat) : Nat := if isLeapYear year then 366 else 365

theorem daysInYear_positive (year : Nat) : 0 < daysInYear year := by
  simp only [daysInYear]
  split <;> omega

end SQLeanite
