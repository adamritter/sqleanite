import SQLeanite.CoreAutomaticIndex
import SQLeanite.CoreEngine.ChooseExtremeEqLeftOrRight
import SQLeanite.CoreForeignKeyData

/-! SQLite's schema-inspection PRAGMAs over the admitted Core schema. These
read the same names, column flags and indexes used by persistence and SQL.
There is no separate catalog or metadata cache to become stale after ALTER. -/
namespace SQLeanite.CoreSchemaPragma

def supported (name : String) : Bool :=
  ["table_info", "table_xinfo", "table_list", "index_list", "index_info", "index_xinfo", "pragma_list", "foreign_key_list", "foreign_key_check"].contains name.toLower

def argumentName : Expr → Option String
  | .column none name => some name
  | .literal (.text name) _ => some name
  | .literal (.integer value) source => some (source.getD (toString value))
  | .literal (.real _) source => source
  | .call "lean_dqs" #[.literal (.text name) _] false => some name
  | .call "__sqlean_boolean_true" #[] false => some "true"
  | .call "__sqlean_boolean_false" #[] false => some "false"
  | _ => none

/-- build.c stores these six standard type names in canonical spelling. -/
def columnType (column : Core.Column) : String :=
  if column.integerPrimaryKey then "INTEGER"
  else if column.textPrimaryKey then (column.indexedType.map (·.declaredType)).getD "TEXT"
  else column.declaredType

def flag (value : Bool) : Value := .integer (if value then 1 else 0)

def tableRows (schema : Core.Schema) (extended : Bool) : List (List Value) :=
  schema.catalogColumns.zipIdx.map fun (column, position) =>
    [.integer position, .text column.name, .text (columnType column),
      flag (if column.integerPrimaryKey then column.integerPrimaryNotNull else column.notNull),
      (column.defaultValue.map (fun spec => Value.text (ColumnDefault.metadata spec))).getD .null, flag (position == schema.declaredPrimaryKey)] ++
        (if extended then [.integer 0] else [])

theorem tableRows_length (schema : Core.Schema) (extended : Bool) :
    (tableRows schema extended).length = schema.catalogColumns.length := by
  simp [tableRows]

/-- sqlite_schema and its aliases have this built-in rowid-table definition. -/
def catalogRows (extended : Bool) : List (List Value) :=
  [("type", "TEXT"), ("name", "TEXT"), ("tbl_name", "TEXT"),
    ("rootpage", "INT"), ("sql", "TEXT")].zipIdx.map fun ((name, typeName), position) =>
      [.integer position, .text name, .text typeName, .integer 0, .null, .integer 0] ++
        (if extended then [.integer 0] else [])

def tableInfo (database : Core.Database) (name : String) (extended : Bool) : List (List Value) :=
  if ["sqlite_schema", "sqlite_master", "sqlite_temp_schema", "sqlite_temp_master"].contains name.toLower then
    catalogRows extended
  else ((CoreNames.table? database name).map fun table => tableRows table.schema extended).getD []

def indexRows (table : Core.Table) : List (List Value) :=
  table.indexes.reverse.zipIdx.map fun (index, position) =>
    let primary := CoreAutomaticIndex.primary table index
    [.integer position, .text index.name, flag (index.unique || primary),
      .text (if primary then "pk" else if CoreAutomaticIndex.contains table index then "u" else "c"), .integer 0]

theorem indexRows_length (table : Core.Table) :
    (indexRows table).length = table.indexes.length := by
  simp [indexRows]

def indexList (database : Core.Database) (name : String) : List (List Value) :=
  ((CoreNames.table? database name).map indexRows).getD []

def findIndex (database : Core.Database) (name : String) : Option (Core.Table × Core.Index) := do
  let table ← database.tables.find? fun table => (CoreNames.index? table name).isSome
  let index ← CoreNames.index? table name
  some (table, index)

def indexInfo (database : Core.Database) (name : String) (extended : Bool) : List (List Value) :=
  match findIndex database name with
  | none => []
  | some (table, index) =>
      match table.schema.catalogColumns[index.column]? with
      | none => []
      | some column =>
          let key : List Value := [.integer 0, .integer index.column, .text column.name]
          if extended then
            [key ++ [.integer 0, .text "BINARY", .integer 1],
              [.integer 1, .integer (-1), .null, .integer 0, .text "BINARY", .integer 0]]
          else [key]

def rows (database : Core.Database) (pragmaName name : String) : List (List Value) :=
  match pragmaName.toLower with
  | "table_info" => tableInfo database name false
  | "table_xinfo" => tableInfo database name true
  | "index_list" => indexList database name
  | "index_info" => indexInfo database name false
  | "index_xinfo" => indexInfo database name true
  | _ => []

/-- Full and filtered physical indexes share the actual catalog identities.
Source predicates never become fabricated full indexes in the Core model. -/
def rowsWithState (state : Core.State) (name target : String) : Except String (List (List Value)) := do
  if state.catalog.current.filteredIndexes.isEmpty then return rows state.database name target
  if name.toLower == "index_list" then
    let basic := indexList state.database target
    let extra := (state.catalog.current.filteredIndexes.filter
      (fun index => index.owner.toLower == target.toLower)).map fun index =>
        [Value.integer 0,.text index.definition.name,flag index.definition.unique,.text "c",.integer 1]
    let rank := fun (row : List Value) => match row[1]? with
      | some (.text indexName) => ((state.catalog.current.identities.find? (fun (identity : CoreCatalogData.Identity) =>
          identity.kind == "index" && identity.name.toLower == indexName.toLower)).map
            (fun (identity : CoreCatalogData.Identity) => identity.rowid)).getD 0
      | _ => 0
    let selected := (basic ++ extra).mergeSort (fun left right => rank left ≥ rank right)
    return selected.zipIdx.map fun (row,position) => row.set 0 (.integer position)
  if !["index_info","index_xinfo"].contains name.toLower then return rows state.database name target
  let some source := state.catalog.current.filteredIndexes.find?
    (fun index => index.definition.name.toLower == target.toLower) | return rows state.database name target
  let some table := CoreNames.table? state.database source.owner | throw "missing partial index owner"
  let some position := table.schema.declaredColumn? source.definition.column | throw "missing partial index column"
  let some column := table.schema.catalogColumns[position]? | throw "missing partial index declaration"
  let key : List Value := [.integer 0,.integer position,.text column.name]
  return if name.toLower == "index_xinfo" then
    [key ++ [.integer 0,.text "BINARY",.integer 1],
      [.integer 1,.integer (-1),.null,.integer 0,.text "BINARY",.integer 0]] else [key]


/-- The current Core has one persistent schema and an empty temporary schema.
Retain an explicit qualifier instead of confusing it with a quoted period. -/
def scopedRows (database : Core.Database) (schema : Option String)
    (pragmaName target : String) : List (List Value) :=
  let temporary := schema.any (fun name => name.toLower == "temp")
  if schema.any (fun name => name.toLower == "main") &&
      ["sqlite_temp_schema", "sqlite_temp_master"].contains target.toLower then []
  else rows (if temporary then Core.Database.empty else database) pragmaName target

def scopedRowsWithState (state : Core.State) (schema : Option String)
    (name target : String) : Except String (List (List Value)) :=
  if schema.any (fun name => name.toLower == "temp") ||
      (schema.any (fun name => name.toLower == "main") &&
        ["sqlite_temp_schema","sqlite_temp_master"].contains target.toLower) then
    .ok (rows Core.Database.empty name target)
  else rowsWithState state name target


theorem scopedRows_temp (database : Core.Database) (schema pragmaName target : String)
    (folded : schema.toLower = "temp") :
    scopedRows database (some schema) pragmaName target =
      rows Core.Database.empty pragmaName target := by
  simp [scopedRows, folded]

/-- Names recognized by the pinned SQLite build. Listing a name is not a
claim that the corresponding operation is implemented by this port. -/
def pragmaListRows : List (List Value) :=
  SQLite.PragmaSyntax.knownNames.map fun name => [.text name]

theorem pragmaListRows_length :
    pragmaListRows.length = SQLite.PragmaSyntax.knownNames.length := by
  simp [pragmaListRows]

/-- Listing uses the pinned live schema order and filters the stored catalog
name before exposing SQLite's preferred sqlite_schema spelling. -/
def tableList (database : Core.Database) (schema target : Option String)
    (tableOrder : Option (List String)) (viewNames : List String := []) : Except String (List (List Value)) := do
  let keep := fun stored => target.all (fun requested => requested.toLower == stored.toLower)
  let mut result := []
  unless schema.any (fun name => name.toLower == "temp") do
    let order := tableOrder.getD (SQLite.SchemaHash.order (database.tables.map (·.schema.name)))
    for name in order do
      unless keep name do continue
      if name == "sqlite_master" then
        result := [.text "main", .text "sqlite_schema", .text "table", .integer 5, .integer 0, .integer 0] :: result
      else if let some table := database.findTable? name then
        let strict ← match table.catalogSource with
          | none => pure false
          | some source => (Option.isSome) <$> source.compiledStrictColumns
        result := [.text "main", .text table.schema.name, .text (if viewNames.contains table.schema.name then "view" else "table"),
          .integer table.schema.catalogColumns.length, .integer 0, flag strict] :: result
  unless schema.any (fun name => name.toLower == "main") do
    if keep "sqlite_temp_master" then
      result := [.text "temp", .text "sqlite_temp_schema", .text "table", .integer 5, .integer 0, .integer 0] :: result
  return result.reverse

def inspectionRows (database : Core.Database) (schema : Option String)
    (name : String) (target : Option String) (tableOrder : Option (List String) := none)
    (viewNames : List String := []) : Except String (List (List Value)) := do
  if name.toLower == "table_list" then return ← tableList database schema target tableOrder viewNames
  let schemaDatabase := if schema.any (fun name => name.toLower == "temp") then Core.Database.empty else database
  if name.toLower == "foreign_key_check" then
    return ← CoreForeignKeyData.checkRows schemaDatabase
      (schema.map fun name => if name.toLower == "temp" then "temp" else "main") target tableOrder
  if ["table_info", "table_xinfo"].contains name.toLower then
    if let some table := target.bind (CoreNames.table? schemaDatabase) then
      if let some source := table.catalogSource then
        let types ← source.compiledStrictColumns
        let generated ← source.compiledGeneratedColumns
        let extended := name.toLower == "table_xinfo"
        let mut result := []
        let mut visible := 0
        for (original, position) in (tableRows table.schema extended).zipIdx do
          let hidden := generated.any (fun spec => spec.position == position)
          if hidden && !extended then continue
          let mut row := original
          if let some (_, typ) := types.bind (fun columns => columns[position]?) then row := row.set 2 (.text typ)
          row := row.set 0 (.integer (if extended then position else visible))
          if extended && hidden then row := row.set 6 (.integer 3)
          result := row :: result
          visible := visible + 1
        return result.reverse
  match target with
  | none => pure []
  | some target =>
      if name.toLower == "foreign_key_list" then CoreForeignKeyData.listRows schemaDatabase target
      else pure (scopedRows database schema name target)

def result (database : Core.Database) (name : String) (argument : Option Expr)
    (schema : Option String) (tableOrder : Option (List String) := none) : Except String Core.Result := do
  if schema.any (fun name => !["main", "temp"].contains name.toLower) then
    throw s!"unknown database {schema.getD ""}"
  if !SQLite.PragmaSyntax.knownNames.contains name.toLower then return {}
  unless supported name do throw "unsupported verified-Core PRAGMA"
  let values ← if name.toLower == "pragma_list" then pure pragmaListRows
    else do
      let target ← argument.mapM fun argument => do
        let some target := argumentName argument | throw "unsupported PRAGMA argument"
        pure target
      inspectionRows database schema name target tableOrder
  let values ← values.mapM (List.mapM SQLSurface.value)
  return { rows := values }

theorem result_unknown_schema (database : Core.Database) (name schema : String)
    (argument : Option Expr)
    (missing : ["main", "temp"].contains schema.toLower = false) :
    result database name argument (some schema) = .error s!"unknown database {schema}" := by
  have rejected : (some schema).any (fun name => !["main", "temp"].contains name.toLower) = true := by
    change !["main", "temp"].contains schema.toLower = true
    rw [missing]
    rfl
  unfold result
  rw [rejected]
  rfl

def execute (state : Core.State) (name : String) (argument : Option Expr)
    (schema : Option String := none) : Except String (Core.State × List Core.Result) := do
  let output ← result state.database name argument schema (state.schemaHash.map (·.names))
  return (state, [output])

theorem execute_preserves_state {state next : Core.State} {name : String}
    {argument : Option Expr} {schema : Option String} {results : List Core.Result}
    (success : execute state name argument schema = .ok (next, results)) : next = state := by
  unfold execute at success
  cases evaluated : result state.database name argument schema (state.schemaHash.map (·.names)) with
  | error message => simp [evaluated, bind, Except.bind] at success
  | ok output =>
      simp only [evaluated, bind, Except.bind, pure, Except.pure] at success
      exact (congrArg Prod.fst (Except.ok.inj success)).symm

end SQLeanite.CoreSchemaPragma
