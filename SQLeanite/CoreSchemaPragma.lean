import SQLeanite.CoreEngine
import SQLeanite.CoreNames
import SQLeanite.SQLSurface

/-! SQLite's schema-inspection PRAGMAs over the admitted Core schema. These
read the same names, column flags and indexes used by persistence and SQL.
There is no separate catalog or metadata cache to become stale after ALTER. -/
namespace SQLeanite.CoreSchemaPragma

def supported (name : String) : Bool :=
  ["table_info", "table_xinfo", "index_list", "index_info", "index_xinfo"].contains name.toLower

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
  else if column.textPrimaryKey then "TEXT"
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
    let primary := index.isImplicitPrimary table.schema
    [.integer position, .text index.name, flag (index.unique || primary),
      .text (if primary then "pk" else "c"), .integer 0]

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

/-- The current Core has one persistent schema and an empty temporary schema.
Retain an explicit qualifier instead of confusing it with a quoted period. -/
def scopedRows (database : Core.Database) (schema : Option String)
    (pragmaName target : String) : List (List Value) :=
  let temporary := schema.any (fun name => name.toLower == "temp")
  if schema.any (fun name => name.toLower == "main") &&
      ["sqlite_temp_schema", "sqlite_temp_master"].contains target.toLower then []
  else rows (if temporary then Core.Database.empty else database) pragmaName target

theorem scopedRows_temp (database : Core.Database) (schema pragmaName target : String)
    (folded : schema.toLower = "temp") :
    scopedRows database (some schema) pragmaName target =
      rows Core.Database.empty pragmaName target := by
  simp [scopedRows, folded]

def result (database : Core.Database) (name : String) (argument : Option Expr)
    (schema : Option String) : Except String Core.Result := do
  if schema.any (fun name => !["main", "temp"].contains name.toLower) then
    throw "unknown database"
  if !SQLite.PragmaSyntax.knownNames.contains name.toLower then return {}
  unless supported name do throw "unsupported verified-Core PRAGMA"
  let values ← match argument with
    | none => pure []
    | some argument => do
        let some target := argumentName argument | throw "unsupported PRAGMA argument"
        pure (scopedRows database schema name target)
  let values ← values.mapM (List.mapM SQLSurface.value)
  return { rows := values }

def execute (state : Core.State) (name : String) (argument : Option Expr)
    (schema : Option String := none) : Except String (Core.State × List Core.Result) := do
  let output ← result state.database name argument schema
  return (state, [output])

theorem execute_preserves_state {state next : Core.State} {name : String}
    {argument : Option Expr} {schema : Option String} {results : List Core.Result}
    (success : execute state name argument schema = .ok (next, results)) : next = state := by
  unfold execute at success
  cases evaluated : result state.database name argument schema with
  | error message => simp [evaluated, bind, Except.bind] at success
  | ok output =>
      simp only [evaluated, bind, Except.bind, pure, Except.pure] at success
      exact (congrArg Prod.fst (Except.ok.inj success)).symm

end SQLeanite.CoreSchemaPragma
