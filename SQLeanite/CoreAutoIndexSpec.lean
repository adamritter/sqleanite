import SQLeanite.Syntax.UnaryOp
import SQLeanite.CanonicalSchemaSQL.Printable
import SQLeanite.SQLite.ColumnType

/-! Automatic-index declaration order and complete source-derived key names.
The physical rowid alias is supplied by the caller's admitted schema. -/
namespace SQLeanite.CoreAutoIndexSpec

structure Key where
  column : String
  collation : String
  deriving DecidableEq, Repr

structure Spec where
  table : String
  name : String
  keys : List Key
  primary : Bool
  deriving DecidableEq, Repr

def Key.identity (key : Key) : String × String := (key.column.toLower,key.collation.toLower)

def merge (keys : List Key) (primary : Bool) : List (List Key × Bool) → List (List Key × Bool)
  | [] => [(keys,primary)]
  | (previous,wasPrimary) :: rest =>
      if previous.map Key.identity == keys.map Key.identity then (previous,wasPrimary || primary) :: rest
      else (previous,wasPrimary) :: merge keys primary rest

def declaredCollation (columns : Array ColumnDef) (name : String) : String :=
  ((columns.find? (fun column => column.name.toLower == name.toLower)).map (·.collation)).getD "binary"

def collect (table : String) (columns : Array ColumnDef) (constraints : Array TableConstraintDef)
    (integerAlias : Option String) : List Spec := Id.run do
  let mut groups : List (List Key × Bool) := []
  for column in columns do
    let key : Key := { column := column.name, collation := column.collation }
    if column.primaryKey && !integerAlias.any (fun name => name.toLower == column.name.toLower) then
      groups := merge [key] true groups
    if column.unique then groups := merge [key] false groups
  for constraint in constraints do
    if constraint.check.isSome || constraint.references.isSome then continue
    if constraint.primaryKey && constraint.columns.size == 1 &&
        integerAlias.any (fun name => constraint.columns[0]?.any (fun column => column.toLower == name.toLower)) then continue
    let keys := constraint.columns.toList.zipIdx.map fun (name,position) => {
      column := name
      collation := (constraint.collations[position]?.getD none).getD (declaredCollation columns name) : Key }
    groups := merge keys constraint.primaryKey groups
  return groups.zipIdx.map fun ((keys,primary),number) => {
    table, name := s!"sqlite_autoindex_{table}_{number+1}", keys, primary }

def integerAlias? (columns : Array ColumnDef) (constraints : Array TableConstraintDef) : Option String := do
  let name ← match columns.find? (·.primaryKey) with
    | some column => some column.name
    | none => do
        let primary ← constraints.find? (·.primaryKey)
        unless primary.columns.size == 1 do none
        primary.columns[0]?
  let column ← columns.find? (fun column => column.name.toLower == name.toLower)
  unless SQLite.ColumnType.standard column.declaredType == some "INTEGER" do none
  return column.name

def Spec.auxiliary (spec : Spec) : Bool :=
  spec.keys.length > 1 || spec.keys.any (fun key => key.collation.toLower != "binary")

def quoteName (name : String) : String := String.ofList (CanonicalSchemaSQL.quoteChars name)

def Spec.source (spec : Spec) : String :=
  "CREATE UNIQUE INDEX " ++ quoteName spec.name ++ " ON " ++ quoteName spec.table ++ "(" ++
    String.intercalate "," (spec.keys.map (fun key => quoteName key.column ++ " COLLATE " ++ quoteName key.collation)) ++ ")"

end SQLeanite.CoreAutoIndexSpec
