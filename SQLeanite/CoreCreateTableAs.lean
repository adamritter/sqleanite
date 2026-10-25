import SQLeanite.CoreJoinUsing
import SQLeanite.CoreExpr
import SQLeanite.CoreNames

/-! CREATE TABLE AS SELECT metadata, from SQLite select.c's column-name and
subquery-affinity derivation. Source evaluation and storage are separate Core
operations; this module only derives unconstrained visible columns. -/
namespace SQLeanite.CoreCreateTableAs

structure ColumnInfo where
  name : String
  affinity : Option SQLite.Affinity
  dataTypes : Nat
  cast : Bool := false

structure Context where
  sources : List CoreExpr.Context
  shared : List CoreJoinUsing.Column := []

def contexts (database : Core.Database) (query : Select) : Except String Context := do
  let sources ← query.sources.toList.mapM fun source => do
    let some table := CoreNames.table? database source.name | throw s!"no such table: {source.name}"
    pure ({ schema := table.schema, sourceName := source.alias.getD source.name } : CoreExpr.Context)
  let shared ← match sources, query.sources.toList with
    | [left, right], [_, source] => CoreJoinUsing.columns left.schema right.schema source
    | _, _ => pure []
  return { sources, shared }

def column? (context : Context) (qualifier : Option String) (name : String) :
    Option (String × SQLite.Affinity) :=
  match context.sources.zipIdx.filterMap (fun (source, sourceIndex) => do
    let position ← source.column? qualifier name
    if qualifier.isNone && sourceIndex == 1 &&
        CoreJoinUsing.suppressesName context.shared name position then none
    else do
      let column ← source.schema.columns[position]?
      let name := if source.schema.hasHiddenRowid && position == source.schema.primaryKey then
        "rowid" else column.name
      some (name, column.affinity)) with
  | [column] => some column
  | _ => none

def bindNames (context : Context) (expression : Expr) : Expr :=
  SQLite.Scalar.bindNames (fun name => (column? context none name).isSome) expression

def affinity (context : Context) (expression : Expr) : Option SQLite.Affinity :=
  match SQLite.ExprCollation.strip expression with
  | .column qualifier name => (column? context qualifier name).map Prod.snd
  | expression => SQLite.Scalar.expressionAffinity expression

def nameExpression : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression => match expression with
      | .collate inner _ => nameExpression fuel inner
      | .call name arguments false =>
          if ["likely", "unlikely", "likelihood"].contains name.toLower then
            match arguments[0]? with
            | some inner => nameExpression fuel inner
            | none => expression
          else expression
      | _ => expression

def affinityMask (affinity : Option SQLite.Affinity) : Nat :=
  match affinity with
  | some .integer | some .real | some .numeric => 5
  | some .text => 6
  | _ => 7

/-- expr.c sqlite3ExprDataType, restricted to the expressions the Core executes.
Bits 1/2/4 indicate numeric/text/blob possibilities, respectively. -/
def dataTypes : Nat → Context → Expr → Nat
  | 0, _, _ => 7
  | fuel + 1, context, expression => match expression with
      | .collate inner _ | .unary .plus inner => dataTypes fuel context inner
      | .literal .null _ => 0
      | .literal (.text _) _ | .literal (.textBytes _) _ => 2
      | .literal (.blob _) _ => 4
      | .binary .concat _ _ => 6
      | .column .. => affinityMask (affinity context expression)
      | .call name _ _ =>
          if name.toLower.startsWith "cast_" then affinityMask (affinity context expression)
          else if (SQLite.Scalar.booleanKeyword? expression).isSome then 1 else 7
      | .case_ _ branches otherwise =>
          branches.toList.foldl (fun mask pair => mask ||| dataTypes fuel context pair.2)
            ((otherwise.map (dataTypes fuel context)).getD 0)
      | .scalarSubquery _ => 7
      | _ => 1

def resultColumn (context : Context) (position : Nat) (column : ResultColumn) : ColumnInfo :=
  let expression := bindNames context column.expr
  let named := nameExpression expression.height expression
  let inherited := match named with
    | .column qualifier name => (column? context qualifier name).map Prod.fst
    | _ => none
  let name := column.alias.getD (inherited.getD (column.sourceSql.getD column.expr.sql))
  let name := if ["true", "false"].contains name.toLower then s!"column{position + 1}" else name
  { name, affinity := affinity context expression,
    dataTypes := dataTypes expression.height context expression,
    cast := match SQLite.ExprCollation.strip expression with
      | .call name _ false => name.toLower.startsWith "cast_"
      | _ => false }

def baseColumns (database : Core.Database) (query : Select) : Except String (List ColumnInfo) := do
  let context ← contexts database query
  let mut output := []
  for column in query.columns do
    match column.expr with
    | .star qualifier =>
        let sources := context.sources.zipIdx.filter fun (source, _) =>
          qualifier.all (fun name => name.toLower == source.sourceName.toLower)
        if sources.isEmpty then throw "no such table in CTAS star"
        for (source, sourceIndex) in sources do
          for index in source.schema.visibleColumnIndices do
            if qualifier.isNone && sourceIndex == 1 &&
                CoreJoinUsing.suppressesRight context.shared index then continue
            let some stored := source.schema.columns[index]? | throw "invalid CTAS source column"
            let derived := resultColumn context output.length
              { expr := .column (some source.sourceName) stored.name }
            output := output ++ [derived]
    | _ => output := output ++ [resultColumn context output.length column]
  return output

def armColumns : Nat → Core.Database → Select → Except String (List (List ColumnInfo))
  | 0, _, _ => .error "CTAS compound depth exceeded"
  | fuel + 1, database, query => do
      let first ← baseColumns database query
      let rest ← query.compounds.toList.mapM fun arm => armColumns fuel database arm.2
      return first :: rest.flatten

def compoundAffinity (columns : List ColumnInfo) : SQLite.Affinity := Id.run do
  let chosen := (columns.findIdx? (·.affinity.isSome)).getD (columns.length - 1)
  let selected := ((columns[chosen]?).bind (·.affinity)).getD .blob
  if columns.length ≤ 1 then return selected
  let others := columns.take chosen ++ columns.drop (chosen + 1)
  let possibilities := others.foldl (fun mask column => mask ||| column.dataTypes) 0
  if selected == .text && possibilities &&& 1 != 0 then return .blob
  if selected.isNumeric && possibilities &&& 2 != 0 then return .blob
  if selected.isNumeric && (columns.head?).any (·.cast) then return .numeric
  return selected

def declaredType : SQLite.Affinity → String
  | .integer => "INT"
  | .text => "TEXT"
  | .numeric => "NUM"
  | .real => "REAL"
  | .blob => ""

/-- SQLite removes a trailing colon plus digits before adding the next suffix. -/
def collisionBase (name : String) : String :=
  match name.toList.reverse.dropWhile Char.isDigit with
  | ':' :: rest => String.ofList rest.reverse
  | _ => name

/-- SQLite switches to a random suffix after four collisions. Until a seeded
random-name source is represented, that case is rejected explicitly. -/
def uniqueName (seen : List String) : Nat → Nat → String → Except String String
  | 0, _, _ => .error "CTAS column-name collision limit"
  | fuel + 1, count, name =>
      if !(seen.any fun previous => previous.toLower == name.toLower) then .ok name
      else if 4 ≤ count then .error "unsupported randomized CTAS column name"
      else uniqueName seen fuel (count + 1) (collisionBase name ++ ":" ++ toString (count + 1))

def columns (database : Core.Database) (query : Select) : Except String (Array ColumnDef) := do
  let groups ← armColumns query.compoundHeight database query
  let first := groups.headD []
  let mut names := []
  let mut output := #[]
  for (column, position) in first.zipIdx do
    let corresponding ← groups.mapM fun group =>
      match group[position]? with
      | some column => pure column
      | none => throw "CTAS compound column width mismatch"
    let name ← uniqueName names 6 0 column.name
    names := names ++ [name]
    output := output.push { name, declaredType := declaredType (compoundAffinity corresponding) }
  if output.isEmpty || output.size > 2000 then throw "too many or no CTAS columns"
  return output

theorem uniqueName_unoccupied (seen : List String) (fuel count : Nat) (name : String)
    (fresh : seen.any (fun previous => previous.toLower == name.toLower) = false) :
    uniqueName seen (fuel + 1) count name = .ok name := by
  simp [uniqueName, fresh]

end SQLeanite.CoreCreateTableAs
