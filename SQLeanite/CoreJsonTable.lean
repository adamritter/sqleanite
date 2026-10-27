import SQLeanite.CorePragmaTable
import SQLeanite.SQLite.JsonTable

namespace SQLeanite.CoreJsonTable

def supported (name : String) : Bool :=
  ["json_each", "json_tree"].contains name.toLower

def execute (state : Core.State) (name : String) (arguments : Array Expr) :
    Except String CorePragmaTable.Result := do
  unless supported name do throw s!"no such table: {name}"
  if arguments.size > 2 then throw s!"too many arguments on {name}() - max 2"
  let columns : Array ColumnDef := #["key", "value", "type", "atom", "id", "parent", "fullkey", "path"].map
    fun name => { name }
  let values ← arguments.mapM fun expression => do
    let expression := CoreConnectionSQL.expression state expression
    if let some message := SQLite.Scalar.resolutionError (fun _ _ => false) expression then throw message
    SQLite.Scalar.eval expression
  let input := values[0]?.getD .null
  let path := values[1]?
  let rows ← SQLite.JsonTable.evaluate (name.toLower == "json_tree") input path
  let original := match input with
    | .blob bytes => if SQLite.JsonValid.blobLooks bytes then input else
        SQLite.Text.fromBytes (SQLite.JsonExtract.nulPrefix (SQLite.Text.bytes input))
    | _ => if SQLite.Text.isNull input then Value.null else
        SQLite.Text.fromBytes (SQLite.JsonExtract.nulPrefix (SQLite.Text.bytes input))
  let root := path.map (fun value => if SQLite.Text.isNull value then Value.null else
    SQLite.Text.fromBytes (SQLite.JsonExtract.nulPrefix (SQLite.Text.bytes value))) |>.getD (.text "$")
  return {
    columns := columns
    rows := ← rows.mapM (List.mapM SQLSurface.value)
    hidden := [("json", original), ("root", root)]
    zeroRowid := true
    jsonValues := true }

/-- A simple projection of a JSON virtual table can be flattened. Materialized
and compound sources deliberately retain their subtype-erasing boundary. -/
def flattenableFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel+1, query =>
      query.sources.size == 1 && query.sources[0]?.any (fun source =>
        if source.functionArgs.isSome then supported (match source.schema with
          | none => source.name
          | some schema => String.ofList (source.name.toList.drop (schema.length+1)))
        else match source.subquerySql with
          | none => false
          | some sql => match CoreTokenGrammar.parseCertified sql with
            | .error _ => false
            | .ok parsed => match parsed.statements.toList with
              | [.select inner] => flattenableFuel fuel inner
              | _ => false) &&
      query.valueRows.isNone && query.compounds.isEmpty && query.orderBy.isEmpty &&
      query.groupBy.isEmpty && query.having.isNone && !query.distinct &&
      query.limit.isNone && query.offset == 0 &&
      !query.columns.any (fun col => (SQLite.Scalar.aggregateMisuse col.expr).isSome)

def flattenable (query : Select) : Bool := flattenableFuel 256 query

/-- Computed TEXT crossing a SELECT boundary loses its JSON subtype, even when
the surrounding query is flattened. Concatenation preserves its bytes; other
storage classes retain their values. Admitted expressions here are pure. -/
def clearTextSubtype (expression : Expr) : Expr :=
  .case_ none #[
    (.binary .eq (.call "typeof" #[expression] false) (.literal (.text "text")),
      .binary .concat expression (.literal (.text "")))] (some expression)

def inlineExpr (source : TableRef) (bindings : List (String × Expr))
    (aliases : Array ResultColumn) : Nat → Expr → Except String Expr
  | 0, _ => .error "flattened expression nesting limit exceeded"
  | fuel+1, expr => do
      let visit := inlineExpr source bindings aliases fuel
      match expr with
      | .column qualifier name =>
          if qualifier.any (fun q => q.toLower != (source.alias.getD source.name).toLower) then
            throw s!"no such column: {(qualifier.map (· ++ ".")).getD ""}{name}"
          if let some (_,value) := bindings.find? (fun pair => pair.1.toLower == name.toLower) then return value
          if qualifier.isNone then
            if let some column := aliases.find? (fun col => col.alias.any (fun a => a.toLower == name.toLower)) then
              return ← inlineExpr source bindings #[] fuel column.expr
          throw s!"no such column: {(qualifier.map (· ++ ".")).getD ""}{name}"
      | .unary op arg => return .unary op (← visit arg)
      | .binary op a b => return .binary op (← visit a) (← visit b)
      | .call name args star => return .call name (← args.mapM visit) star
      | .isNull arg negated => return .isNull (← visit arg) negated
      | .inList arg values negated affinity => return .inList (← visit arg) (← values.mapM visit) negated affinity
      | .collate arg name => return .collate (← visit arg) name
      | .case_ base branches other =>
          return .case_ (← base.mapM visit) (← branches.mapM fun (a,b) => return (← visit a, ← visit b)) (← other.mapM visit)
      | .inSubquery arg sql negated => return .inSubquery (← visit arg) sql negated
      | other => return other

def inlineProjection (state : Core.State) (outer inner : Select) (source : TableRef) (original : Select) :
    Except String Select := do
  let definitions ← CoreCreateTableAs.columns state.database inner
  unless definitions.size == inner.columns.size && inner.columns.all (fun col => match col.expr with
      | .star _ => false | _ => true) do throw "unsupported flattened JSON projection"
  let stars := original.columns.toList.countP (fun col => match col.expr with | .star _ => true | _ => false)
  let starWidth := if stars == 0 then 0 else (definitions.size - (original.columns.size-stars)) / stars
  let direct := original.columns.toList.flatMap fun col => match col.expr with
    | .star _ => List.replicate starWidth true
    | .column .. => [true]
    | _ => [false]
  unless direct.length == definitions.size do throw "flattened projection width mismatch"
  let bindings := (definitions.toList.zip inner.columns.toList).zip direct |>.map fun ((col,result),direct) =>
    let expression := if direct then result.expr else clearTextSubtype result.expr
    let expression := if !direct && !col.declaredType.isEmpty then
        Expr.call ("cast_" ++ col.declaredType) #[expression] false
      else expression
    (col.name,expression)
  let aliasHeight := outer.columns.foldl (fun n col => max n col.expr.height) 0
  let bind := fun aliases expr => inlineExpr source bindings aliases (expr.height+aliasHeight+2) expr
  let mut columns := #[]
  for column in outer.columns do
    match column.expr with
    | .star qualifier =>
        if qualifier.any (fun q => q.toLower != (source.alias.getD source.name).toLower) then
          throw "no such table or alias in qualified star"
        for (name,expr) in bindings do columns := columns.push { expr, alias := some name }
    | _ => columns := columns.push { column with expr := ← bind #[] column.expr }
  let condition ← outer.where_.mapM (bind outer.columns)
  let condition := match inner.where_,condition with
    | none, condition => condition
    | condition, none => condition
    | some a, some b => some (.binary .and a b)
  return { outer with
    columns := columns
    sources := inner.sources
    where_ := condition
    groupBy := ← outer.groupBy.mapM (bind outer.columns)
    having := ← outer.having.mapM (bind outer.columns)
    orderBy := ← outer.orderBy.mapM fun (term : OrderTerm) => do
      let alias : Bool := match term.expr with
        | .column none name => outer.columns.any (fun col => col.alias.any (fun a => a.toLower == name.toLower))
        | _ => false
      let expr ← if alias then pure term.expr else bind outer.columns term.expr
      return { term with expr } }

end SQLeanite.CoreJsonTable
