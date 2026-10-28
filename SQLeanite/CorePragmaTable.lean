import SQLeanite.CoreConnectionSQL

namespace SQLeanite.CorePragmaTable

/-- PRAGMA virtual-table output columns have no declared affinity. -/
def names (name : String) : Option (List String) :=
  match name.toLower with
  | "pragma_foreign_keys" => some ["foreign_keys"]
  | "pragma_table_list" => some ["schema", "name", "type", "ncol", "wr", "strict"]
  | "pragma_table_info" => some ["cid", "name", "type", "notnull", "dflt_value", "pk"]
  | "pragma_table_xinfo" => some ["cid", "name", "type", "notnull", "dflt_value", "pk", "hidden"]
  | "pragma_index_list" => some ["seq", "name", "unique", "origin", "partial"]
  | "pragma_index_info" => some ["seqno", "cid", "name"]
  | "pragma_index_xinfo" => some ["seqno", "cid", "name", "desc", "coll", "key"]
  | "pragma_pragma_list" => some ["name"]
  | "pragma_foreign_key_list" => some ["id", "seq", "table", "from", "to", "on_update", "on_delete", "match"]
  | "pragma_foreign_key_check" => some ["table", "rowid", "parent", "fkid"]
  | _ => none

structure Result where
  columns : Array ColumnDef
  rows : List (List Core.Value)
  hidden : List (String × Value)
  zeroRowid : Bool := false
  jsonValues : Bool := false

/-- Arguments are scalar expressions, unlike the token-like arguments of a
PRAGMA statement. NULL arguments produce no target rows. -/
def executeWith (inspect : Core.State → Option String → String → Option String → Except String (List (List Value)))
    (state : Core.State) (name : String) (arguments : Array Expr) : Except String Result := do
  let some fields := names name | throw s!"no such table: {name}"
  if state.schemaProgram then throw s!"unsafe use of virtual table \"{name}\""
  let scalar := name.toLower == "pragma_foreign_keys"
  let listing := name.toLower == "pragma_pragma_list"
  let tables := name.toLower == "pragma_table_list"
  let maximum := if listing || scalar then 0 else if tables then 1 else 2
  if arguments.size > maximum then
    throw s!"too many arguments on {name}() - max {maximum}"
  let columns : Array ColumnDef := (fields.map fun name => { name }).toArray
  let values ← arguments.mapM fun expression => do
    let expression := CoreConnectionSQL.expression state expression
    if let some message := SQLite.Scalar.resolutionError (fun _ _ => false) expression then throw message
    SQLite.Scalar.eval expression
  let strings ← values.mapM fun value => do
    if SQLite.Text.isNull value then return none
    return some (String.ofList (SQLite.Text.nulPrefix (← SQLite.Scalar.text value)))
  let schema := strings[1]?.getD none
  if schema.any (fun name => !["main", "temp"].contains name.toLower) then
    throw s!"unknown database '{schema.getD ""}'"
  let target := strings[0]?.getD none
  let rows ← if scalar then pure [[.integer (if state.foreignKeys then 1 else 0)]]
    else if listing then pure CoreSchemaPragma.pragmaListRows
    else inspect state schema (String.ofList (name.toLower.toList.drop 7)) target
  let hidden := if listing || scalar then [] else
    [("arg", (target.map Value.text).getD .null)] ++
      (if tables then [] else [("schema", (schema.map Value.text).getD .null)])
  return { columns, rows := ← rows.mapM (List.mapM SQLSurface.value), hidden }

/-- Only an actually resolved PRAGMA virtual table is subject to DIRECTONLY;
physical tables with the same spelling follow the ordinary table path. -/
theorem executeWith_schemaProgram
    (inspect : Core.State → Option String → String → Option String → Except String (List (List Value)))
    (state : Core.State) (name : String) (arguments : Array Expr) (fields : List String)
    (known : names name = some fields) (program : state.schemaProgram = true) :
    executeWith inspect state name arguments = .error s!"unsafe use of virtual table \"{name}\"" := by
  simp [executeWith, known, program]
  rfl

def execute (state : Core.State) (name : String) (arguments : Array Expr) : Except String Result :=
  executeWith (fun state schema name target => CoreSchemaPragma.inspectionRows state.database schema
    name target (state.schemaHash.map (·.names))) state name arguments

structure HiddenSource where
  alias : String
  values : List (String × Value)
  jsonValues : Bool := false

/-- Hidden virtual-table arguments participate in name resolution but not star
expansion. Guard with the source rowid so an outer join's null extension also
nulls the hidden fields. -/
def hiddenExpr (database : Core.Database) (sources : Array TableRef)
    (hidden : List HiddenSource) : Nat → Expr → Except String Expr
  | 0, _ => .error "table-function expression nesting limit exceeded"
  | fuel + 1, expr => do
      let visit := hiddenExpr database sources hidden fuel
      match expr with
      | .column qualifier name =>
          let jsonSources := hidden.filter fun source => source.jsonValues && name.toLower == "value" &&
            !qualifier.any (fun q => q.toLower != source.alias.toLower)
          unless jsonSources.isEmpty do
            let context ← CoreCreateTableAs.contexts database { columns := #[], sources }
            let physical := CoreJoinUsing.nameCandidates context.sources qualifier name
            unless physical.length == 1 && jsonSources.length == 1 do throw s!"ambiguous column name: {name}"
            let some source := jsonSources.head? | throw "missing JSON value binding"
            let value := Expr.column (some source.alias) "value"
            let container := Expr.inList (.column (some source.alias) "type")
              #[.literal (.text "array"), .literal (.text "object")] false true
            return .case_ none #[(container,.call "json" #[value] false)] (some value)
          let candidates := hidden.flatMap fun source =>
            if qualifier.any (fun q => q.toLower != source.alias.toLower) then []
            else source.values.filterMap fun (field,value) =>
              if field == name.toLower then some (source.alias,value) else none
          if candidates.isEmpty then return expr
          let context ← CoreCreateTableAs.contexts database { columns := #[], sources }
          let physical := CoreJoinUsing.nameCandidates context.sources qualifier name
          unless physical.isEmpty && candidates.length == 1 do throw s!"ambiguous column name: {name}"
          let some (alias,value) := candidates.head? | throw "missing virtual column binding"
          return .case_ none #[(.isNull (.column (some alias) "rowid") false, .literal .null)]
            (some (.literal value))
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

def bindHidden (database : Core.Database) (hidden : List HiddenSource) (query : Select) :
    Except String Select := do
  if hidden.isEmpty then return query
  let query ← if query.sources.size == 1 && hidden.any (·.jsonValues) then do
      let context ← CoreCreateTableAs.contexts database query
      let some source := context.sources[0]? | throw "missing JSON source"
      let columns := query.columns.toList.flatMap fun column => match column.expr with
        | .star qualifier =>
            if qualifier.any (fun q => q.toLower != source.sourceName.toLower) then [column]
            else source.schema.catalogColumns.map fun c =>
              { expr := .column (some source.sourceName) c.name, alias := some c.name }
        | _ => [column]
      pure { query with columns := columns.toArray }
    else pure query
  let bind := fun expr => hiddenExpr database query.sources hidden expr.height expr
  return { query with
    columns := ← query.columns.mapM fun col => return { col with expr := ← bind col.expr }
    where_ := ← query.where_.mapM bind
    groupBy := ← query.groupBy.mapM bind
    having := ← query.having.mapM bind
    orderBy := ← query.orderBy.mapM fun (term : OrderTerm) => do
      let alias := match term.expr with
        | .column none name => query.columns.any (fun (col : ResultColumn) => col.alias.any (fun (a : String) => a.toLower == name.toLower))
        | _ => false
      let expr ← if alias then pure term.expr else bind term.expr
      return { term with expr }
    sources := ← query.sources.mapM fun source => return { source with joinOn := ← source.joinOn.mapM bind } }

theorem bindHidden_empty (database : Core.Database) (query : Select) :
    bindHidden database [] query = .ok query := by
  simp [bindHidden, pure, Except.pure]

end SQLeanite.CorePragmaTable
