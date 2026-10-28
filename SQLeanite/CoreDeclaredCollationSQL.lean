import SQLeanite.CoreSQL

namespace SQLeanite.CoreDeclaredCollationSQL

structure Context where
  core : CoreExpr.Context
  declarations : List CoreCollationSyntax.Spec
  qualifiedOnly : Bool := false

def tableContext (table : Core.Table) (name : String) : Except String Context := do
  let declarations ← match table.catalogSource with
    | none => pure []
    | some source => source.compiledCollations
  return { core := { schema := table.schema, sourceName := name }, declarations }

def contexts (state : Core.State) (sources : Array TableRef) : Except String (List Context) := do
  let mut result := []
  for source in sources do
    if let some table := CoreNames.table? state.database source.name then
      result := result ++ [← tableContext table (source.alias.getD source.name)]
  return result

def lookup (frames : List Context) (qualifier : Option String) (name : String) : Option String := do
  let candidates := frames.filterMap fun frame => do
    if qualifier.isNone && frame.qualifiedOnly then none else do
      let position ← frame.core.column? qualifier name
      return (frame,position)
  let [(frame,position)] := candidates | none
  let column ← frame.core.schema.columns[position]?
  let declaration ← frame.declarations.find? (fun spec => spec.1.toLower == column.name.toLower)
  return declaration.2

def expression (frames : List Context) (value : Expr) : Expr :=
  CoreCollationSyntax.annotate (lookup frames) value

def tableUses (table : Core.Table) : Bool :=
  table.catalogSource.any fun source => match source.compiledCollations with
    | .ok declarations => !declarations.isEmpty
    | .error _ => true

def usesFuel : Nat → Core.State → Select → Bool
  | 0, _, _ => false
  | fuel + 1, state, query =>
      query.sources.any (fun source => (CoreNames.table? state.database source.name).any tableUses) ||
        query.compounds.any (fun (_,arm) => usesFuel fuel state arm)

def uses (state : Core.State) (query : Select) : Bool := usesFuel query.compoundHeight state query

def selectFuel : Nat → Core.State → Select → Except String Select
  | 0, _, _ => .error "declared collation query nesting limit exceeded"
  | fuel + 1, state, query => do
      let frames ← contexts state query.sources
      if frames.any (fun frame => !frame.declarations.isEmpty) &&
          query.sources.any (fun source => !source.usingColumns.isEmpty || source.naturalJoin) then
        throw "unsupported general verified-MVP SQL: declared collation USING join"
      let visit := expression frames
      let mut columns := #[]
      for column in query.columns do
        match column.expr with
        | .star qualifier =>
            if frames.any (fun frame => !frame.declarations.isEmpty) then
              for frame in frames do
                unless qualifier.all (fun name => name.toLower == frame.core.sourceName.toLower) do continue
                for position in frame.core.schema.visibleColumnIndices do
                  if let some definition := frame.core.schema.columns[position]? then
                    columns := columns.push {
                      expr := visit (.column (some frame.core.sourceName) definition.name)
                      alias := some definition.name
                      sourceSql := some definition.name }
            else columns := columns.push column
        | _ => columns := columns.push { column with expr := visit column.expr }
      let compounds ← query.compounds.mapM fun (operation,arm) => do
        return (operation, ← selectFuel fuel state arm)
      return { query with
        columns
        where_ := query.where_.map visit
        groupBy := query.groupBy.map visit
        having := query.having.map visit
        orderBy := query.orderBy.map fun term => { term with expr := visit term.expr }
        sources := query.sources.map fun source => { source with joinOn := source.joinOn.map visit }
        compounds }

def select (state : Core.State) (query : Select) : Except String Select :=
  selectFuel query.compoundHeight state query

def returning (frame : Context) (columns : Array ResultColumn) : Array ResultColumn :=
  columns.map fun column => { column with expr := expression [frame] column.expr }

def statement (state : Core.State) : Statement → Except String Statement
  | .select query => .select <$> select state query
  | .insert name columns rows policy output => do
      let some table := CoreNames.table? state.database name | return .insert name columns rows policy output
      let frame ← tableContext table table.schema.name
      return .insert name columns rows policy (returning frame output)
  | .insertSelect name columns query policy output => do
      let some table := CoreNames.table? state.database name | return .insertSelect name columns query policy output
      let frame ← tableContext table table.schema.name
      return .insertSelect name columns (← select state query) policy (returning frame output)
  | .update name alias assignments condition policy output => do
      let some table := CoreNames.table? state.database name | return .update name alias assignments condition policy output
      let frame ← tableContext table (alias.getD table.schema.name)
      let result ← tableContext table table.schema.name
      let visit := expression [frame]
      return .update name alias (assignments.map fun (name,value) => (name,visit value))
        (condition.map visit) policy (returning result output)
  | .delete name alias condition output => do
      let some table := CoreNames.table? state.database name | return .delete name alias condition output
      let frame ← tableContext table (alias.getD table.schema.name)
      let result ← tableContext table table.schema.name
      return .delete name alias (condition.map (expression [frame])) (returning result output)
  | .upsert base alias clauses => do
      let base ← statement state base
      let name := match base with | .insert name .. | .insertSelect name .. => some name | _ => none
      let some name := name | return .upsert base alias clauses
      let some table := CoreNames.table? state.database name | return .upsert base alias clauses
      let frame ← tableContext table (alias.getD table.schema.name)
      let excluded ← tableContext table "excluded"
      let visit := expression [frame, { excluded with qualifiedOnly := true }]
      return .upsert base alias (clauses.map fun clause => { clause with
        assignments := clause.assignments.map (·.map fun (name,value) => (name,visit value))
        where_ := clause.where_.map visit })
  | .createTableAs name query guard => do
      return .createTableAs name (← select state query) guard
  | other => .ok other

theorem tableUses_canonical (table : Core.Table) (canonical : table.catalogSource = none) :
    tableUses table = false := by simp [tableUses, canonical]

end SQLeanite.CoreDeclaredCollationSQL
