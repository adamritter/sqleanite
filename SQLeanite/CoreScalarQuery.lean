import SQLeanite.CoreConnectionSQL

/-! Scalar SELECT evaluation with lexical outer bindings. The scalar evaluator
invokes the query callback lazily; a separate preparation pass checks every
captured query's names and width even in unexecuted branches. -/
namespace SQLeanite.CoreScalarQuery

structure Frame where
  context : CoreExpr.Context
  row : List Core.Value

def expressions (query : Select) : List Expr :=
  query.columns.toList.map (·.expr) ++ query.where_.toList ++
  query.groupBy.toList ++ query.having.toList ++ query.orderBy.toList.map (·.expr) ++
  query.sources.toList.flatMap (fun source => source.joinOn.toList ++
    (source.functionArgs.getD #[]).toList) ++
  (query.valueRows.getD #[]).toList.flatMap Array.toList

def captures : Nat → Expr → List String
  | 0, _ => []
  | fuel + 1, expression =>
      let visit := captures fuel
      match expression with
      | .scalarSubquery sql => [sql]
      | .unary _ arg | .isNull arg _ | .collate arg _ | .inSubquery arg _ _ => visit arg
      | .binary _ a b => visit a ++ visit b
      | .call _ args _ => args.toList.flatMap visit
      | .inList arg values _ _ => visit arg ++ values.toList.flatMap visit
      | .case_ base branches other => base.toList.flatMap visit ++
          branches.toList.flatMap (fun (a,b) => visit a ++ visit b) ++ other.toList.flatMap visit
      | _ => []

def has : Nat → Select → Bool
  | 0, _ => true
  | fuel + 1, query => (expressions query).any (fun expression =>
      !(captures expression.height expression).isEmpty) ||
      query.compounds.any (fun (_,query) => has fuel query)

def column? (ctx : CoreExpr.Context) (qualifier : Option String) (name : String) : Option Nat :=
  if ctx.schema.columns.isEmpty then none else ctx.column? qualifier name

def localContext (state : Core.State) (query : Select) : Except String CoreExpr.Context := do
  match query.sources.toList with
  | [] => return { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  | [source] =>
      let some table := CoreNames.table? state.database source.name | throw s!"no such table: {source.name}"
      return { schema := table.schema, sourceName := source.alias.getD source.name }
  | _ => throw "unsupported scalar-subquery source shape"

def outerValue (parents : List Frame) (qualifier : Option String) (name : String) : Except String (Option Expr) := do
  for frame in parents do
    if let some index := column? frame.context qualifier name then
      let some value := frame.row[index]? | throw "missing correlated row value"
      let some column := frame.context.schema.columns[index]? | throw "missing correlated column metadata"
      let value ← CoreExpr.value value
      return some (.call "__sqlean_bound_value"
        #[.literal value, .literal (.text (CoreCreateTableAs.declaredType column.affinity))] false)
  return none

def bind (ctx : CoreExpr.Context) (parents : List Frame) (aliases : List ResultColumn) :
    Nat → Expr → Except String Expr
  | 0, _ => .error "correlated expression nesting limit exceeded"
  | fuel + 1, expression => do
      let visit := bind ctx parents aliases fuel
      match expression with
      | .column qualifier name =>
          if (column? ctx qualifier name).isSome then return expression
          if qualifier.isNone && (CoreOrder.aliasExpression? aliases name).isSome then return expression
          return (← outerValue parents qualifier name).getD expression
      | .unary op arg => return .unary op (← visit arg)
      | .binary op a b => return .binary op (← visit a) (← visit b)
      | .call name args star =>
          if let some column := SQLite.Scalar.quotedIdentifier? expression then
            if (column? ctx none column).isNone then
              if let some value ← outerValue parents none column then return value
          return .call name (← args.mapM visit) star
      | .isNull arg negated => return .isNull (← visit arg) negated
      | .inList arg values negated affinity => return .inList (← visit arg) (← values.mapM visit) negated affinity
      | .collate arg name => return .collate (← visit arg) name
      | .case_ base branches other =>
          return .case_ (← base.mapM visit) (← branches.mapM fun (a,b) => return (← visit a, ← visit b)) (← other.mapM visit)
      | other => return other

def bindQuery (ctx : CoreExpr.Context) (parents : List Frame) (query : Select) : Except String Select := do
  let visit := fun aliases expr => bind ctx parents aliases (expr.height + 1) expr
  return { query with
    columns := ← query.columns.mapM fun column => return { column with expr := ← visit [] column.expr }
    where_ := ← query.where_.mapM (visit query.columns.toList)
    groupBy := ← query.groupBy.mapM (visit query.columns.toList)
    having := ← query.having.mapM (visit query.columns.toList)
    orderBy := ← query.orderBy.mapM fun order => return { order with expr := ← visit query.columns.toList order.expr } }

def parseQuery (sql : String) : Except String Select := do
  let parsed ← CoreTokenGrammar.parseCertified sql
  match parsed.statements.toList with
  | [.select query] => return query
  | [.values rows] => return {
      columns := (rows[0]?.getD #[]).mapIdx (fun i expr => { expr, alias := some s!"column{i+1}" })
      valueRows := some rows }
  | _ => throw "scalar subquery requires one SELECT"

structure TypedOutput where
  typed : List SQLite.ScalarValue
  values : List Core.Value
  keys : List Core.Value := []

def project (ctx : CoreExpr.Context) (row : List Core.Value) (expressions : List Expr) : Except String TypedOutput := do
  let typed ← expressions.mapM (ctx.evalTyped row)
  let values ← typed.mapM (fun value => SQLSurface.value value.value)
  return { typed, values }

def insert (directions : List CoreOrder.KeySpec) (row : TypedOutput) : List TypedOutput → List TypedOutput
  | [] => [row]
  | first :: rest => if CoreOrder.keysLess directions row.keys first.keys then row :: first :: rest
      else first :: insert directions row rest

/-- The existing bounded-sort projection order, retaining scalar subtype slots
until the SELECT value is consumed by its parent expression. -/
def scan (ctx : CoreExpr.Context) (expressions : List Expr) (terms : List OrderTerm)
    (distinct : Bool) (rows : List (List Core.Value)) (offset : Nat) (limit : Option Nat) :
    Except String (List TypedOutput) := do
  if limit == some 0 then return []
  let directions ← terms.mapM CoreOrder.specification
  let capacity := limit.map (· + offset)
  let mut sorted : List TypedOutput := []
  let mut seen : List (List Core.Value) := []
  for row in rows do
    let output ← if distinct || capacity.isNone then some <$> project ctx row expressions else pure none
    let key := output.map (fun output => Core.distinctRowKey output.values)
    if distinct && key.any (fun output => seen.any (CoreExpr.distinctEqual expressions output)) then continue
    if distinct then seen := key.toList ++ seen
    let keys ← ctx.projectRow row (terms.map (fun term => CoreOrder.keyExpression term.expr))
    if capacity.any (fun count => sorted.length ≥ count) &&
        sorted.getLast?.any (fun last => !CoreOrder.keysLess directions keys last.keys) then continue
    let output ← match output with
      | some output => pure output
      | none => project ctx row expressions
    sorted := insert directions { output with keys } sorted
    if let some count := capacity then sorted := sorted.take count
  return sorted.drop offset

structure Result where
  result : Core.Result
  width : Nat
  affinity : Option SQLite.Affinity
  firstTyped : Option SQLite.ScalarValue := none

structure Prepared where
  source : String
  query : Select
  affinity : Option SQLite.Affinity

/-- Explicit LIMIT 0 stays empty; otherwise a scalar SELECT stops at its first
row, retaining OFFSET and its ORDER BY semantics. -/
def scalarLimit (query : Select) : Select :=
  { query with limit := some (min 1 (query.limit.getD 1)) }

def execute : Nat → Core.State → List Frame → Select → Except String Result
  | 0, _, _, _ => .error "scalar subquery nesting limit exceeded"
  | fuel + 1, state, parents, original => do
      let original := CoreConnectionSQL.select state original.compoundHeight original
      let ctx ← localContext state original
      let query ← bindQuery ctx parents original
      let columns ← CoreOrder.expandResults ctx query.columns.toList
      let width := if let some rows := query.valueRows then (rows[0]?.getD #[]).size else columns.length
      let scalarShape := query.valueRows.isNone && query.groupBy.isEmpty && query.having.isNone &&
        query.compounds.isEmpty && !(query.columns.any (fun col => CoreAggregate.containsAggregate col.expr))
      if !has query.compoundHeight query && !scalarShape then
        let selected ← CoreSQL.executeSelect state query
        let context ← CoreCreateTableAs.contexts state.database query
        return {
          result := selected.result
          width := selected.width
          affinity := columns.head?.bind (fun column => CoreCreateTableAs.affinity context column.expr) }
      unless query.valueRows.isNone && query.groupBy.isEmpty && query.having.isNone && query.compounds.isEmpty do
        throw "unsupported scalar-subquery grouping or compound shape"
      let dummy : Frame := { context := ctx, row := List.replicate ctx.schema.columns.length .null }
      let sources := (expressions query).flatMap (fun expression => captures expression.height expression)
      let mut prepared : List Prepared := []
      for sql in sources do
        unless prepared.any (fun entry => entry.source == sql) do
          let inner ← parseQuery sql
          let validated ← execute fuel state (dummy :: parents) { inner with limit := some 0 }
          unless validated.width == 1 do
            throw s!"sub-select returns {validated.width} columns - expected 1"
          prepared := prepared ++ [{ source := sql, query := inner, affinity := validated.affinity }]
      let evaluateQuery := fun row sql => do
        let some entry := prepared.find? (fun entry => entry.source == sql) | throw "unprepared scalar subquery"
        let result ← execute fuel state ({ context := ctx, row } :: parents) (scalarLimit entry.query)
        if let some value := result.firstTyped then return value
        let value := ((result.result.rows.head?).bind List.head?).getD .null
        SQLite.Scalar.plainScalar <$> CoreExpr.value value
      let preparedContext := { ctx with
        scalarQuery := some evaluateQuery
        queryAffinity := fun sql => (prepared.find? (fun entry => entry.source == sql)).bind (·.affinity) }
      let ordering ← CoreOrder.resolve preparedContext columns query.orderBy.toList
      let condition := query.where_.map (CoreOrder.resolveAliases preparedContext columns)
      let projected := columns.map (·.expr)
      for expression in projected ++ ordering.map (·.expr) ++ condition.toList do
        if let some message := SQLite.Scalar.resolutionError
            (fun qualifier name => (column? ctx qualifier name).isSome) expression then throw message
        preparedContext.validate expression
      let affinity := columns.head?.bind fun column => preparedContext.affinity column.expr
      if query.limit == some 0 then return { result := {}, width, affinity }
      let rows ← if query.sources.isEmpty then pure [[]] else do
        let (_, result) ← Core.execute state (.query ctx.schema.name { columns := List.range ctx.schema.columns.length })
        pure result.rows
      let filtered ← rows.filterM fun row => do
        match condition with
        | none => pure true
        | some expression =>
            let expression := SQLite.Scalar.prepare (preparedContext.bindNames expression)
            SQLite.Scalar.testEvaluatedFuel (preparedContext.eval row) preparedContext.affinity true
              expression.height true expression
      let result ← scan preparedContext projected ordering query.distinct filtered query.offset query.limit
      return {
        result := { rows := result.map (·.values) }
        width
        affinity
        firstTyped := result.head?.bind (fun row => row.typed.head?) }

theorem scalarLimit_zero (query : Select) (zero : query.limit = some 0) :
    (scalarLimit query).limit = some 0 := by simp [scalarLimit, zero]

end SQLeanite.CoreScalarQuery
