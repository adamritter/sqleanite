import SQLeanite.CoreConnectionSQL

/-! Read-only single-source window evaluation. Window frames run after WHERE
and before projection, DISTINCT, final ordering and LIMIT. -/
namespace SQLeanite.CoreWindow

def node : Expr → Bool
  | .call "__sqlean_window" _ false => true
  | _ => false

def has (query : Select) : Bool :=
  query.columns.any (fun col => col.expr.any node) ||
  query.orderBy.any (fun term => term.expr.any node) ||
  query.where_.any (fun expression => expression.any node) ||
  query.groupBy.any (fun expression => expression.any node) ||
  query.having.any (fun expression => expression.any node)

structure Term where
  name : String
  function : Expr
  specification : WindowSpec

abbrev Collect := StateT (Array Term) (Except String)

def replace (schema : Core.Schema) : Nat → Expr → Collect Expr
  | 0, _ => throw "window expression nesting limit exceeded"
  | fuel + 1, expression => do
      let visit := replace schema fuel
      match expression with
      | .call "__sqlean_window" #[function, .literal (.text source) none] false =>
          let terms ← get
          let candidates := List.range (schema.columns.length + terms.size + 1)
          let some index := candidates.find? (fun index =>
              let name := s!"__sqlean_window_value_{index}"
              (schema.column? name).isNone && !terms.any (fun term => term.name == name))
            | throw "cannot allocate a window column"
          let name := s!"__sqlean_window_value_{index}"
          let specification ← parseWindowSpec source
          set (terms.push { name, function, specification })
          return .column none name
      | .unary op arg => return .unary op (← visit arg)
      | .binary op a b => return .binary op (← visit a) (← visit b)
      | .call name args star => return .call name (← args.mapM visit) star
      | .isNull arg negated => return .isNull (← visit arg) negated
      | .inList arg values negated affinity => return .inList (← visit arg) (← values.mapM visit) negated affinity
      | .collate arg name => return .collate (← visit arg) name
      | .case_ base branches other =>
          return .case_ (← base.mapM visit) (← branches.mapM fun (a,b) => return (← visit a, ← visit b)) (← other.mapM visit)
      | other => return other

structure Input where
  index : Nat
  row : List Core.Value
  partition : List Core.Value
  keys : List Core.Value

def insert (directions : List CoreOrder.KeySpec) (row : Input) : List Input → List Input
  | [] => [row]
  | first :: rest =>
      if CoreOrder.keysLess directions row.keys first.keys then row :: first :: rest
      else first :: insert directions row rest

def equivalent (directions : List CoreOrder.KeySpec) (a b : List Core.Value) : Bool :=
  !CoreOrder.keysLess directions a b && !CoreOrder.keysLess directions b a

def offset (expression : Expr) (first : Bool) : Except String Nat := do
  let message := if first then "frame starting offset must be a non-negative integer"
    else "frame ending offset must be a non-negative integer"
  let value ← match SQLite.Limit.evaluate expression with
    | .ok value => pure value | .error _ => throw message
  if value < 0 then throw message
  return value.toNat

def bound (position count : Nat) (first : Bool) : WindowBound → Except String Int
  | .unboundedPreceding => .ok 0
  | .unboundedFollowing => .ok (Int.ofNat count - 1)
  | .current => .ok position
  | .preceding expression => do return Int.ofNat position - Int.ofNat (← offset expression first)
  | .following expression => do return Int.ofNat position + Int.ofNat (← offset expression first)

def frameRange (specification : WindowSpec) (directions : List CoreOrder.KeySpec)
    (partition : List Input) (position : Nat) : Except String (Nat × Nat) := do
  if specification.kind == "rows" then
    let first ← bound position partition.length true specification.first
    let last ← bound position partition.length false specification.last
    return (min partition.length first.toNat, min partition.length (last + 1).toNat)
  unless !specification.explicitFrame do throw "unsupported explicit RANGE/GROUPS window frame"
  let some current := partition[position]? | throw "window position outside partition"
  return (0, (partition.takeWhile fun row => !CoreOrder.keysLess directions current.keys row.keys).length)

def frame (specification : WindowSpec) (directions : List CoreOrder.KeySpec)
    (partition : List Input) (position : Nat) : Except String (List (List Core.Value)) := do
  let (first, stop) ← frameRange specification directions partition position
  return ((partition.drop first).take (stop - first)).map (·.row)

/-- The ordered SUM/AVG/TOTAL accumulator advances monotonically across a
partition. FILTER and argument expressions are evaluated once per input. -/
def numericPartition (ctx : CoreExpr.Context) (term : Term) (aggregate : CoreAggregate.Term)
    (directions : List CoreOrder.KeySpec) (partition : List Input) : Except String (List (Nat × Core.Value)) := do
  let inputs ← partition.mapM fun row => do
    let selected ← aggregate.filteredRows ctx [row.row]
    if selected.isEmpty then return (.null : Core.Value)
    let some argument := aggregate.argument | throw "missing numeric window argument"
    SQLSurface.value (← ctx.eval row.row argument)
  let mut accumulator : SQLite.AggregateSum.State := {}
  let mut added := 0
  let mut removed := 0
  let mut results := []
  for (row,position) in partition.zipIdx do
    let (first,stop) ← frameRange term.specification directions partition position
    for i in [removed:min first added] do
      let some value := inputs[i]? | throw "missing window inverse input"
      accumulator := accumulator.inverse value
      removed := i + 1
    for i in [added:stop] do
      let some value := inputs[i]? | throw "missing window step input"
      accumulator := accumulator.step value
      added := i + 1
    for i in [removed:min first added] do
      let some value := inputs[i]? | throw "missing initial window inverse input"
      accumulator := accumulator.inverse value
      removed := i + 1
    let value ← match aggregate.function with
      | .sum => accumulator.sumResult
      | .average => pure (if accumulator.count == 0 then .null else
          SQLite.AggregateSum.realValue (accumulator.total / Float.ofNat accumulator.count))
      | .total => pure (SQLite.AggregateSum.realValue accumulator.total)
      | _ => throw "invalid numeric window aggregate"
    results := (row.index,value) :: results
  return results.reverse

def functionName : Expr → String
  | .call "__sqlean_aggregate_filter" #[function, _] false => functionName function
  | .call name _ _ => name.toLower
  | _ => ""

def checkSource (ctx : CoreExpr.Context) (expression : Expr) : Except String Unit := do
  if ctx.schema.columns.isEmpty then
    let bad := expression.any (fun node => match node with | .column .. | .star .. => true | _ => false)
    if bad then throw "no such column in a source-free window query"

def validate (ctx : CoreExpr.Context) (term : Term) : Except String (Option CoreAggregate.Term) := do
  checkSource ctx term.function
  for expression in term.specification.partition do
    checkSource ctx expression
    ctx.validate expression
  for order in term.specification.ordering do
    checkSource ctx order.expr
    CoreOrder.validateTerm ctx order
  if functionName term.function == "row_number" then
    match term.function with
    | .call name args star =>
        unless name.toLower == "row_number" do throw "FILTER clause may only be used with aggregate window functions"
        unless args.isEmpty && !star do throw "wrong number of arguments to function row_number()"
        return none
    | _ => throw "invalid row_number window function"
  if term.function.any (fun expression => match expression with
      | .call name _ _ => isDistinctAggregateName name | _ => false) then
    throw "DISTINCT is not supported for window functions"
  return some (← CoreAggregate.term ctx { expr := term.function })

def evaluate (ctx : CoreExpr.Context) (rows : List (List Core.Value))
    (term : Term) : Except String (List Core.Value × List Nat) := do
  let aggregate ← validate ctx term
  let directions ← term.specification.ordering.toList.mapM CoreOrder.specification
  let partitions ← term.specification.partition.toList.mapM fun expr => CoreOrder.specification { expr }
  let inputs ← rows.zipIdx.mapM fun (row,index) => do
    return ({
      index := index
      row := row
      partition := ← ctx.projectRow row term.specification.partition.toList
      keys := ← ctx.projectRow row (term.specification.ordering.toList.map (fun order => CoreOrder.keyExpression order.expr)) } : Input)
  let keyed := inputs.map fun row => { row with keys := row.partition ++ row.keys }
  let sorted := (keyed.foldl (fun acc row => insert (partitions ++ directions) row acc) []).map
    (fun row => { row with keys := row.keys.drop partitions.length })
  let numeric := aggregate.any (fun term => match term.function with
    | .sum | .average | .total => true | _ => false)
  let mut numericResults : List (Nat × Core.Value) := []
  if numeric then
    let some aggregate := aggregate | throw "missing numeric aggregate"
    let mut completed : List (List Core.Value) := []
    for input in sorted do
      unless completed.any (fun key => equivalent partitions key input.partition) do
        let partition := sorted.filter (fun row => equivalent partitions row.partition input.partition)
        numericResults := numericResults ++ (← numericPartition ctx term aggregate directions partition)
        completed := input.partition :: completed
  let values ← inputs.mapM fun input => do
    if numeric then
      let some (_,value) := numericResults.find? (fun result => result.1 == input.index)
        | throw "missing numeric window result"
      return value
    let partition := sorted.filter (fun row => equivalent partitions row.partition input.partition)
    let position := partition.findIdx (fun row => row.index == input.index)
    match aggregate with
    | none => SQLSurface.value (.integer (position + 1))
    | some aggregate => aggregate.eval ctx (← frame term.specification directions partition position)
  return (values, sorted.map (·.index))

def execute (state : Core.State) (original : Select) : Except String Core.Result := do
  let query := CoreConnectionSQL.select state original.compoundHeight original
  unless query.sources.size ≤ 1 && query.valueRows.isNone && query.groupBy.isEmpty &&
      query.having.isNone && query.compounds.isEmpty do
    throw "unsupported window query source/grouping shape"
  let (ctx, allRows) ← match query.sources.toList with
    | [] => pure (({ schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" } : CoreExpr.Context), [[]])
    | [source] => do
        let some stored := CoreNames.table? state.database source.name | throw s!"no such table: {source.name}"
        let (_, input) ← Core.execute state (.query stored.schema.name { columns := List.range stored.schema.columns.length })
        pure ({ schema := stored.schema, sourceName := source.alias.getD source.name }, input.rows)
    | _ => throw "unsupported window join"
  for column in query.columns do checkSource ctx column.expr
  let _ ← query.where_.mapM (checkSource ctx)
  let columns ← CoreOrder.expandResults ctx query.columns.toList
  let ordering ← CoreOrder.resolve ctx columns query.orderBy.toList
  let condition := query.where_.map (CoreOrder.resolveAliases ctx columns)
  if let some expression := condition then
    if expression.any node then
      let (_, terms) ← (replace ctx.schema (expression.height + 1) expression).run #[]
      let name := (terms[0]?.map (fun term => functionName term.function)).getD ""
      throw s!"misuse of window function {name}()"
  let _ ← condition.mapM ctx.validate
  let collect : Collect (List Expr × List OrderTerm) := do
    let expressions ← columns.mapM fun col => replace ctx.schema (col.expr.height + 1) col.expr
    let ordering ← ordering.mapM fun order => do
      return { order with expr := ← replace ctx.schema (order.expr.height + 1) order.expr }
    return (expressions, ordering)
  let ((expressions, ordering), terms) ← collect.run #[]
  for term in terms do discard <| validate ctx term
  let expanded : CoreExpr.Context := { ctx with schema := { ctx.schema with
    columns := ctx.schema.columns ++ terms.toList.map (fun term => ({ name := term.name } : Core.Column)) } }
  for expression in expressions do expanded.validate expression
  for order in ordering do CoreOrder.validateTerm expanded order
  if query.limit == some 0 then return {}
  let rows ← allRows.filterM (fun row => ctx.matches row condition)
  -- SQLite nests incompatible window orderings from right to left. Stable
  -- ties in an outer window therefore inherit the inner window's row order.
  let mut rowOrder := List.range rows.length
  let mut values : List (List Core.Value) := []
  for term in terms.toList.reverse do
    let inputs ← rowOrder.mapM fun index =>
      match rows[index]? with
      | some row => pure row | none => throw "missing window source row"
    let (computed, ordering) ← evaluate ctx inputs term
    let restored ← (List.range rows.length).mapM fun index => do
      let position := rowOrder.findIdx (· == index)
      let some value := computed[position]? | throw "missing window column value"
      return value
    values := restored :: values
    rowOrder ← ordering.mapM fun index =>
      match rowOrder[index]? with
      | some index => pure index | none => throw "window ordering lost its source index"
  let augmented := rows.zipIdx.map fun (row,index) => row ++ values.map (fun values => (values[index]?).getD .null)
  let ordered ← rowOrder.mapM fun index =>
    match augmented[index]? with
    | some row => pure row
    | none => throw "window ordering lost its source row"
  let selected ← CoreOrder.scan expanded none expressions ordering query.distinct ordered query.offset query.limit
  return { rows := selected.map (·.output) }

theorem insert_length (directions : List CoreOrder.KeySpec) (row : Input) (rows : List Input) :
    (insert directions row rows).length = rows.length + 1 := by
  induction rows with
  | nil => rfl
  | cons first rest ih => simp only [insert]; split <;> simp_all <;> omega

end SQLeanite.CoreWindow
