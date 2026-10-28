import SQLeanite.CoreDeclaredCollationSQL
import SQLeanite.CoreConnectionSQL

/-! Scalar, IN and EXISTS SELECT evaluation with lexical outer bindings.
Callbacks retain their distinct result requirements and run lazily; preparation
checks captured names and widths even in unexecuted scalar branches. -/
namespace SQLeanite.CoreScalarQuery

structure Frame where
  context : CoreExpr.Context
  row : List Core.Value
  declarations : List CoreCollationSyntax.Spec := []

def expressions (query : Select) : List Expr :=
  query.columns.toList.map (·.expr) ++ query.where_.toList ++
  query.groupBy.toList ++ query.having.toList ++ query.orderBy.toList.map (·.expr) ++
  query.sources.toList.flatMap (fun source => source.joinOn.toList ++
    (source.functionArgs.getD #[]).toList) ++
  (query.valueRows.getD #[]).toList.flatMap Array.toList

def captures : Nat → Expr → List (SQLite.Scalar.QueryKind × String)
  | 0, _ => []
  | fuel + 1, expression =>
      let visit := captures fuel
      match expression with
      | .scalarSubquery sql => [(.scalar,sql)]
      | .existsSubquery sql => [(.exists,sql)]
      | .inSubquery arg sql _ => visit arg ++ [(.membership,sql)]
      | .unary _ arg | .isNull arg _ | .collate arg _ => visit arg
      | .binary _ a b => visit a ++ visit b
      | .call _ args _ => args.toList.flatMap visit
      | .inList arg values _ _ => visit arg ++ values.toList.flatMap visit
      | .case_ base branches other => base.toList.flatMap visit ++
          branches.toList.flatMap (fun (a,b) => visit a ++ visit b) ++ other.toList.flatMap visit
      | _ => []

def has : Nat → Select → Bool
  | 0, _ => true
  | fuel + 1, query => (expressions query).any (fun expression =>
      !(captures expression.height (SQLite.Scalar.prepare expression)).isEmpty) ||
      query.compounds.any (fun (_,query) => has fuel query)

def column? (ctx : CoreExpr.Context) (qualifier : Option String) (name : String) : Option Nat :=
  if ctx.schema.columns.isEmpty then none else ctx.column? qualifier name

/-- Preserve quoted periods; only an explicit main schema is normalized. -/
def sourceNames (query : Select) : Except String Select := do
  let sources ← query.sources.mapM fun source => do
    match source.schema with
    | none => pure source
    | some schema =>
        unless schema.toLower == "main" do throw s!"no such table: {source.name}"
        let name := String.ofList (source.name.toList.drop (schema.length + 1))
        return { source with name, schema := none, alias := source.alias.orElse (fun _ => some name) }
  return { query with sources }

def localContext (state : Core.State) (query : Select) : Except String CoreExpr.Context := do
  match query.sources.toList with
  | [] => return { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  | [source] =>
      let some table := CoreNames.table? state.database source.name | throw s!"no such table: {source.name}"
      return { schema := table.schema, sourceName := source.alias.getD source.name, storedTexts := state.catalog.storedTexts }
  | _ => throw "unsupported scalar-subquery source shape"

def outerValue (parents : List Frame) (qualifier : Option String) (name : String) : Except String (Option Expr) := do
  for frame in parents do
    if let some index := column? frame.context qualifier name then
      let some value := frame.row[index]? | throw "missing correlated row value"
      let some column := frame.context.schema.columns[index]? | throw "missing correlated column metadata"
      let value ← CoreExpr.value value
      let expression := Expr.call "__sqlean_bound_value"
        #[.literal value, .literal (.text (CoreCreateTableAs.declaredType column.affinity))] false
      let expression := match frame.declarations.find? (fun spec => spec.1.toLower == column.name.toLower) with
        | none => expression
        | some spec => SQLite.ExprCollation.declared expression spec.2
      return some expression
  return none

def bindLocal (localName : Option String → String → Except String Bool) (parents : List Frame) (aliases : List ResultColumn) :
    Nat → Expr → Except String Expr
  | 0, _ => .error "correlated expression nesting limit exceeded"
  | fuel + 1, expression => do
      let visit := bindLocal localName parents aliases fuel
      match expression with
      | .column qualifier name =>
          if ← localName qualifier name then return expression
          if qualifier.isNone && (CoreOrder.aliasExpression? aliases name).isSome then return expression
          return (← outerValue parents qualifier name).getD expression
      | .unary op arg => return .unary op (← visit arg)
      | .binary op a b => return .binary op (← visit a) (← visit b)
      | .call name args star =>
          if let some column := SQLite.Scalar.quotedIdentifier? expression then
            unless ← localName none column do
              if let some value ← outerValue parents none column then return value
          return .call name (← args.mapM visit) star
      | .isNull arg negated => return .isNull (← visit arg) negated
      | .inList arg values negated affinity => return .inList (← visit arg) (← values.mapM visit) negated affinity
      | .inSubquery arg sql negated => return .inSubquery (← visit arg) sql negated
      | .collate arg name => return .collate (← visit arg) name
      | .case_ base branches other =>
          return .case_ (← base.mapM visit) (← branches.mapM fun (a,b) => return (← visit a, ← visit b)) (← other.mapM visit)
      | other => return other

def bind (ctx : CoreExpr.Context) (parents : List Frame) (aliases : List ResultColumn)
    (fuel : Nat) (expression : Expr) : Except String Expr :=
  bindLocal (fun qualifier name => .ok ((column? ctx qualifier name).isSome)) parents aliases fuel expression

def bindQuery (localName : Option String → String → Except String Bool) (parents : List Frame) (query : Select) : Except String Select := do
  let visit := fun aliases expr => bindLocal localName parents aliases (expr.height + 1) expr
  return { query with
    columns := ← query.columns.mapM fun column => return { column with expr := ← visit [] column.expr }
    where_ := ← query.where_.mapM (visit query.columns.toList)
    groupBy := ← query.groupBy.mapM (visit query.columns.toList)
    having := ← query.having.mapM (visit query.columns.toList)
    orderBy := ← query.orderBy.mapM fun order => return { order with expr := ← visit query.columns.toList order.expr }
    sources := ← query.sources.mapM fun source => return { source with joinOn := ← source.joinOn.mapM (visit []) } }

/-- Every compound arm has its own local scope and shares the same lexical
parents. A left arm's local columns never bind names in its right arm. -/
def bindInputs : Nat → Core.State → List Frame → Select → Except String Select
  | 0, _, _, _ => .error "correlated compound nesting limit exceeded"
  | fuel + 1, state, parents, query => do
      let query ← sourceNames query
      let ctx ← CoreCreateTableAs.contexts state.database query
      let localName := fun qualifier name => do
        let candidates := CoreJoinUsing.nameCandidates ctx.sources qualifier name
        if candidates.isEmpty then return false
        if (CoreCreateTableAs.column? ctx qualifier name).isNone then
          throw s!"ambiguous column name: {(qualifier.map (· ++ ".")).getD ""}{name}"
        return true
      let query ← bindQuery localName parents query
      let compounds ← query.compounds.mapM fun (operation, arm) => do
        return (operation, ← bindInputs fuel state parents arm)
      return { query with compounds }

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

def rowMatches (ctx : CoreExpr.Context) (condition : Option Expr) (row : List Core.Value) : Except String Bool := do
  match condition with
  | none => pure true
  | some expression =>
      let expression := SQLite.Scalar.prepare (ctx.bindNames expression)
      SQLite.Scalar.testEvaluatedFuel (ctx.eval row) ctx.affinity true expression.height true expression

/-- The existing bounded-sort projection order, retaining scalar subtype slots
until the SELECT value is consumed by its parent expression. -/
def scan (ctx : CoreExpr.Context) (condition : Option Expr) (expressions : List Expr) (terms : List OrderTerm)
    (distinct : Bool) (rows : List (List Core.Value)) (offset : Nat) (limit : Option Nat) :
    Except String (List TypedOutput) := do
  if limit == some 0 then return []
  if terms.isEmpty then
    let mut remainingOffset := offset
    let mut count := 0
    let mut reversed : List TypedOutput := []
    let mut seen : List (List Core.Value) := []
    for row in rows do
      if limit.any (count ≥ ·) then break
      unless ← rowMatches ctx condition row do continue
      if !distinct && remainingOffset > 0 then
        remainingOffset := remainingOffset - 1
        continue
      let output ← project ctx row expressions
      let key := Core.distinctRowKey output.values
      if distinct && seen.any (CoreExpr.distinctEqual expressions key) then continue
      if distinct then seen := key :: seen
      if remainingOffset > 0 then
        remainingOffset := remainingOffset - 1
        continue
      reversed := output :: reversed
      count := count + 1
    return reversed.reverse
  let directions ← terms.mapM CoreOrder.specification
  let capacity := limit.map (· + offset)
  let mut sorted : List TypedOutput := []
  let mut seen : List (List Core.Value) := []
  for row in rows do
    unless ← rowMatches ctx condition row do continue
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

theorem scan_limit_zero (ctx : CoreExpr.Context) (condition : Option Expr)
    (expressions : List Expr) (terms : List OrderTerm) (distinct : Bool)
    (rows : List (List Core.Value)) (offset : Nat) :
    scan ctx condition expressions terms distinct rows offset (some 0) = .ok [] := rfl

def setTruth (collation : SQLite.Collation.Kind) (affinity : SQLite.Affinity)
    (left : Value) (values : List Value) : Truth :=
  if values.isEmpty then .false else
    SQLite.Scalar.membership collation affinity left values (SQLite.Scalar.isNull left)

theorem setTruth_empty (collation : SQLite.Collation.Kind) (affinity : SQLite.Affinity) (left : Value) :
    setTruth collation affinity left [] = .false := rfl

/-- Preparation compiles source scopes without evaluating their rows. Execution
uses actual lexical values. Both phases return their real private input state. -/
abbrev SourceCompiler := Bool → Nat → Core.State → List Frame → Select →
  Except String (Core.State × Select)

def identitySources : SourceCompiler := fun _ _ state _ query => .ok (state,query)

theorem identitySources_input (preparing : Bool) (fuel : Nat) (state : Core.State)
    (parents : List Frame) (query : Select) :
    identitySources preparing fuel state parents query = .ok (state,query) := rfl

structure Result where
  result : Core.Result
  width : Nat
  affinity : Option SQLite.Affinity
  firstTyped : Option SQLite.ScalarValue := none
  typedRows : List (List SQLite.ScalarValue) := []
  inputState : Core.State
  inputQuery : Select

structure Prepared where
  source : String
  kind : SQLite.Scalar.QueryKind
  query : Select
  affinity : Option SQLite.Affinity
  collation : Option String
  defaultCollation : Option String := none

def membershipCollation (leftExplicit rightExplicit leftDefault rightDefault : Option String) :
    Option SQLite.Collation.Kind :=
  SQLite.ExprCollation.ofName (leftExplicit.orElse fun _ => rightExplicit.orElse fun _ =>
    leftDefault.orElse fun _ => rightDefault)

theorem membershipCollation_explicit_right (collation : String)
    (leftDefault rightDefault : Option String) :
    membershipCollation none (some collation) leftDefault rightDefault =
      SQLite.ExprCollation.ofName (some collation) := rfl

theorem membershipCollation_default_left (collation : String) (rightDefault : Option String) :
    membershipCollation none none (some collation) rightDefault =
      SQLite.ExprCollation.ofName (some collation) := rfl

/-- IN uses the rightmost SELECT arm's result expression. Multi-row VALUES
keeps its first row's expression list; its row values are a separate program. -/
def membershipOperand : Nat → Select → Select
  | 0, query => query
  | fuel + 1, query => match query.compounds.toList.getLast? with
      | none => query
      | some (_,last) => membershipOperand fuel last

theorem membershipOperand_last (query last : Select) (operation : CompoundOp) (fuel : Nat)
    (found : query.compounds.toList.getLast? = some (operation,last)) :
    membershipOperand (fuel + 1) query = membershipOperand fuel last := by
  simp [membershipOperand, found]

/-- Explicit LIMIT 0 stays empty; otherwise a scalar SELECT stops at its first
row, retaining OFFSET and its ORDER BY semantics. -/
def scalarLimit (query : Select) : Select :=
  { query with limit := some (min 1 (query.limit.getD 1)) }

/-- EXISTS does not evaluate result scalars, but aggregate arguments and GROUP
BY keys still execute. Keeping the original expression in an unselected CASE
arm retains aggregate preparation while suppressing only result projection. -/
def existsExpression (expression : Expr) : Expr :=
  .case_ none #[(.literal (.integer 1), .literal (.integer 1))] (some expression)

def existsInput : Nat → Core.State → Select → Except String Select
  | 0, _, _ => .error "EXISTS query nesting limit exceeded"
  | fuel + 1, state, query => do
      let ctx ← localContext state query
      let columns ← CoreOrder.expandResults ctx query.columns.toList
      let groups ← query.groupBy.mapM fun expression => do
        return (← CoreGrouped.resolveGroupExpression ctx columns (SQLite.Scalar.prepare expression)).1
      let compounds ← query.compounds.mapM fun (op,branch) => do
        return (op, ← existsInput fuel state branch)
      return { query with
        columns := (columns.map fun column => { column with expr := existsExpression column.expr }).toArray
        where_ := query.where_.map (CoreOrder.resolveAliases ctx columns)
        having := query.having.map (CoreAggregateHaving.resolve ctx columns)
        groupBy := groups
        orderBy := #[]
        distinct := false
        valueRows := query.valueRows.map (·.map (·.map existsExpression))
        compounds }

def executeWithSources (compile : SourceCompiler) (preparing existsMode : Bool) : Nat → Core.State → List Frame → Select → Except String Result
  | 0, _, _, _ => .error "scalar subquery nesting limit exceeded"
  | fuel + 1, state, parents, original => do
      let (state,original) ← compile preparing fuel state parents original
      let original := CoreConnectionSQL.select state original.compoundHeight original
      let original ← CoreDeclaredCollationSQL.select state original
      let original ← bindInputs (original.compoundHeight + 1) state parents original
      let query := if existsMode then { original with distinct := false } else original
      let scalarShape := query.valueRows.isNone && query.groupBy.isEmpty && query.having.isNone &&
        query.compounds.isEmpty && query.sources.size ≤ 1 && !(query.columns.any (fun col => CoreAggregate.containsAggregate col.expr))
      if !has query.compoundHeight query && !scalarShape then
        let execution ← if existsMode then do
            -- Name/ordinal validation still precedes ORDER BY suppression.
            discard <| CoreSQL.executeSelect state { query with limit := some 0 }
            if query.compounds.all (fun (op,_) => op == .unionAll) then
              existsInput query.compoundHeight state query
            else pure { query with orderBy := #[] }
          else pure query
        let selected ← CoreSQL.executeSelectEncoded state execution
        let columns ← CoreCreateTableAs.baseColumns state.database query
        return {
          result := selected.result
          width := selected.width
          affinity := columns.head?.bind (·.affinity)
          inputState := state
          inputQuery := query }
      let ctx ← localContext state query
      let declarations ← match CoreNames.table? state.database ctx.schema.name with
        | none => pure []
        | some table => match table.catalogSource with
            | none => pure []
            | some source => source.compiledCollations
      let columns ← CoreOrder.expandResults ctx query.columns.toList
      let width := if let some rows := query.valueRows then (rows[0]?.getD #[]).size else columns.length
      unless query.valueRows.isNone && query.groupBy.isEmpty && query.having.isNone && query.compounds.isEmpty do
        throw "unsupported scalar-subquery grouping or compound shape"
      let dummy : Frame := { context := ctx, row := List.replicate ctx.schema.columns.length .null, declarations }
      let sources := (expressions query).flatMap (fun expression => captures expression.height (SQLite.Scalar.prepare expression))
      let mut prepared : List Prepared := []
      for (kind, sql) in sources do
        unless prepared.any (fun entry => entry.source == sql && entry.kind == kind) do
          let inner ← parseQuery sql
          let validated ← executeWithSources compile true (kind == .exists) fuel state (dummy :: parents) { inner with limit := some 0 }
          unless kind == .exists || validated.width == 1 do
            throw s!"sub-select returns {validated.width} columns - expected 1"
          let (collation,defaultCollation) ← if kind == .membership then do
              let operand := membershipOperand validated.inputQuery.compoundHeight validated.inputQuery
              let operand ← CoreSQL.compoundTailArm validated.inputState operand
              let expression := operand.columns.head?.map (fun column => SQLite.Scalar.prepare column.expr)
              pure (expression.bind SQLite.ExprCollation.name, expression.bind SQLite.ExprCollation.effectiveName)
            else pure (none,none)
          prepared := prepared ++ [{
            source := sql
            kind
            query := inner
            affinity := validated.affinity
            collation
            defaultCollation }]
      let evaluateQuery := fun row (request : SQLite.Scalar.QueryRequest) => do
        let some entry := prepared.find? (fun entry => entry.source == request.source && entry.kind == request.kind)
          | throw "unprepared scalar subquery"
        let query := if request.kind == .membership then entry.query else scalarLimit entry.query
        let result ← executeWithSources compile preparing (request.kind == .exists) fuel state
          ({ context := ctx, row, declarations } :: parents) query
        match request.kind with
        | .exists => return SQLite.Scalar.plainScalar (SQLite.Scalar.boolValue (!result.result.rows.isEmpty))
        | .membership =>
            let values ← result.result.rows.mapM fun row => CoreExpr.value ((row.head?).getD .null)
            let collation ← SQLite.ExprCollation.require
              ((membershipCollation request.collation entry.collation request.defaultCollation entry.defaultCollation).map
                (SQLite.Collation.forEncoding state.catalog.current.textEncoding))
            let affinity := SQLite.Scalar.comparisonAffinity request.affinity entry.affinity
            let truth := setTruth collation affinity request.value values
            return SQLite.Scalar.plainScalar ((if request.negated then truth.not else truth).toValue)
        | .scalar =>
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
        let checkedExpression := SQLite.Scalar.prepare expression
        if let some message := SQLite.Scalar.functionError checkedExpression.height checkedExpression then throw message
        preparedContext.validate expression
      let affinity := columns.head?.bind fun column => preparedContext.affinity column.expr
      if query.limit == some 0 then return { result := {}, width, affinity, inputState := state, inputQuery := query }
      let rows ← if query.sources.isEmpty then pure [[]] else do
        let (_, result) ← Core.execute state (.query ctx.schema.name { columns := List.range ctx.schema.columns.length })
        pure result.rows
      let emitted := if existsMode then [Expr.literal (.integer 1)] else projected
      let ordering := if existsMode then [] else ordering
      let result ← scan preparedContext condition emitted ordering query.distinct rows query.offset query.limit
      return {
        result := { rows := result.map (·.values) }
        width
        affinity
        firstTyped := result.head?.bind (fun row => row.typed.head?)
        typedRows := result.map (·.typed)
        inputState := state
        inputQuery := query }

def executeWith (existsMode : Bool) (fuel : Nat) (state : Core.State) (parents : List Frame) (query : Select) :
    Except String Result := executeWithSources identitySources false existsMode fuel state parents query

def executePrepared (compile : SourceCompiler) (preparing : Bool) (fuel : Nat)
    (state : Core.State) (parents : List Frame) (query : Select) : Except String Result :=
  executeWithSources compile preparing false fuel state parents query

def execute (fuel : Nat) (state : Core.State) (parents : List Frame) (query : Select) :
    Except String Result := executeWith false fuel state parents query

theorem scalarLimit_zero (query : Select) (zero : query.limit = some 0) :
    (scalarLimit query).limit = some 0 := by simp [scalarLimit, zero]

end SQLeanite.CoreScalarQuery
