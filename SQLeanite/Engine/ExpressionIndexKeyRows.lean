import SQLeanite.Engine.EvaluationDepth

namespace SQLeanite

/-- Attach expression-index keys without dropping or duplicating candidate
environments. This helper is on the live SELECT path below. -/
def expressionIndexKeyRows (db : Database) (expressions : Array Expr) :
    List Env → Except String (List (Array Value × Env))
  | [] => .ok []
  | env :: envs =>
      match expressions.mapM (evalWithDb db env) with
      | .error message => .error message
      | .ok keys =>
          match expressionIndexKeyRows db expressions envs with
          | .error message => .error message
          | .ok tail => .ok ((keys, env) :: tail)

theorem expressionIndexKeyRows_preserves_rows
    (db : Database) (expressions : Array Expr) (envs : List Env)
    {keyed : List (Array Value × Env)}
    (success : expressionIndexKeyRows db expressions envs = .ok keyed) :
    keyed.map (·.2) = envs := by
  induction envs generalizing keyed with
  | nil =>
      simp [expressionIndexKeyRows] at success
      subst keyed
      rfl
  | cons env envs induction =>
      unfold expressionIndexKeyRows at success
      cases keysResult : expressions.mapM (evalWithDb db env) with
      | error message => simp [keysResult] at success
      | ok keys =>
          rw [keysResult] at success
          cases tailResult : expressionIndexKeyRows db expressions envs with
          | error message => simp [tailResult] at success
          | ok tail =>
              rw [tailResult] at success
              simp only [Except.ok.injEq] at success
              subst keyed
              simp [induction tailResult]

/-- The live expression-index branch evaluates keys and uses them only to
reorder rows. It does not yet perform indexed lookup. -/
def evalIndex (db : Database) (expressions : Array Expr)
    (filtered : Array Env) : Except String (List Env) :=
  match expressionIndexKeyRows db expressions filtered.toList with
  | .error message => .error message
  | .ok keyed => .ok ((sortValueKeyed keyed.toArray).map (·.2)).toList

def evalScan (filtered : Array Env) : List Env := filtered.toList

/-- The actual live expression-index ordering path is bag-equivalent to the
full-scan candidate list: evaluating and sorting keys can neither lose nor
duplicate a row. -/
theorem index_matches_scan (db : Database) (expressions : Array Expr)
    (filtered : Array Env) {indexed : List Env}
    (success : evalIndex db expressions filtered = .ok indexed) :
    indexed.Perm (evalScan filtered) := by
  unfold evalIndex at success
  cases keyedResult : expressionIndexKeyRows db expressions filtered.toList with
  | error message => simp [keyedResult] at success
  | ok keyed =>
      rw [keyedResult] at success
      simp only [Except.ok.injEq] at success
      subst indexed
      have sorted := (sortValueKeyed_perm keyed.toArray).map (fun pair => pair.2)
      have keysPreserve := expressionIndexKeyRows_preserves_rows db expressions
        filtered.toList keyedResult
      simpa [evalScan, keysPreserve] using sorted

def evalMiniQuery (db : Database) (outer : Env) (sql : String) :
    Except String (Array (Array Value)) :=
  evalMiniQueryFuel (evaluationDepth db) db outer sql

def evalMiniSelect (db : Database) (outer : Env) (query : Select) :
    Except String (Array (Array Value)) :=
  evalMiniSelectFuel (evaluationDepth db + query.compoundHeight) db outer query

def evalViewTable (db : Database) (tableName : String) (view : View) : Except String Table :=
  evalViewTableFuel (evaluationDepth db + view.query.compoundHeight) db tableName view

theorem evalWithDb_literal (db : Database) (env : Env) (value : Value) :
    evalWithDb db env (.literal value) = .ok value := by
  simp only [evalWithDb, evaluationDepth, Expr.height, evalWithDbFuel,
    resolveSubqueriesFuel, evalExpr_literal]
  simpa using evalExpr_literal env value

def Expr.hasAggregate (expression : Expr) : Bool :=
  expression.anyOutsideSubqueries fun
    | .call name args _ =>
        let name := aggregateFunctionName name
        ["count", "sum", "total", "avg", "group_concat", "string_agg",
          "legacy_count", "md5sum"].contains name ||
          ((nameEq name "min" || nameEq name "max") && args.size == 1)
    | _ => false

def Expr.referencesAnyColumn (expression : Expr) : Bool :=
  expression.any fun
    | .column .. => true
    | _ => false

def Select.hasSourceFreeColumnAggregateFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, query =>
    (query.sources.isEmpty && query.columns.any (fun column =>
      column.expr.hasAggregate && column.expr.referencesAnyColumn)) ||
      query.compounds.any (fun compound =>
        hasSourceFreeColumnAggregateFuel fuel compound.2)

def Select.hasSourceFreeColumnAggregate (query : Select) : Bool :=
  query.hasSourceFreeColumnAggregateFuel query.compoundHeight

def Expr.hasOuterAggregateSubqueryFuel : Nat → Expr → Bool
  | 0, _ => false
  | _ + 1, .scalarSubquery sql => match parseLegacy sql with
    | .ok statements => match statements[0]? with
      | some (Statement.select query) => query.hasSourceFreeColumnAggregate
      | _ => false
    | .error _ => false
  | fuel + 1, .unary _ expression | fuel + 1, .isNull expression _ |
      fuel + 1, .collate expression _ => hasOuterAggregateSubqueryFuel fuel expression
  | fuel + 1, .binary _ left right =>
    hasOuterAggregateSubqueryFuel fuel left || hasOuterAggregateSubqueryFuel fuel right
  | fuel + 1, .call _ arguments _ =>
    arguments.any (hasOuterAggregateSubqueryFuel fuel)
  | fuel + 1, .inList expression values _ _ =>
    hasOuterAggregateSubqueryFuel fuel expression ||
      values.any (hasOuterAggregateSubqueryFuel fuel)
  | fuel + 1, .case_ base branches else_ =>
    base.any (hasOuterAggregateSubqueryFuel fuel) || branches.any (fun pair =>
      hasOuterAggregateSubqueryFuel fuel pair.1 ||
        hasOuterAggregateSubqueryFuel fuel pair.2) ||
      else_.any (hasOuterAggregateSubqueryFuel fuel)
  | fuel + 1, .inSubquery expression _ _ =>
    hasOuterAggregateSubqueryFuel fuel expression
  | _, _ => false

def Expr.hasOuterAggregateSubquery (expression : Expr) : Bool :=
  hasOuterAggregateSubqueryFuel expression.height expression

def Expr.hasParameter (expression : Expr) : Bool :=
  expression.any fun
    | .column none name => name == "?"
    | .call name _ _ => nameEq name "lean_unbound_parameter"
    | .scalarSubquery sql | .existsSubquery sql | .inSubquery _ sql _ => sql.contains '?'
    | _ => false

def Expr.containsSubquery (expression : Expr) : Bool :=
  expression.any fun
    | .scalarSubquery .. | .existsSubquery .. | .inSubquery .. => true
    | _ => false

def Expr.defaultHasNonconstantFunction (expression : Expr) : Bool :=
  expression.anyOutsideSubqueries fun
    | .call name _ _ => ["random", "randomblob", "raise"].contains name.toLower
    | _ => false

/-- SQLite's legacy DEFAULT grammar treats a lone unknown bare word as a text
literal, while a real column name (or a reference nested in an expression) is
non-constant. -/
def defaultReferencesColumn (definitions : Array ColumnDef) (expression : Expr) : Bool :=
  match expression with
  | .column none candidate => definitions.any (fun definition => nameEq definition.name candidate)
  | _ => expressionHasRealColumn expression

def Expr.withCheckQualifierFuel : Nat → Expr → Expr
  | 0, expression => expression
  | _ + 1, .column (some qualifier) name =>
    .column (some (if qualifier.toList.contains '.' then unqualifiedName qualifier else qualifier)) name
  | fuel + 1, .unary operation expression =>
    .unary operation (withCheckQualifierFuel fuel expression)
  | fuel + 1, .isNull expression negated =>
    .isNull (withCheckQualifierFuel fuel expression) negated
  | fuel + 1, .collate expression name =>
    .collate (withCheckQualifierFuel fuel expression) name
  | fuel + 1, .binary operation left right =>
    .binary operation (withCheckQualifierFuel fuel left) (withCheckQualifierFuel fuel right)
  | fuel + 1, .call name args hasStar =>
    .call name (args.map (withCheckQualifierFuel fuel)) hasStar
  | fuel + 1, .inList expression values negated affinity =>
    .inList (withCheckQualifierFuel fuel expression) (values.map (withCheckQualifierFuel fuel))
      negated affinity
  | fuel + 1, .case_ base branches else_ =>
    .case_ (base.map (withCheckQualifierFuel fuel))
      (branches.map fun pair =>
        (withCheckQualifierFuel fuel pair.1, withCheckQualifierFuel fuel pair.2))
      (else_.map (withCheckQualifierFuel fuel))
  | fuel + 1, .inSubquery expression sql negated =>
    .inSubquery (withCheckQualifierFuel fuel expression) sql negated
  | _, expression => expression

def Expr.withCheckQualifier (expression : Expr) : Expr :=
  withCheckQualifierFuel expression.height expression

def Expr.indexNondeterminismFuel? : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, .call name arguments _ =>
      let function := aggregateFunctionName name
      if function == "random" || function == "randomblob" || function == "lean_nondeterministic" then
        some "non-deterministic functions prohibited in index expressions"
      else if function == "julianday" && arguments.any (fun argument =>
          match argument with | .literal (.text value) => value.toLower == "now" | _ => false) then
        some "non-deterministic use of julianday() in an index"
      else arguments.findSome? (indexNondeterminismFuel? fuel)
  | fuel + 1, .unary _ expression | fuel + 1, .isNull expression _ |
      fuel + 1, .collate expression _ => indexNondeterminismFuel? fuel expression
  | fuel + 1, .binary _ left right =>
    indexNondeterminismFuel? fuel left <|> indexNondeterminismFuel? fuel right
  | fuel + 1, .inList expression values _ _ =>
    indexNondeterminismFuel? fuel expression <|>
      values.findSome? (indexNondeterminismFuel? fuel)
  | fuel + 1, .case_ base branches else_ =>
    base.bind (indexNondeterminismFuel? fuel) <|>
      branches.findSome? (fun pair => indexNondeterminismFuel? fuel pair.1 <|>
        indexNondeterminismFuel? fuel pair.2) <|>
      else_.bind (indexNondeterminismFuel? fuel)
  | _, _ => none

def Expr.indexNondeterminism? (expression : Expr) : Option String :=
  indexNondeterminismFuel? expression.height expression

def Select.hasParameterFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, query =>
    query.columns.any (fun column => column.expr.hasParameter) ||
      query.valueRows.any (fun rows => rows.any (fun row => row.any Expr.hasParameter)) ||
      query.where_.any Expr.hasParameter ||
      query.groupBy.any Expr.hasParameter || query.having.any Expr.hasParameter ||
      query.orderBy.any (fun term => term.expr.hasParameter) ||
      query.sources.any (fun source => source.subquerySql.any (·.contains '?')) ||
      query.compounds.any (fun compound => hasParameterFuel fuel compound.2)

def Select.hasParameter (query : Select) : Bool :=
  query.hasParameterFuel query.compoundHeight

def Expr.firstAggregateFuel? : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, .call name args _ =>
    let name := aggregateFunctionName name
    if ["count", "sum", "total", "avg", "group_concat", "string_agg",
        "legacy_count", "md5sum"].contains name ||
        ((nameEq name "min" || nameEq name "max") && args.size == 1) then some name
    else args.findSome? (firstAggregateFuel? fuel)
  | fuel + 1, .unary _ expression | fuel + 1, .isNull expression _ |
      fuel + 1, .collate expression _ => firstAggregateFuel? fuel expression
  | fuel + 1, .inList expression values _ _ =>
    firstAggregateFuel? fuel expression <|> values.findSome? (firstAggregateFuel? fuel)
  | fuel + 1, .case_ base branches else_ =>
    base.bind (firstAggregateFuel? fuel) <|>
      branches.findSome? (fun pair => firstAggregateFuel? fuel pair.1 <|>
        firstAggregateFuel? fuel pair.2) <|>
      else_.bind (firstAggregateFuel? fuel)
  | fuel + 1, .binary _ left right =>
    firstAggregateFuel? fuel left <|> firstAggregateFuel? fuel right
  | _, _ => none

def Expr.firstAggregate? (expression : Expr) : Option String :=
  firstAggregateFuel? expression.height expression

def Expr.referencesColumn (target : String) (expression : Expr) : Bool :=
  expression.any fun
    | .column _ name => nameEq name target
    | _ => false

def Expr.aggregateReferencesColumn (target : String) (expression : Expr) : Bool :=
  expression.any fun
    | .call name args _ =>
        let name := aggregateFunctionName name
        let aggregate := ["count", "sum", "total", "avg", "group_concat", "string_agg",
          "legacy_count", "md5sum"].contains name ||
          ((nameEq name "min" || nameEq name "max") && args.size == 1)
        aggregate && args.any (Expr.referencesColumn target)
    | _ => false

def aggregateValues (db : Database) (envs : Array Env) (arg : Expr) : Except String (Array Value) :=
  envs.mapM (fun env => evalWithDb db env arg)

def distinctAggregateValues (db : Database) (envs : Array Env)
    (arg : Expr) : Except String (Array Value) := do
  let values ← aggregateValues db envs arg
  let collation := arg.collationIn (envs[0]?.getD #[])
  pure (deduplicateNonNullValues collation values)

def aggregateEvaluationDepth : Nat := 1000

def evalAggregateFuel : Nat → Database → Array Env → Expr → Except String Value
  | 0, _, _, _ => throw "expression tree is too large"
  | fuel + 1, db, envs, .scalarSubquery sql => do
    let statements ← parseLegacy sql
    let query ← match statements[0]? with
      | some (Statement.select query) => pure query
      | _ => throw "subquery must be a SELECT"
    let rec materialize : Nat → Select → Except String Select
      | 0, _ => throw "expression tree is too large"
      | remaining + 1, query => do
        let columns ← if query.sources.isEmpty then query.columns.mapM fun column => do
            if column.expr.hasAggregate && column.expr.referencesAnyColumn then
              let value ← evalAggregateFuel remaining db envs column.expr
              pure { column with expr := .literal value }
            else pure column
          else pure query.columns
        let compounds ← query.compounds.mapM fun compound => do
          pure (compound.1, ← materialize remaining compound.2)
        pure { query with columns, compounds }
    let rows ← evalMiniSelect db (envs[0]?.getD #[]) (← materialize fuel query)
    pure (rows[0]?.bind (·[0]?) |>.getD .null)
  | fuel + 1, db, envs, .call name args star => do
    let distinct := isDistinctAggregateName name
    let lname := aggregateFunctionName name
    let call := Expr.call name args star
    if !call.hasAggregate then
      evalWithDb db (envs[0]?.getD #[]) call
    else if distinct && args.size != 1 then
      throw "DISTINCT aggregates must have exactly one argument"
    else if lname == "count" then
      if args.isEmpty then pure (.integer envs.size)
      else if args.size != 1 then throw "wrong number of arguments to function count()"
      else
        let values ← if distinct then distinctAggregateValues db envs args[0]!
          else aggregateValues db envs args[0]!
        pure (.integer (values.foldl (init := 0) fun n v => if v matches .null then n else n + 1))
    else if ["sum", "total", "avg"].contains lname then
      if args.size != 1 then throw s!"wrong number of arguments to function {name}()"
      if let some nested := args[0]!.firstAggregate? then
        throw s!"misuse of aggregate function {nested}()"
      let values ← if distinct then distinctAggregateValues db envs args[0]!
        else aggregateValues db envs args[0]!
      let numericValues := values.filterMap fun value =>
        if value matches .null then none else some (aggregateNumericOperand value)
      let numbers := numericValues.filterMap Value.toFloat?
      if numericValues.isEmpty then pure (if lname == "total" then .real 0.0 else .null)
      else
        let total := numbers.foldl (· + ·) 0.0
        if lname == "avg" then pure (.real (total / numbers.size.toFloat))
        else if lname == "sum" && numericValues.all (fun v => v matches .integer _) then
          let mut integerTotal : Int := 0
          for value in numericValues do
            integerTotal := integerTotal + value.toInt?.getD 0
            unless inSigned64Range integerTotal do throw "integer overflow"
          pure (.integer integerTotal)
        else pure (.real total)
    else if lname == "group_concat" || lname == "string_agg" then
      if (lname == "group_concat" && (args.size != 1 && args.size != 2)) ||
          (lname == "string_agg" && args.size != 2) then
        throw s!"wrong number of arguments to function {name}()"
      let mut output := ""
      let mut found := false
      if distinct then
        let values ← distinctAggregateValues db envs args[0]!
        for value in values do
          if found then output := output ++ ","
          output := output ++ toString value
          found := true
      else
        for env in envs do
          let value ← evalWithDb db env args[0]!
          unless value matches .null do
            if found then
              let separator ← if args.size == 2 then evalWithDb db env args[1]!
                else pure (.text ",")
              unless separator matches .null do output := output ++ toString separator
            output := output ++ toString value
            found := true
      pure (if found then .text output else .null)
    else if lname == "legacy_count" then
      if !args.isEmpty then throw "wrong number of arguments to function legacy_count()"
      else pure (.integer envs.size)
    else if lname == "md5sum" then
      let mut output := ""
      for env in envs do
        for argument in args do
          let value ← evalWithDb db env argument
          unless value matches .null do output := output ++ toString value
      pure (.text output)
    else if (lname == "min" || lname == "max") && args.size == 1 then
      let values ← if distinct then distinctAggregateValues db envs args[0]!
        else aggregateValues db envs args[0]!
      pure (scalarMinMax (lname == "max") (values.filter fun v => !(v matches .null)))
    else
      let values ← args.mapM (evalAggregateFuel fuel db envs)
      evalExpr #[] (.call name (values.map Expr.literal) star)
  | fuel + 1, db, envs, .binary op a b => do
    let x ← evalAggregateFuel fuel db envs a
    let y ← evalAggregateFuel fuel db envs b
    let isComparison := [.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains op
    let representative := envs[0]?.getD #[]
    let (x, y) := if isComparison then
        comparisonValues (a.declaredTypeIn representative) (b.declaredTypeIn representative) x y
      else (x, y)
    let nocase := isComparison &&
      (nameEq (a.collationIn representative) "nocase" || nameEq (b.collationIn representative) "nocase")
    let x := if nocase then match x with | .text value => .text value.toLower | other => other else x
    let y := if nocase then match y with | .text value => .text value.toLower | other => other else y
    match op with
    | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .shiftLeft | .shiftRight =>
      pure (arithmetic op x y)
    | .eq | .ne | .lt | .le | .gt | .ge | .is | .isNot => pure (compareOp op x y)
    | .like => pure (patternOp false x y)
    | .glob => pure (patternOp true x y)
    | .match => throw "unable to use function MATCH in the requested context"
    | .and => pure (Truth.toValue (Truth.and x.truth y.truth))
    | .or => pure (Truth.toValue (Truth.or x.truth y.truth))
    | .concat => pure (if (x matches .null) || (y matches .null) then .null
        else .text (toString x ++ toString y))
    | .arrow => pure (.text (toString x ++ "->" ++ toString y))
    | .arrowText => pure (.text (toString x ++ "->>" ++ toString y))
  | fuel + 1, db, envs, .unary op e => do evalExpr #[] (.unary op (.literal (← evalAggregateFuel fuel db envs e)))
  | fuel + 1, db, envs, .isNull e n => do evalExpr #[] (.isNull (.literal (← evalAggregateFuel fuel db envs e)) n)
  | fuel + 1, db, envs, .collate e name => do evalExpr #[] (.collate (.literal (← evalAggregateFuel fuel db envs e)) name)
  | fuel + 1, db, envs, .inList e values n applyAffinity => do
    let left ← evalAggregateFuel fuel db envs e
    let right ← values.mapM (evalAggregateFuel fuel db envs)
    evalExpr #[] (.inList (.literal left) (right.map Expr.literal) n applyAffinity)
  | fuel + 1, db, envs, .case_ base branches else_ => do
    let base ← base.mapM (evalAggregateFuel fuel db envs)
    let branches ← branches.mapM fun (a, b) => do
      pure (.literal (← evalAggregateFuel fuel db envs a), .literal (← evalAggregateFuel fuel db envs b))
    let else_ ← else_.mapM (evalAggregateFuel fuel db envs)
    evalExpr #[] (.case_ (base.map Expr.literal) branches (else_.map Expr.literal))
  | _fuel + 1, db, envs, e@(.column _ _) =>
    if envs.isEmpty then pure .null else evalWithDb db envs[0]! e
  | _fuel + 1, db, envs, e => evalWithDb db (envs[0]?.getD #[]) e

def evalAggregate (db : Database) (envs : Array Env) (expression : Expr) : Except String Value :=
  evalAggregateFuel (Nat.succ (max aggregateEvaluationDepth expression.height)) db envs expression

theorem evalAggregate_fuel_covers_syntax (expression : Expr) :
    expression.height ≤ Nat.succ (max aggregateEvaluationDepth expression.height) :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)

def makeBindings (ref : TableRef) (table : Table) (row : StoredRow) : Env :=
  let defaultAlias := unqualifiedName table.name
  let visible := table.columns.mapIdx fun i col =>
    { table := ref.name, alias := ref.alias.getD defaultAlias,
      column := col.name, value := row.values[i]?.getD .null, collation := col.collation,
      declaredType := col.declaredType }
  let hidden := #["rowid", "_rowid_", "oid"].map fun name =>
    Binding.mk ref.name (ref.alias.getD defaultAlias) name (.integer row.rowid)
      true 0 "binary" "LEAN_HIDDEN"
  visible ++ hidden

end SQLeanite
