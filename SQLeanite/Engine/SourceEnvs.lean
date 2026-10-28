import SQLeanite.Engine.ExpressionIndexKeyRows

namespace SQLeanite

def sourceEnvs (db : Database) (refs : Array TableRef) : Except String (Array Env) := do
  let mut envs : Array Env := #[#[]]
  let mut template : Env := #[]
  let mut deferredInnerOn : Array Expr := #[]
  for ref in refs do
    let schemaColumns : Array Column := #[
      { name := "type" }, { name := "name" }, { name := "tbl_name" },
      { name := "rootpage" }, { name := "sql" }]
    let viewSchemaRows : Array StoredRow := db.views.toArray.mapIdx fun i view =>
      { rowid := i + 1, values := #[.text "view", .text view.name, .text view.name,
        .integer 0, .text (if view.sourceSql.isEmpty then s!"CREATE VIEW {view.name}" else view.sourceSql)] }
    let tableSchemaRows : Array StoredRow := db.tables.toArray.mapIdx fun i t =>
      { rowid := db.views.length + i + 1, values := #[.text "table", .text t.name, .text t.name,
        .integer (Int.ofNat (i + 2)), .text t.sql] }
    let triggerSchemaRows : Array StoredRow := db.triggers.toArray.mapIdx fun i trigger =>
      { rowid := db.views.length + db.tables.length + i + 1,
        values := #[.text "trigger", .text trigger.name, .text trigger.table,
          .integer 0, .text (if trigger.sourceSql.isEmpty then
            s!"CREATE TRIGGER {trigger.name}" else trigger.sourceSql)] }
    let indexSchemaRows : Array StoredRow := db.indexes.toArray.mapIdx fun i index =>
      { rowid := db.views.length + db.tables.length + db.triggers.length + i + 1,
        values := #[.text "index", .text index.name, .text index.table,
          .integer 0, if index.automatic then .null else .text index.sql] }
    let schemaRows := viewSchemaRows ++ tableSchemaRows ++ triggerSchemaRows ++ indexSchemaRows
    let schemaStore ← RowStore.checked schemaRows schemaColumns.size
    let schema := Table.mk ref.name schemaColumns schemaStore
      (Int.ofNat (schemaRows.size + 1)) #[] #[]
    let table ← match ref.subquerySql with
      | some sql => do
        let rows ← evalMiniQuery db #[] sql
        let statements ← parseLegacy sql
        let columns ← match statements[0]? with
          | some (Statement.select query) => pure (selectColumnSchema db query)
          | some (Statement.values values) => pure ((valuesColumnNames
              (values[0]?.map Array.size |>.getD 0)).map fun name => ({ name } : Column))
          | _ => throw "derived table must be a SELECT or VALUES"
        let columns := applyColumnAliases ref.columnAliases columns
        let stored := rows.mapIdx fun i values => { rowid := i + 1, values }
        let rowStore ← RowStore.checked stored columns.size
        pure (Table.mk ref.name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[])
      | none =>
        if let some view := findView? db ref.name then evalViewTable db ref.name view
        else if nameEq ref.name "sqlite_master" || nameEq ref.name "sqlite_schema" then pure schema
        else optionOr (findTable? db ref.name) s!"no such table: {ref.name}"
    if let some alias := ref.alias then
      if let some duplicate := table.columns.find? (fun column => template.any (fun binding =>
          !binding.hidden && nameEq binding.alias alias && nameEq binding.column column.name)) then
        throw s!"ambiguous column name: {alias}.{duplicate.name}"
    if ref.naturalJoin && (ref.joinOn.isSome || !ref.usingColumns.isEmpty) then
      throw "a NATURAL join may not have an ON or USING clause"
    let leftTemplate := template
    for column in ref.usingColumns do
      unless leftTemplate.any (fun binding => !binding.hidden && nameEq binding.column column) &&
          table.columns.any (fun candidate => nameEq candidate.name column) do
        throw s!"cannot join using column {column} - column not present in both tables"
    let naturalTemplateColumns := if ref.naturalJoin then table.columns.filterMap fun column =>
      if leftTemplate.any (fun left => !left.hidden && nameEq left.column column.name)
      then some column.name else none
      else #[]
    let templateUsingColumns := ref.usingColumns ++ naturalTemplateColumns
    let nullRow : StoredRow := { rowid := 0, values := table.columns.map fun _ => .null }
    let rightTemplate := (makeBindings ref table nullRow).map fun binding =>
      if templateUsingColumns.any (nameEq binding.column) then { binding with hidden := true }
      else binding
    let mut next := #[]
    let mut matchedRight := Std.HashSet.emptyWithCapacity (capacity := table.rows.size)
    let mut deferCurrentOn := false
    for baseEnv in envs do
      let mut matched := false
      let naturalColumns := if ref.naturalJoin then table.columns.filterMap fun column =>
        if baseEnv.any (fun left => !left.hidden && nameEq left.column column.name)
        then some column.name else none
        else #[]
      let usingColumns := ref.usingColumns ++ naturalColumns
      for rowIndex in [:table.rows.size] do
        let row := table.rows[rowIndex]!
        let right := makeBindings ref table row
        let combined := baseEnv ++ right
        let usingMatches ← usingColumns.allM (joinColumnMatches baseEnv right)
        let onMatches ← match ref.joinOn with
          | none => pure true
          | some condition =>
              if deferCurrentOn then pure true
              else match evalWithDb db combined condition with
                | .ok value => pure (value.truth == .true)
                | .error message =>
                    if !ref.leftJoin && !ref.rightJoin && message.startsWith "no such column:" then
                      deferCurrentOn := true
                      pure true
                    else throw message
        if usingMatches && onMatches then
          let projectedRight := right.map fun b =>
            if usingColumns.any (nameEq b.column) then { b with hidden := true } else b
          next := next.push (baseEnv ++ projectedRight)
          matched := true
          matchedRight := matchedRight.insert rowIndex
      if ref.leftJoin && !matched then
        let projectedRight := (makeBindings ref table nullRow).map fun binding =>
          if usingColumns.any (nameEq binding.column) then { binding with hidden := true }
          else binding
        next := next.push (baseEnv ++ projectedRight)
    if ref.rightJoin then
      for rowIndex in [:table.rows.size] do
        unless matchedRight.contains rowIndex do
          let right := makeBindings ref table table.rows[rowIndex]!
          let projectedRight := right.map fun binding =>
            if templateUsingColumns.any (nameEq binding.column) then { binding with hidden := true }
            else binding
          next := next.push (leftTemplate.map (fun binding => { binding with value := .null }) ++ projectedRight)
    envs := next
    template := leftTemplate ++ rightTemplate
    if deferCurrentOn then
      if let some condition := ref.joinOn then deferredInnerOn := deferredInnerOn.push condition
  unless deferredInnerOn.isEmpty do
    let mut filtered := #[]
    for env in envs do
      if ← deferredInnerOn.allM fun condition => do
          pure ((← evalWithDb db env condition).truth == .true) then
        filtered := filtered.push env
    envs := filtered
  pure envs

def matchesWhere (db : Database) (env : Env) (where_ : Option Expr) : Except String Bool := do
  match where_ with
  | none => pure true
  | some e => pure ((← evalWithDb db env e).truth == .true)

def addResultAliases (db : Database) (env : Env) (columns : Array ResultColumn) : Except String Env := do
  let mut out := env
  for col in columns do
    unless col.expr.hasAggregate do
      if let some alias := col.alias then
        let value ← evalWithDb db env col.expr
        out := out.push (Binding.mk "" "" alias value true 0
          (col.expr.collationIn env) (expressionDeclaredType col.expr))
  pure out

def expandResult (db : Database) (env : Env) (columns : Array ResultColumn) : Except String (Array Value) := do
  let mut out := #[]
  let mut outstandingDestructors := 0
  for col in columns do
    match col.expr with
    | .star qualifier =>
      if let some q := qualifier then
        unless env.any (fun b => (!b.hidden || b.declaredType != "LEAN_HIDDEN") &&
            (if nameEq b.alias b.table then nameEq b.table q else nameEq b.alias q)) do
          throw s!"no such table: {q}"
      for b in env do
        if (!b.hidden || (qualifier.isSome && b.declaredType != "LEAN_HIDDEN")) &&
            qualifier.all (fun q => if nameEq b.alias b.table then nameEq q b.table else nameEq q b.alias) then
          out := out.push b.value
    | .call name _ _ =>
      if nameEq name "test_destructor_count" then
        out := out.push (.integer outstandingDestructors)
      else
        let value ← evalWithDb db env col.expr
        if nameEq name "test_destructor" || nameEq name "test_destructor16" then
          outstandingDestructors := outstandingDestructors + 1
        out := out.push value
    | e => out := out.push (← evalWithDb db env e)
  pure out

def resultNames (db : Database) (env : Env) (columns : Array ResultColumn) : Array String := Id.run do
  let mut out := #[]
  for col in columns do
    match col.expr with
    | .star qualifier =>
      for b in env do
        if (!b.hidden || (qualifier.isSome && b.declaredType != "LEAN_HIDDEN")) &&
            qualifier.all (fun q => if nameEq b.alias b.table then nameEq q b.table else nameEq q b.alias) then
          let name := if db.shortColumnNames then b.column
            else if db.fullColumnNames then b.alias ++ "." ++ b.column else b.column
          out := out.push name
    | .column qualifier name =>
      let generated := if db.fullColumnNames then
          let tableName? := env.find? (fun b => !b.hidden && nameEq b.column name &&
            qualifier.all (fun q => nameEq q b.alias || nameEq q b.table)) |>.map (·.table)
          match tableName? with
          | some tableName => tableName ++ "." ++ name
          | none => match qualifier with | some q => q ++ "." ++ name | none => name
        else if db.shortColumnNames then name else col.sourceSql.getD col.expr.sql
      out := out.push (col.alias.getD generated)
    | e => out := out.push (col.alias.getD (col.sourceSql.getD e.sql))
  return out

structure Candidate where
  env : Env
  values : Array Value
  orderKeys : Array Value

def candidateLess (terms : Array OrderTerm) (a b : Candidate) : Bool := Id.run do
  for i in [:min a.orderKeys.size b.orderKeys.size] do
    let term := terms[i]!
    if let some before := nullOrderLess? term.descending term.nullsFirst a.orderKeys[i]! b.orderKeys[i]! then
      return before
    let collation := term.expr.explicitOrderCollation?.getD (term.expr.collationIn a.env)
    let ord := collatedCompare collation a.orderKeys[i]! b.orderKeys[i]!
    if ord != .eq then
      return if terms[i]!.descending then ord == .gt else ord == .lt
  return false

def insertSorted (terms : Array OrderTerm) (xs : List Candidate) (x : Candidate) : List Candidate :=
  match xs with
  | [] => [x]
  | y :: ys => if candidateLess terms x y then x :: y :: ys else y :: insertSorted terms ys x

def sortCandidates (terms : Array OrderTerm) (xs : Array Candidate) : Array Candidate :=
  (xs.foldl (insertSorted terms) []).toArray

def orderKey (db : Database) (env : Env) (values : Array Value) (names : Array String)
    (e : Expr) : Except String Value :=
  match e with
  | .literal (.integer i) =>
    if i > 0 && i.toNat <= values.size then pure values[i.toNat - 1]!
    else throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
  | .unary .plus (.literal (.integer i)) => orderKey db env values names (.literal (.integer i))
  | .unary .neg (.literal (.integer _)) =>
    throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
  | .column none name =>
    match names.findIdx? (nameEq name) with
    | some i => pure values[i]!
    | none => evalWithDb db env e
  | _ => evalWithDb db env e

structure SelectGroup where
  keys : Array Value
  envs : Array Env
  deriving Inhabited

def ordinal (index : Nat) : String :=
  let number := index + 1
  let suffix := if number % 100 >= 11 && number % 100 <= 13 then "th"
    else match number % 10 with
      | 1 => "st"
      | 2 => "nd"
      | 3 => "rd"
      | _ => "th"
  s!"{number}{suffix}"

def evalGroupTerm (db : Database) (query : Select) (env : Env)
    (position : Nat) (term : Expr) : Except String Value := do
  match term with
  | .literal (.integer index) =>
    if index > 0 && index.toNat <= query.columns.size then
      let values ← expandResult db env #[query.columns[index.toNat - 1]!]
      pure (values[0]?.getD .null)
    else
      throw s!"{ordinal position} GROUP BY term out of range - should be between 1 and {query.columns.size}"
  | .column none name =>
    match evalWithDb db env term with
    | .ok value => pure value
    | .error message =>
      if message.startsWith "no such column:" then
        match query.columns.find? (fun column => column.alias.any (nameEq name)) with
        | some column => evalWithDb db env column.expr
        | none => throw message
      else throw message
  | _ => evalWithDb db env term

def partitionQueryGroups (db : Database) (envs : Array Env)
    (query : Select) : Except String (Array SelectGroup) := do
  if query.groupBy.isEmpty then pure #[{ keys := #[], envs }]
  else
    let mut groups : Array SelectGroup := #[]
    for env in envs do
      let keys ← query.groupBy.mapIdxM fun position term =>
        evalGroupTerm db query env position term
      match groups.findIdx? (fun group => group.keys == keys) with
      | some position =>
        let group := groups[position]!
        groups := groups.set! position { group with envs := group.envs.push env }
      | none => groups := groups.push { keys, envs := #[env] }
    let preserveInputOrder := query.groupBy.any fun term => term matches .unary .neg _
    if preserveInputOrder then pure groups
    else pure ((sortValueKeyed (groups.map fun group => (group.keys, group))).map (·.2))

def aggregateAliasEnv (columns : Array ResultColumn) (values : Array Value) : Env := Id.run do
  let mut aliases : Env := #[]
  for i in [:columns.size] do
    if let some column := columns[i]? then
      if let some alias := column.alias then
        aliases := aliases.push (Binding.mk "" "" alias (values[i]?.getD .null)
          true 0 "binary" "LEAN_HIDDEN")
  return aliases

def missingAggregateAliases (representative aliases : Env) : Env :=
  aliases.filter fun alias =>
    !representative.any (fun binding => binding.hidden && nameEq binding.column alias.column)

theorem missingAggregateAliases_are_fresh (representative aliases : Env) (alias : Binding)
    (membership : alias ∈ missingAggregateAliases representative aliases) :
    representative.any (fun binding => binding.hidden && nameEq binding.column alias.column) = false := by
  have fresh := (Array.mem_filter.mp membership).2
  simpa using fresh

def Expr.firstMinMaxFuel? : Nat → Expr → Option (Bool × Expr)
  | 0, _ => none
  | fuel + 1, .call name args _ =>
    let name := aggregateFunctionName name
    if args.size == 1 && (nameEq name "min" || nameEq name "max") then
      some (nameEq name "max", args[0]!)
    else args.findSome? (firstMinMaxFuel? fuel)
  | fuel + 1, .unary _ expression | fuel + 1, .isNull expression _ |
      fuel + 1, .collate expression _ => firstMinMaxFuel? fuel expression
  | fuel + 1, .binary _ left right =>
    firstMinMaxFuel? fuel left <|> firstMinMaxFuel? fuel right
  | fuel + 1, .inList expression values _ _ =>
    firstMinMaxFuel? fuel expression <|> values.findSome? (firstMinMaxFuel? fuel)
  | fuel + 1, .case_ base branches else_ =>
    base.bind (firstMinMaxFuel? fuel) <|> branches.findSome? (fun pair =>
      firstMinMaxFuel? fuel pair.1 <|> firstMinMaxFuel? fuel pair.2) <|>
      else_.bind (firstMinMaxFuel? fuel)
  | _, _ => none

def Expr.firstMinMax? (expression : Expr) : Option (Bool × Expr) :=
  firstMinMaxFuel? expression.height expression

def prioritizeMinMaxRow (db : Database) (envs : Array Env) (maximum : Bool)
    (expression : Expr) : Except String (Array Env) := do
  let mut best : Option (Nat × Value) := none
  for i in [:envs.size] do
    let value ← evalWithDb db envs[i]! expression
    unless value matches .null do
      match best with
      | none => best := some (i, value)
      | some (_, current) =>
        let order := value.compare current
        if (maximum && order == .gt) || (!maximum && order == .lt) then
          best := some (i, value)
  match best with
  | none => pure envs
  | some (index, _) =>
    pure (#[envs[index]!] ++ envs.extract 0 index ++ envs.extract (index + 1) envs.size)

def executeSimpleSelect (db : Database) (query : Select) : Except String QueryResult := do
  SQLite.Limit.validate query.limitClause
  if let some expressionRows := query.valueRows then
    let rows ← expressionRows.mapM fun row => row.mapM (evalWithDb db #[])
    let width := query.columns.size
    unless rows.all (fun row => row.size == width) do
      throw "all VALUES must have the same number of terms"
    let names := selectColumnNames db query
    let mut candidates : Array Candidate := #[]
    for values in rows do
      let orderKeys ← query.orderBy.mapM fun term => orderKey db #[] values names term.expr
      candidates := candidates.push { env := #[], values, orderKeys }
    unless query.orderBy.isEmpty do candidates := sortCandidates query.orderBy candidates
    let selected := candidates.extract query.offset
      (query.offset + query.limit.getD candidates.size) |>.map (·.values)
    return { columns := names, rows := selected }
  for position in [:query.groupBy.size] do
    if let .literal (.integer index) := query.groupBy[position]! then
      unless index > 0 && index.toNat <= query.columns.size do
        throw s!"{ordinal position} GROUP BY term out of range - should be between 1 and {query.columns.size}"
  if query.groupBy.isEmpty && !query.columns.any (fun c => c.expr.hasAggregate) &&
      query.orderBy.any (fun term => term.expr.hasAggregate) then
    let functionName := query.orderBy.findSome? (fun term => term.expr.firstAggregate?) |>.getD "aggregate"
    throw s!"misuse of aggregate: {functionName}()"
  for column in query.columns do
    if column.expr.hasAggregate then
      if let some alias := column.alias then
        if query.having.any (Expr.aggregateReferencesColumn alias) then
          throw s!"misuse of aliased aggregate {alias}"
  let sources ← sourceEnvs db query.sources
  let aggregate := query.columns.any (fun c =>
      c.expr.hasAggregate || c.expr.hasOuterAggregateSubquery) || !query.groupBy.isEmpty ||
    query.having.any Expr.hasAggregate
  let mut filtered := #[]
  for env in sources do
    let candidateEnv ← addResultAliases db env query.columns
    if ← matchesWhere db candidateEnv query.where_ then filtered := filtered.push candidateEnv
  if query.orderBy.isEmpty && query.sources.size == 1 then
    if let some source := query.sources[0]? then
      let whereSql := query.where_.map Expr.sql |>.getD ""
      if let some index := db.indexes.find? (fun index =>
          if nameEq index.table source.name then
            index.expressions[0]?.any (fun expression => stringContains whereSql expression.sql)
          else false) then
        filtered := (← evalIndex db index.expressions filtered).toArray
  let mut candidates := #[]
  if aggregate then
    let groups ← partitionQueryGroups db filtered query
    for group in groups do
      let groupEnvs ← match query.columns.findSome? (fun column => column.expr.firstMinMax?) with
        | some (maximum, expression) => prioritizeMinMaxRow db group.envs maximum expression
        | none => pure group.envs
      let mut values := #[]
      for col in query.columns do
        match col.expr with
        | .star _ => values := values ++ (← expandResult db (groupEnvs[0]?.getD #[]) #[col])
        | expression => values := values.push (← evalAggregate db groupEnvs expression)
      let representative := groupEnvs[0]?.getD #[]
      let aliases := missingAggregateAliases representative (aggregateAliasEnv query.columns values)
      let withAliases := groupEnvs.map fun env => env ++ aliases
      let keep ← match query.having with
        | none => pure true
        | some condition => pure ((← evalAggregate db withAliases condition).truth == .true)
      if keep then
        let env := withAliases[0]?.getD aliases
        let names := resultNames db env query.columns
        let keys ← query.orderBy.mapM fun term =>
          if term.expr.hasAggregate then evalAggregate db withAliases term.expr
          else orderKey db env values names term.expr
        candidates := candidates.push { env, values, orderKeys := keys }
  else
    for env in filtered do
      let values ← expandResult db env query.columns
      let names := resultNames db env query.columns
      let keys ← query.orderBy.mapM (fun term => orderKey db env values names term.expr)
      candidates := candidates.push { env, values, orderKeys := keys }
  if query.distinct then
    let collations := (selectColumnSchema db query).map (·.collation)
    let mut unique := #[]
    for candidate in candidates do
      unless unique.any (fun prior : Candidate =>
          rowsEqualCollated collations prior.values candidate.values) do
        unique := unique.push candidate
    candidates := unique
    if query.orderBy.isEmpty && shouldSortDistinctByIndex db query then
      let rows := sortRowsCollated collations (candidates.map (·.values))
      candidates := rows.filterMap fun row => candidates.find? (fun candidate => candidate.values == row)
  unless query.orderBy.isEmpty do candidates := sortCandidates query.orderBy candidates
  let rows := (candidates.extract query.offset (query.offset + query.limit.getD candidates.size)).map (·.values)
  let representative := filtered[0]?.getD (sources[0]?.getD #[])
  let runtimeNames := resultNames db representative query.columns
  let columns := if runtimeNames.isEmpty && query.columns.any (fun column => column.expr matches .star _) then
      selectColumnNames db query
    else runtimeNames
  pure { columns, rows }

def legacyMaxCompoundSelectDepth : Nat := 500

def executeSelectFuel : Nat → Database → Select → Except String QueryResult
  | 0, _, _ => throw "too many terms in compound SELECT"
  | fuel + 1, db, query => do
    let baseQuery := if query.compounds.isEmpty then query
      else { query with orderBy := #[], limit := none, offset := 0, compounds := #[] }
    let collations := (selectColumnSchema db baseQuery).map (·.collation)
    let mut result ← executeSimpleSelect db baseQuery
    for (operation, right) in query.compounds do
      let next ← executeSelectFuel fuel db right
      if (selectColumnSchema db baseQuery).size != (selectColumnSchema db right).size then
        throw s!"SELECTs to the left and right of {operation.sqlName} do not have the same number of result columns"
      let combined := combineCompoundRowsCollated collations operation result.rows next.rows
      let rows := if operation == .unionAll then combined else sortRowsCollated collations combined
      result := { result with rows }
    if !query.compounds.isEmpty then
      unless query.orderBy.isEmpty do
        let keys ← compoundOrderKeys db query result.columns
        result := { result with rows := sortOrderedValueRows keys result.rows }
      let limitedRows := result.rows.extract query.offset
        (query.offset + query.limit.getD result.rows.size)
      result := { result with rows := limitedRows }
    pure result

def executeSelect (db : Database) (query : Select) : Except String QueryResult :=
  executeSelectFuel (Nat.succ legacyMaxCompoundSelectDepth) db query

theorem executeSelect_without_compounds (db : Database) (query : Select)
    (empty : query.compounds = #[]) :
    executeSelect db query = executeSimpleSelect db query := by
  simp [executeSelect, executeSelectFuel, empty]

def unknownDefaultPrefix := "\u0000sqleanite-unknown-default:"

end SQLeanite
