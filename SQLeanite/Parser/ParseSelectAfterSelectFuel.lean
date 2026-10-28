import SQLeanite.Parser.ParseLimitClause
import SQLeanite.SQLite.RowAssignment

namespace SQLeanite

def parseSelectAfterSelectFuel : Nat → Bool → ParserM Select
  | 0, _ => throw "too many nested SELECT terms"
  | fuel + 1, compoundArm => do
    let distinct ← acceptKeyword "distinct"
    if !distinct then discard <| acceptKeyword "all"
    let mut columns := #[(← parseResultColumn)]
    while ← acceptSymbol "," do columns := columns.push (← parseResultColumn)
    let mut sources := #[]
    if ← acceptKeyword "from" then
      sources := ← parseFromItems
      if sources.size > 64 then throw "at most 64 tables in a join"
      if isKeyword (← peek) "using" then throw "a JOIN clause is required before USING"
    let where_ ← if ← acceptKeyword "where" then some <$> parseExpr else pure none
    let mut groupBy := #[]
    if ← acceptKeyword "group" then
      expectKeyword "by"
      groupBy := groupBy.push (← parseExpr)
      while ← acceptSymbol "," do groupBy := groupBy.push (← parseExpr)
    let having ← if ← acceptKeyword "having" then some <$> parseExpr else pure none
    let mut query : Select := { columns, sources, where_, groupBy, having, distinct }
    unless compoundArm do
      let mut scanningCompounds := true
      while scanningCompounds do
        let operation ← if ← acceptKeyword "union" then
            pure (some (if ← acceptKeyword "all" then CompoundOp.unionAll else .unionDistinct))
          else if ← acceptKeyword "except" then pure (some .except)
          else if ← acceptKeyword "intersect" then pure (some .intersect)
          else pure none
        match operation with
        | none => scanningCompounds := false
        | some operation =>
          let arm ← if ← acceptKeyword "select" then parseSelectAfterSelectFuel fuel true
            else if ← acceptKeyword "values" then valuesQuery <$> parseValuesRows
            else throw (syntaxError (← peek))
          query := { query with compounds := query.compounds.push (operation, arm) }
          if query.compounds.size >= 500 then throw "too many terms in compound SELECT"
      let mut orderBy := #[]
      if ← acceptKeyword "order" then
        expectKeyword "by"
        let e ← parseExpr
        let desc ← acceptKeyword "desc"
        if !desc then discard <| acceptKeyword "asc"
        let nullsFirst ← parseNullOrder
        orderBy := orderBy.push { expr := e, descending := desc, nullsFirst }
        while ← acceptSymbol "," do
          let e ← parseExpr
          let desc ← acceptKeyword "desc"
          if !desc then discard <| acceptKeyword "asc"
          let nullsFirst ← parseNullOrder
          orderBy := orderBy.push { expr := e, descending := desc, nullsFirst }
      let (limit, offset, limitClause) ← parseLimitClause
      query := { query with orderBy, limit, offset, limitClause }
      if !orderBy.isEmpty || limitClause.isSome then
        let pending ← if ← acceptKeyword "union" then
            pure (some (if ← acceptKeyword "all" then "UNION ALL" else "UNION"))
          else if ← acceptKeyword "except" then pure (some "EXCEPT")
          else if ← acceptKeyword "intersect" then pure (some "INTERSECT")
          else pure none
        if let some operation := pending then
          if !orderBy.isEmpty then throw s!"ORDER BY clause should come after {operation} not before"
          else throw s!"LIMIT clause should come after {operation} not before"
    pure query

def maxCompoundSelectDepth : Nat := 500

def parseSelectAfterSelect (compoundArm : Bool := false) : ParserM Select :=
  parseSelectAfterSelectFuel (Nat.succ maxCompoundSelectDepth) compoundArm

def parseValuesAfterValues (rows : Array (Array Expr)) : ParserM Select := do
  let mut query := valuesQuery rows
  let mut scanningCompounds := true
  while scanningCompounds do
    let operation ← if ← acceptKeyword "union" then
        pure (some (if ← acceptKeyword "all" then CompoundOp.unionAll else .unionDistinct))
      else if ← acceptKeyword "except" then pure (some .except)
      else if ← acceptKeyword "intersect" then pure (some .intersect)
      else pure none
    match operation with
    | none => scanningCompounds := false
    | some operation =>
      let arm ← if ← acceptKeyword "select" then parseSelectAfterSelect true
        else if ← acceptKeyword "values" then valuesQuery <$> parseValuesRows
        else throw (syntaxError (← peek))
      query := { query with compounds := query.compounds.push (operation, arm) }
      if query.compounds.size >= 500 then throw "too many terms in compound SELECT"
  let mut orderBy := #[]
  if ← acceptKeyword "order" then
    expectKeyword "by"
    let expression ← parseExpr
    let descending ← acceptKeyword "desc"
    if !descending then discard <| acceptKeyword "asc"
    let nullsFirst ← parseNullOrder
    orderBy := orderBy.push { expr := expression, descending, nullsFirst }
    while ← acceptSymbol "," do
      let expression ← parseExpr
      let descending ← acceptKeyword "desc"
      if !descending then discard <| acceptKeyword "asc"
      let nullsFirst ← parseNullOrder
      orderBy := orderBy.push { expr := expression, descending, nullsFirst }
  let (limit, offset, limitClause) ← parseLimitClause
  query := { query with orderBy, limit, offset, limitClause }
  if !orderBy.isEmpty || limitClause.isSome then
    let pending ← if ← acceptKeyword "union" then
        pure (some (if ← acceptKeyword "all" then "UNION ALL" else "UNION"))
      else if ← acceptKeyword "except" then pure (some "EXCEPT")
      else if ← acceptKeyword "intersect" then pure (some "INTERSECT")
      else pure none
    if let some operation := pending then
      if !orderBy.isEmpty then throw s!"ORDER BY clause should come after {operation} not before"
      else throw s!"LIMIT clause should come after {operation} not before"
  pure query

def inlineCteSourceFuel : Nat → Select → String → String → Array String → Select
  | 0, query, _, _, _ => query
  | fuel + 1, query, name, sourceSql, columns =>
    { query with
      sources := query.sources.map fun source =>
        if source.name.toLower == name.toLower && source.subquerySql.isNone then
          { source with subquerySql := some sourceSql, columnAliases := columns }
        else source
      compounds := query.compounds.map fun (operation, arm) =>
        (operation, inlineCteSourceFuel fuel arm name sourceSql columns) }

def inlineCteSource (query : Select) (name sourceSql : String)
    (columns : Array String) : Select :=
  inlineCteSourceFuel query.compoundHeight query name sourceSql columns

def parseWithSelectQuery : ParserM Select := do
  discard <| acceptKeyword "recursive"
  let name ← expectIdent
  let columns := (← parseOptionalNameList).getD #[]
  expectKeyword "as"
  if ← acceptKeyword "not" then expectKeyword "materialized"
  else discard <| acceptKeyword "materialized"
  expectSymbol "("
  let sourceStart ← currentTokenPos
  if ← acceptKeyword "select" then discard <| parseSelectAfterSelect
  else if ← acceptKeyword "values" then discard <| parseValuesAfterValues (← parseValuesRows)
  else throw (syntaxError (← peek))
  let sourceStop ← currentTokenPos
  let sourceSql ← tokenSource sourceStart sourceStop
  expectSymbol ")"
  expectKeyword "select"
  let body ← parseSelectAfterSelect
  pure (inlineCteSource body name sourceSql columns)

def parseCreate (temporarySeen : Bool := false) (sourceStart : Option Nat := none) : ParserM Statement := do
  let temporary ← if temporarySeen then pure true
    else if ← acceptKeyword "temp" then pure true else acceptKeyword "temporary"
  if ← acceptKeyword "table" then
    let ifNotExists ← if ← acceptKeyword "if" then
      expectKeyword "not" *> expectKeyword "exists" *> pure true
      else pure false
    let (schema, objectName) ← parseQualifiedName
    let name := match schema with
      | some schemaName => if schemaName.toLower == "main" then objectName else schemaName ++ "." ++ objectName
      | none => if temporary then "temp." ++ objectName else objectName
    if ← acceptKeyword "as" then
      let query ← if ← acceptKeyword "select" then parseSelectAfterSelect
        else if ← acceptKeyword "values" then parseValuesAfterValues (← parseValuesRows)
        else throw (syntaxError (← peek))
      pure (.createTableAs name query ifNotExists)
    else
      expectSymbol "("
      let mut columns := #[]
      let mut constraints := #[]
      unless ← acceptSymbol ")" do
        let mut more := true
        while more do
          if isKeyword (← peek) "primary" || isKeyword (← peek) "unique" ||
             isKeyword (← peek) "check" || isKeyword (← peek) "foreign" ||
             isKeyword (← peek) "constraint" then
            if let some constraint ← parseTableConstraint then
              constraints := constraints.push constraint
          else columns := columns.push (← parseColumnDef)
          more := ← acceptSymbol ","
        expectSymbol ")"
      if ← acceptKeyword "without" then expectKeyword "rowid"
      if ← acceptKeyword "strict" then pure (.createStrictTable name columns constraints ifNotExists)
      else pure (.createTable name columns constraints ifNotExists)
  else if ← acceptKeyword "view" then
    let ifNotExists ← if ← acceptKeyword "if" then
      expectKeyword "not" *> expectKeyword "exists" *> pure true
      else pure false
    let name ← expectIdent
    let columns ← parseOptionalNameList
    expectKeyword "as"
    let query ← if ← acceptKeyword "select" then parseSelectAfterSelect
      else if ← acceptKeyword "with" then parseWithSelectQuery
      else throw (syntaxError (← peek))
    let sourceSql ← match sourceStart with
      | some start => tokenSource start (← currentTokenPos)
      | none => pure ""
    pure (.createView name columns query ifNotExists temporary sourceSql)
  else
    let unique ← acceptKeyword "unique"
    expectKeyword "index"
    let ifNotExists ← if ← acceptKeyword "if" then
      expectKeyword "not" *> expectKeyword "exists" *> pure true
      else pure false
    let (schema, objectName) ← parseQualifiedName
    let name := if schema.any (fun name => name.toLower != "main") then
        schema.map (· ++ "." ++ objectName) |>.getD objectName
      else objectName
    expectKeyword "on"
    let table ← expectIdent
    expectSymbol "("
    let mut expressions := #[]
    unless ← acceptSymbol ")" do
      let first ← parseExpr
      expressions := expressions.push first
      if !(← acceptKeyword "desc") then discard <| acceptKeyword "asc"
      while ← acceptSymbol "," do
        let term ← parseExpr
        expressions := expressions.push term
        if !(← acceptKeyword "desc") then discard <| acceptKeyword "asc"
      expectSymbol ")"
    let where_ ← if ← acceptKeyword "where" then some <$> parseExpr else pure none
    pure (.createIndex name table expressions unique where_ ifNotExists)

def parseDmlTableName (insideTrigger : Bool) : ParserM String := do
  let first ← expectAlias
  if ← acceptSymbol "." then
    if insideTrigger then
      throw "qualified table names are not allowed on INSERT, UPDATE, and DELETE statements within triggers"
    else pure (first ++ "." ++ (← expectAlias))
  else pure first

def parseDelete (insideTrigger : Bool := false) : ParserM Statement := do
  expectKeyword "from"
  let table ← parseDmlTableName insideTrigger
  if ← acceptKeyword "not" then
    expectKeyword "indexed"
    if insideTrigger then
      throw "the NOT INDEXED clause is not allowed on UPDATE or DELETE statements within triggers"
  if ← acceptKeyword "indexed" then
    expectKeyword "by"
    discard <| expectIdent
    if insideTrigger then
      throw "the INDEXED BY clause is not allowed on UPDATE or DELETE statements within triggers"
  let alias ← if ← acceptKeyword "as" then some <$> expectAlias else pure none
  let where_ ← if ← acceptKeyword "where" then some <$> parseExpr else pure none
  let mut returning := #[]
  if ← acceptKeyword "returning" then
    returning := returning.push (← parseResultColumn)
    while ← acceptSymbol "," do returning := returning.push (← parseResultColumn)
  pure (.delete table alias where_ returning)

/-- Try a scalar, a row of scalars, then an extra grouping layer. Each
alternative starts at the same token state, and nesting is fuel bounded. -/
def parseAssignmentValuesFuel : Nat → ParserM (Array Expr)
  | 0 => throw "parser stack overflow"
  | fuel + 1 => fun state =>
      let scalar : ParserM (Array Expr) := do return #[(← parseExpr)]
      let vector : ParserM (Array Expr) := do
        expectSymbol "("
        let mut expressions := #[(← parseExpr)]
        while ← acceptSymbol "," do expressions := expressions.push (← parseExpr)
        expectSymbol ")"
        return expressions
      let grouped : ParserM (Array Expr) := do
        expectSymbol "("
        let expressions ← parseAssignmentValuesFuel fuel
        expectSymbol ")"
        return expressions
      match scalar state with
      | .ok result => .ok result
      | .error message =>
          -- Row/group alternatives repair syntax ambiguity only. A scalar
          -- expression's resource-limit diagnostic is already definitive.
          if message != "incomplete input" && !(message.startsWith "near ") then .error message
          else match vector state with
            | .ok result => .ok result
            | .error message =>
                if message != "incomplete input" && !(message.startsWith "near ") then .error message
                else grouped state

def parseUpdateAssignment : ParserM (Array (String × Expr)) := do
  let names : Array String ← match ← parseOptionalNameList with
    | some names => pure names
    | none => do pure #[(← expectIdent)]
  expectSymbol "="
  let values ← parseAssignmentValuesFuel (parserExpressionDepth + 1)
  match SQLite.RowAssignment.bind names.toList values.toList with
  | .ok assignments => return assignments.toArray
  | .error message => throw message

def parseUpsertClauses : ParserM (Array UpsertClause) := do
  let mut clauses := #[]
  while isKeyword (← peek) "on" do
    if clauses.any (fun clause => clause.target.isNone) then throw (syntaxError (← peek))
    expectKeyword "on"
    expectKeyword "conflict"
    let target ← if ← acceptSymbol "(" then do
        let mut expressions := #[]
        let mut more := true
        while more do
          expressions := expressions.push (← parseExpr)
          if !(← acceptKeyword "desc") then discard <| acceptKeyword "asc"
          more ← acceptSymbol ","
        expectSymbol ")"
        pure (some expressions)
      else pure none
    let targetWhere ← if target.isSome && (← acceptKeyword "where") then some <$> parseExpr else pure none
    expectKeyword "do"
    let assignments ← if ← acceptKeyword "nothing" then pure none else do
      expectKeyword "update"
      expectKeyword "set"
      let mut assignments ← parseUpdateAssignment
      while ← acceptSymbol "," do assignments := assignments ++ (← parseUpdateAssignment)
      pure (some assignments)
    let where_ ← if assignments.isSome && (← acceptKeyword "where") then some <$> parseExpr else pure none
    clauses := clauses.push { target, targetWhere, assignments, where_ }
  return clauses

def parseInsert (initial : ConflictAction := .default)
    (insideTrigger : Bool := false) : ParserM Statement := do
  let mut conflict := initial
  let hasOr ← acceptKeyword "or"
  -- Conflict action, when present.
  if hasOr then
    conflict := ← parseConflictAction
  expectKeyword "into"
  let table ← parseDmlTableName insideTrigger
  let alias ← if ← acceptKeyword "as" then some <$> expectAlias else pure none
  let columns ← parseOptionalNameList
  let statement : Statement ← do
    if insideTrigger && isKeyword (← peek) "default" then throw (syntaxError (← peek))
    if ← acceptKeyword "default" then
      expectKeyword "values"
      pure (.insert table columns #[#[]] conflict)
    else if ← acceptKeyword "values" then
      let rows ← parseValuesRows
      if ["union", "except", "intersect"].any (isKeyword (← peek)) then
        pure (.insertSelect table columns (← parseValuesAfterValues rows) conflict)
      else pure (.insert table columns rows conflict)
    else if ← acceptKeyword "select" then
      pure (.insertSelect table columns (← parseSelectAfterSelect) conflict)
    else throw "expected VALUES, DEFAULT VALUES, or SELECT after INSERT"
  if isKeyword (← peek) "on" then
    if let .insert _ _ rows _ _ := statement then
      if rows.size == 1 && rows[0]!.isEmpty then throw (syntaxError (← peek))
  let clauses ← parseUpsertClauses
  let mut returning := #[]
  if ← acceptKeyword "returning" then
    if insideTrigger then throw "cannot use RETURNING in a trigger"
    returning := returning.push (← parseResultColumn)
    while ← acceptSymbol "," do returning := returning.push (← parseResultColumn)
  let statement ← match statement with
    | .insert target names rows policy _ => pure (.insert target names rows policy returning)
    | .insertSelect target names query policy _ => pure (.insertSelect target names query policy returning)
    | _ => throw "invalid INSERT source"
  return if clauses.isEmpty then statement else .upsert statement alias clauses

def parseUpdate (insideTrigger : Bool := false) : ParserM Statement := do
  let mut conflict := ConflictAction.default
  if ← acceptKeyword "or" then
    conflict := ← parseConflictAction
  let table ← parseDmlTableName insideTrigger
  if ← acceptKeyword "not" then
    expectKeyword "indexed"
    if insideTrigger then
      throw "the NOT INDEXED clause is not allowed on UPDATE or DELETE statements within triggers"
  if ← acceptKeyword "indexed" then
    expectKeyword "by"
    discard <| expectIdent
    if insideTrigger then
      throw "the INDEXED BY clause is not allowed on UPDATE or DELETE statements within triggers"
  let alias ← if ← acceptKeyword "as" then some <$> expectAlias else pure none
  expectKeyword "set"
  let mut assignments ← parseUpdateAssignment
  while ← acceptSymbol "," do
    assignments := assignments ++ (← parseUpdateAssignment)
  unless assignments.size ≤ SQLite.Limits.maxColumns do throw "too many columns in set list"
  let where_ ← if ← acceptKeyword "where" then some <$> parseExpr else pure none
  let mut returning := #[]
  if ← acceptKeyword "returning" then
    if insideTrigger then throw "cannot use RETURNING in a trigger"
    returning := returning.push (← parseResultColumn)
    while ← acceptSymbol "," do returning := returning.push (← parseResultColumn)
  pure (.update table alias assignments where_ conflict returning)

def Select.referencesSourceFuel : Nat → Select → String → Bool
  | 0, _, _ => false
  | fuel + 1, query, name =>
    query.sources.any (fun source => source.name.toLower == name.toLower) ||
      query.compounds.any (fun compound => referencesSourceFuel fuel compound.2 name)

def Select.referencesSource (query : Select) (name : String) : Bool :=
  query.referencesSourceFuel query.compoundHeight name

def recursiveCteParts? (name : String) (query : Select) :
    Option (Select × Select × Bool) := do
  let arms := query.compounds.toList
  let position ← arms.findIdx? (fun (_,arm) => arm.referencesSource name)
  let (operation,first) ← arms[position]?
  let seed := {
    query with
    compounds := (arms.take position).toArray
    orderBy := #[]
    limit := none
    offset := 0
    limitClause := none }
  let step := {
    first with
    compounds := first.compounds ++ (arms.drop (position + 1)).toArray
    orderBy := query.orderBy
    limit := query.limit
    offset := query.offset
    limitClause := query.limitClause }
  return (seed,step,operation == .unionAll)

def parseWithFuel : Nat → List String → ParserM Statement
  | 0, _ => throw "parser stack overflow"
  | fuel + 1, seen => do
    let name ← expectIdent
    if seen.contains name.toLower then throw s!"duplicate WITH table name: {name}"
    let columns := (← parseOptionalNameList).getD #[]
    expectKeyword "as"
    let materialization : CteMaterialization ← if ← acceptKeyword "not" then
        expectKeyword "materialized" *> pure .notMaterialized
      else do
        if ← acceptKeyword "materialized" then pure .materialized else pure .default
    expectSymbol "("
    let source : Statement ←
      if ← acceptKeyword "select" then pure (.select (← parseSelectAfterSelect))
      else if ← acceptKeyword "values" then do
        let rows ← parseValuesRows
        let query ← parseValuesAfterValues rows
        if query.compounds.isEmpty && query.orderBy.isEmpty && query.limitClause.isNone then
          pure (.values rows)
        else pure (.select query)
      else throw (syntaxError (← peek))
    expectSymbol ")"
    let body ←
      if ← acceptSymbol "," then parseWithFuel fuel (name.toLower :: seen)
      else if ← acceptKeyword "insert" then parseInsert
      else if ← acceptKeyword "replace" then parseInsert .replace
      else if ← acceptKeyword "update" then parseUpdate
      else if ← acceptKeyword "delete" then parseDelete
      else if ← acceptKeyword "select" then pure (.select (← parseSelectAfterSelect))
      else throw (syntaxError (← peek))
    match source with
    | .select query =>
        match recursiveCteParts? name query with
        | some (seed,step,all) => pure (.withRecursive name columns seed step all body materialization)
        | none => pure (.withCte name columns source body materialization)
    | _ => pure (.withCte name columns source body materialization)

def parseWith : ParserM Statement := do
  discard <| acceptKeyword "recursive"
  parseWithFuel ((← get).tokens.size + 1) []

end SQLeanite
