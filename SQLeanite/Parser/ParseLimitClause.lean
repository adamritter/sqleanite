import SQLeanite.Parser.ParserState
import SQLeanite.SQLite.DefaultSyntax
import SQLeanite.SQLite.JoinType
import SQLeanite.SQLite.Limit

namespace SQLeanite

/-- Retain the original expression tree, including the comma spelling, for
independent replay; use the same scalar operations as other SQL expressions. -/
def parseLimitClause : ParserM (Option Nat × Nat × Option LimitClause) := do
  unless ← acceptKeyword "limit" do return (none, 0, none)
  let first ← parseExpr
  let clause ← if ← acceptSymbol "," then do
      let count ← parseExpr
      pure ({ count, offset := some first, comma := true } : LimitClause)
    else do
      let offset ← if ← acceptKeyword "offset" then some <$> parseExpr else pure none
      pure ({ count := first, offset } : LimitClause)
  -- CTAS can discard its SELECT when IF NOT EXISTS finds an existing table.
  -- Keep failed expressions intact; certified ordinary SELECTs reject them,
  -- while CTAS checks them only after its schema no-op decision.
  let (limit, offset) := (SQLite.Limit.resolve clause).toOption.getD (none, 0)
  return (limit, offset, some clause)

def parseOptionalNameList : ParserM (Option (Array String)) := do
  if ← acceptSymbol "(" then
    let mut names := #[(← expectIdent)]
    while ← acceptSymbol "," do names := names.push (← expectIdent)
    unless isSymbol (← peek) ")" do
      throw s!"syntax error after column name \"{names[names.size - 1]!}\""
    expectSymbol ")"
    pure (some names)
  else pure none

def isColumnConstraint : Token → Bool
  | .ident s => ["primary", "not", "null", "unique", "check", "default", "collate",
      "references", "constraint", "as"].contains s.toLower
  | _ => false

def skipTableConstraint : ParserM Unit := do
  let mut depth := 0
  let mut done := false
  while !done do
    match ← peek with
    | .symbol "(" => depth := depth + 1; discard <| advance
    | .symbol ")" =>
      if depth == 0 then done := true
      else depth := depth - 1; discard <| advance
    | .symbol "," =>
      if depth == 0 then done := true else discard <| advance
    | .eof => throw "incomplete input"
    | _ => discard <| advance

def parseConflictAction : ParserM ConflictAction := do
  if ← acceptKeyword "rollback" then pure .rollback
  else if ← acceptKeyword "abort" then pure .abort
  else if ← acceptKeyword "fail" then pure .fail
  else if ← acceptKeyword "ignore" then pure .ignore
  else if ← acceptKeyword "replace" then pure .replace
  else throw "expected conflict action"

def expectConstraintName : ParserM String := do
  let token ← advance
  let some name := SQLite.PragmaSyntax.nameToken false token | throw (syntaxError token)
  pure name

def consumeIgnoredConstraintNames : ParserM Unit := do
  while ← acceptKeyword "constraint" do discard <| expectConstraintName

def parseForeignReference : ParserM ForeignKeyDef := do
  let table ← expectIdent
  let column ← if ← acceptSymbol "(" then
    let name ← expectIdent
    expectSymbol ")"
    pure (some name)
    else pure none
  let mut cascade := false
  let mut scanningActions := true
  while scanningActions do
    if ← acceptKeyword "on" then
      if ← acceptKeyword "delete" then
        if ← acceptKeyword "cascade" then cascade := true
        else if ← acceptKeyword "no" then expectKeyword "action"
        else if ← acceptKeyword "set" then discard <| advance
        else discard <| advance
      else if ← acceptKeyword "update" then
        if ← acceptKeyword "no" then expectKeyword "action" else discard <| advance
      else scanningActions := false
    else scanningActions := false
  return { table, column, onDeleteCascade := cascade }

def parseTableConstraint : ParserM (Option TableConstraintDef) := do
  let mut constraintName := none
  while ← acceptKeyword "constraint" do constraintName := some (← expectConstraintName)
  let primary ← if ← acceptKeyword "primary" then expectKeyword "key" *> pure true
    else pure false
  if primary || (← acceptKeyword "unique") then
    expectSymbol "("
    let mut columns := #[]
    let mut collations : Array (Option String) := #[]
    let mut descending : Array Bool := #[]
    let mut autoIncrement := false
    let mut done := false
    while !done do
      columns := columns.push (← expectIdent)
      if isSymbol (← peek) "(" then
        throw "expressions prohibited in PRIMARY KEY and UNIQUE constraints"
      let collation ← if ← acceptKeyword "collate" then some <$> expectIdent else pure none
      collations := collations.push collation
      let desc ← if ← acceptKeyword "asc" then pure false else acceptKeyword "desc"
      descending := descending.push desc
      done := !(← acceptSymbol ",")
    if primary then autoIncrement := ← acceptKeyword "autoincrement"
    expectSymbol ")"
    let conflict ← if ← acceptKeyword "on" then
        expectKeyword "conflict" *> parseConflictAction
      else pure .abort
    consumeIgnoredConstraintNames
    pure (some { columns, collations, descending, primaryKey := primary, autoIncrement, conflict })
  else if ← acceptKeyword "check" then
    expectSymbol "("
    let sourceStart ← currentTokenPos
    let expression ← parseExpr
    let sourceStop ← currentTokenPos
    let sourceSql ← tokenSource sourceStart sourceStop
    expectSymbol ")"
    if ← acceptKeyword "on" then
      expectKeyword "conflict"
      discard <| parseConflictAction
    consumeIgnoredConstraintNames
    pure (some { columns := #[], check := some { expression, name := constraintName, sourceSql } })
  else if ← acceptKeyword "foreign" then
    expectKeyword "key"
    expectSymbol "("
    let mut columns := #[(← expectIdent)]
    if isSymbol (← peek) "(" then throw "near \"(\": syntax error"
    while ← acceptSymbol "," do columns := columns.push (← expectIdent)
    expectSymbol ")"
    expectKeyword "references"
    let references ← parseForeignReference
    consumeIgnoredConstraintNames
    pure (some { columns, references := some references })
  else
    skipTableConstraint
    pure none

def parseDefault : ParserM (Expr × String) := do
  let start ← currentTokenPos
  let expression ← match ← peek with
    | .quotedIdent name _ => advance *> pure (.literal (.text name))
    | .ident name => do
        let lower := name.toLower
        let st ← get
        let following := st.tokens[(nextTokenAt st.tokens st.pos).1 + 1]?
        let blob := lower == "x" && (match following with | some (.string _) => true | _ => false)
        if blob || ["null", "true", "false", "current_time", "current_date", "current_timestamp"].contains lower then
          parseUnary
        else if SQLite.DefaultSyntax.identifier name then advance *> pure (.literal (.text name))
        else throw (syntaxError (← peek))
    | _ => parseUnary
  let stop := (← get).pos
  let tokens := ((← get).tokens.extract start stop).toList.filter fun token =>
    match token with | .space _ => false | _ => true
  unless SQLite.DefaultSyntax.shape tokens do throw "invalid DEFAULT syntax"
  return (expression, ← tokenSource start stop)

def parseColumnDef : ParserM ColumnDef := do
  let name ← expectIdent
  let typeStart ← currentTokenPos
  let mut typeDepth := 0
  let mut scanningType := true
  while scanningType do
    match ← peek with
    | token@(.ident _) =>
      if typeDepth == 0 && isColumnConstraint token then scanningType := false
      else discard <| advance
    | .symbol "(" => typeDepth := typeDepth + 1; discard <| advance
    | .symbol ")" =>
      if typeDepth == 0 then scanningType := false
      else typeDepth := typeDepth - 1; discard <| advance
    | .symbol "," =>
      if typeDepth == 0 then scanningType := false else discard <| advance
    | .symbol ";" => scanningType := false
    | .eof => scanningType := false
    | _ => discard <| advance
  let typ ← tokenSource typeStart (← get).pos
  unless SQLite.ColumnType.valid typ do throw "invalid column type syntax"
  let mut defaultValue := none
  let mut defaultSql := none
  let mut earlierDefaults := #[]
  let mut generated := none
  let mut generatedStored := false
  let mut notNull := false
  let mut notNullConflict := ConflictAction.abort
  let mut primaryKey := false
  let mut autoIncrement := false
  let mut unique := false
  let mut conflict := ConflictAction.abort
  let mut collation := "binary"
  let mut references : Option ForeignKeyDef := none
  let mut check : Option CheckDef := none
  let mut earlierChecks : Array CheckDef := #[]
  let mut pendingConstraintName : Option String := none
  let mut scanning := true
  while scanning do
    if ← acceptKeyword "constraint" then pendingConstraintName := some (← expectConstraintName)
    else if ← acceptKeyword "default" then
      if generated.isSome then throw "cannot use DEFAULT on a generated column"
      if let some previous := defaultValue then
        earlierDefaults := earlierDefaults.push (previous, defaultSql.getD "")
      let (expression, source) ← parseDefault
      defaultValue := some expression
      defaultSql := some source
    else if ← acceptKeyword "generated" then
      if defaultValue.isSome || generated.isSome then throw s!"error in generated column \"{name}\""
      discard <| acceptKeyword "always"
      expectKeyword "as"
      expectSymbol "("
      generated := some (← parseExpr)
      expectSymbol ")"
      generatedStored := ← acceptKeyword "stored"
      if !generatedStored then discard <| acceptKeyword "virtual"
    else if ← acceptKeyword "as" then
      if defaultValue.isSome || generated.isSome then throw s!"error in generated column \"{name}\""
      expectSymbol "("
      generated := some (← parseExpr)
      expectSymbol ")"
      generatedStored := ← acceptKeyword "stored"
      if !generatedStored then discard <| acceptKeyword "virtual"
    else if ← acceptKeyword "not" then
      expectKeyword "null"
      notNull := true
      notNullConflict := .abort
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        notNullConflict := ← parseConflictAction
    else if ← acceptKeyword "null" then pure ()
    else if ← acceptKeyword "primary" then
      expectKeyword "key"
      primaryKey := true
      discard <| acceptKeyword "asc"
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        conflict := ← parseConflictAction
      if ← acceptKeyword "autoincrement" then autoIncrement := true
    else if ← acceptKeyword "unique" then
      unique := true
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        conflict := ← parseConflictAction
    else if ← acceptKeyword "references" then
      references := some (← parseForeignReference)
    else if ← acceptKeyword "collate" then collation := ← expectIdent
    else if ← acceptKeyword "check" then
      expectSymbol "("
      let sourceStart ← currentTokenPos
      let expression ← parseExpr
      let sourceStop ← currentTokenPos
      let sourceSql ← tokenSource sourceStart sourceStop
      expectSymbol ")"
      if let some previous := check then earlierChecks := earlierChecks.push previous
      check := some { expression, name := pendingConstraintName, sourceSql }
    else scanning := false
  pure (ColumnDef.mk name typ defaultValue generated notNull notNullConflict primaryKey unique conflict
    collation references check defaultSql autoIncrement earlierDefaults earlierChecks generatedStored)

def parseTableAlias : ParserM (Option String) := do
  if ← acceptKeyword "as" then some <$> expectAlias
  else parseImplicitAlias

def parseJoinConstraint : ParserM (Option Expr × Array String) := do
  let on ← if ← acceptKeyword "on" then some <$> parseExpr else pure none
  let mut usingColumns := #[]
  if ← acceptKeyword "using" then
    if on.isSome then throw "near USING: syntax error"
    expectSymbol "("
    usingColumns := usingColumns.push (← expectIdent)
    while ← acceptSymbol "," do usingColumns := usingColumns.push (← expectIdent)
    expectSymbol ")"
  return (on, usingColumns)

mutual
  def parseTableFactorFuel : Nat → ParserM (Array TableRef)
    | 0 => throw "parser stack overflow"
    | fuel + 1 => do
      if ← acceptSymbol "(" then
        if isKeyword (← peek) "select" || isKeyword (← peek) "values" then
          let sql ← captureSubquery
          let alias ← parseTableAlias
          let columnAliases := (← parseOptionalNameList).getD #[]
          pure #[{ name := "(subquery-0)", alias, columnAliases, subquerySql := some sql }]
        else
          let refs ← parseFromItemsFuel fuel
          expectSymbol ")"
          let alias ← parseTableAlias
          discard <| parseOptionalNameList
          pure (match alias with
            | none => refs
            | some name => refs.map fun ref => { ref with alias := some name })
      else
        let (schema, objectName) ← parseQualifiedName
        let name := match schema with
          | some schemaName => schemaName ++ "." ++ objectName
          | none => objectName
        let functionArgs ← if ← acceptSymbol "(" then do
            let mut arguments := #[]
            unless ← acceptSymbol ")" do
              arguments := arguments.push (← parseExpr)
              while ← acceptSymbol "," do arguments := arguments.push (← parseExpr)
              expectSymbol ")"
            pure (some arguments)
          else pure none
        let alias ← parseTableAlias
        let columnAliases := (← parseOptionalNameList).getD #[]
        pure #[{ name, schema, alias, columnAliases, functionArgs }]

  def parseFromItemsFuel : Nat → ParserM (Array TableRef)
    | 0 => throw "parser stack overflow"
    | fuel + 1 => do
      let mut sources ← parseTableFactorFuel fuel
      let mut scanning := true
      while scanning do
        if ← acceptSymbol "," then
          let mut right ← parseTableFactorFuel fuel
          let (joinOn, usingColumns) ← parseJoinConstraint
          if let some first := right[0]? then
            right := right.set! 0 { first with usingColumns := first.usingColumns ++ usingColumns }
          if let some condition := joinOn then
            let last := right.size - 1
            if let some final := right[last]? then
              let combined := final.joinOn.map (fun prior => Expr.binary .and prior condition) |>.getD condition
              right := right.set! last { final with joinOn := some combined }
          sources := sources ++ right
        else
          let joinStarter := match ← peek with
            | .ident word => ["natural", "left", "right", "full", "inner", "cross", "outer", "join"].contains word.toLower
            | _ => false
          if joinStarter then
            let mut words : Array String := #[]
            while !isKeyword (← peek) "join" do
              match ← advance with
              | .ident word => words := words.push word.toUpper
              | token => throw (syntaxError token)
            expectKeyword "join"
            let some kind := SQLite.JoinType.classify words.toList
              | throw s!"unknown join type: {String.intercalate " " words.toList}"
            let leftJoin := kind.left
            let rightJoin := kind.right
            let naturalJoin := kind.natural
            let mut right ← parseTableFactorFuel fuel
            let (joinOn, usingColumns) ← parseJoinConstraint
            if let some first := right[0]? then
              let mergedUsing := first.usingColumns ++ usingColumns
              let mergedNatural := first.naturalJoin || naturalJoin
              let mergedLeft := first.leftJoin || leftJoin
              let mergedRight := first.rightJoin || rightJoin
              let updated := { first with
                usingColumns := mergedUsing
                naturalJoin := mergedNatural
                leftJoin := mergedLeft
                rightJoin := mergedRight
                crossJoin := first.crossJoin || kind.cross }
              right := right.set! 0 updated
            if let some condition := joinOn then
              let last := right.size - 1
              if let some final := right[last]? then
                let combined := final.joinOn.map (fun prior => Expr.binary .and prior condition) |>.getD condition
                right := right.set! last { final with joinOn := some combined }
            sources := sources ++ right
          else scanning := false
      pure sources

end

def parserFromDepth : Nat := 1000

def parseFromItems : ParserM (Array TableRef) :=
  parseFromItemsFuel (Nat.succ parserFromDepth)

def parseValuesRows : ParserM (Array (Array Expr)) := do
  let mut rows := #[]
  let mut more := true
  while more do
    expectSymbol "("
    let mut row := #[]
    unless ← acceptSymbol ")" do
      row := row.push (← parseExpr)
      while ← acceptSymbol "," do row := row.push (← parseExpr)
      expectSymbol ")"
    rows := rows.push row
    more := ← acceptSymbol ","
  pure rows

def valuesQuery (rows : Array (Array Expr)) : Select :=
  let columns := (rows[0]?.getD #[]).mapIdx fun i expression =>
    ({ expr := expression, alias := some s!"column{i + 1}", sourceSql := some expression.sql } : ResultColumn)
  { columns, valueRows := some rows }

def parseResultColumn : ParserM ResultColumn := do
  let start ← currentTokenPos
  let expr ← parseExpr
  let stop ← currentTokenPos
  let sourceSql := some (← tokenSource start stop)
  let alias ←
    if ← acceptKeyword "as" then some <$> expectAlias
    else parseImplicitAlias
  match expr, alias with
  | .star _, some _ => throw "a result star cannot have an alias"
  | _, _ => pure { expr, alias, sourceSql }

end SQLeanite
