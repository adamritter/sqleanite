import SQLeanite.CoreTokenGrammar.MatchExpr
import SQLeanite.SQLite.JoinType

namespace SQLeanite
namespace CoreTokenGrammar

def matchColumnConstraints (column : ColumnDef) : MatchM Unit := do
  if (SQLite.Collation.named? column.collation).isNone then
    throw s!"no such collation sequence: {column.collation}"
  unless (if column.generated.isSome then column.generatedStored else !column.generatedStored) &&
      column.references.all (fun key => !key.onDeleteCascade) do
    mismatch "a verified-Core column definition"
  let finalDefault ← match column.defaultValue, column.defaultSql with
    | none, none => pure []
    | some expression, some source => pure [(expression, source)]
    | _, _ => mismatch "consistent DEFAULT metadata"
  let defaults := column.earlierDefaults.toList ++ finalDefault
  let mut defaultIndex := 0
  let checks := column.earlierChecks.toList ++ column.check.toList
  let mut checkIndex := 0
  let mut pendingCheckName : Option String := none
  let mut sawNotNull := false
  let mut notNullConflict := ConflictAction.abort
  let mut sawUnique := false
  let mut sawPrimary := false
  let mut sawAutoIncrement := false
  let mut primaryConflict := ConflictAction.abort
  let mut sawCollation := false
  let mut sawReferences := false
  let mut sawGenerated := false
  let mut scanning := true
  while scanning do
    let checkName := pendingCheckName
    if ← acceptKeyword "constraint" then pendingCheckName := some (← readConstraintName)
    else if ← acceptKeyword "check" then
      let some check := checks[checkIndex]? | mismatch "a retained CHECK clause"
      matchCheck check checkName
      checkIndex := checkIndex + 1
    else if ← acceptKeyword "default" then
      let some (expression, source) := defaults[defaultIndex]? | mismatch "a declared DEFAULT clause"
      matchDefault expression source
      defaultIndex := defaultIndex + 1
    else if isKeyword (← peek) "not" then
      expectKeyword "not"
      expectKeyword "null"
      sawNotNull := true
      notNullConflict := .abort
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        notNullConflict := ← matchConflictAction
    else if isKeyword (← peek) "null" then
      expectKeyword "null"
    else if isKeyword (← peek) "primary" then
      expectKeyword "primary"
      expectKeyword "key"
      sawPrimary := true
      primaryConflict := .abort
      discard <| acceptKeyword "asc"
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        primaryConflict := ← matchConflictAction
      sawAutoIncrement := ← acceptKeyword "autoincrement"
    else if ← acceptKeyword "unique" then
      sawUnique := true
      primaryConflict := .abort
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        primaryConflict := ← matchConflictAction
    else if isKeyword (← peek) "generated" || isKeyword (← peek) "as" then
      if sawGenerated then mismatch "one generated expression"
      let some expression := column.generated | mismatch "a retained generated expression"
      if ← acceptKeyword "generated" then discard <| acceptKeyword "always"
      expectKeyword "as"
      expectSymbol "("
      matchExpr expression
      expectSymbol ")"
      expectKeyword "stored"
      sawGenerated := true
    else if ← acceptKeyword "references" then
      if sawReferences then mismatch "one retained REFERENCES clause"
      let some key := column.references | mismatch "a retained REFERENCES clause"
      matchForeignReference key
      sawReferences := true
    else if isKeyword (← peek) "collate" then
      expectKeyword "collate"
      expectName column.collation
      sawCollation := true
    else
      scanning := false
  unless sawGenerated == column.generated.isSome && sawReferences == column.references.isSome && checkIndex == checks.length && sawUnique == column.unique && defaultIndex == defaults.length && sawNotNull == column.notNull && notNullConflict == column.notNullConflict && sawPrimary == column.primaryKey && sawAutoIncrement == column.autoIncrement && primaryConflict == column.conflict &&
      (sawCollation || column.collation.toLower == "binary") do
    mismatch s!"the parsed constraints for column {column.name}"

def matchDeclaredType (source : String) : MatchM Unit := do
  unless SQLite.ColumnType.valid source do mismatch "a legal column type"
  unless source.isEmpty do
    let before := (← get).remaining.dropWhile fun token => match token with | .space _ => true | _ => false
    expectSource source
    let after := (← get).remaining
    let actual := (String.join ((before.take (before.length - after.length)).map Token.render)).trimAscii.toString
    unless actual == source do mismatch "the exact column type source"

def matchColumn (column : ColumnDef) : MatchM Unit := do
  expectDeclaredName column.name
  matchDeclaredType column.declaredType
  matchColumnConstraints column

def matchColumns : List ColumnDef → MatchM Unit
  | [] => pure ()
  | column :: columns => do
      matchColumn column
      for next in columns do
        expectSymbol ","
        matchColumn next

def matchTableForeign (constraint : TableConstraintDef) (key : ForeignKeyDef) : MatchM Unit := do
  unless constraint.columns.size == 1 && constraint.collations.isEmpty &&
      constraint.descending.isEmpty && !constraint.primaryKey && !constraint.autoIncrement &&
      constraint.check.isNone && constraint.conflict == .abort do
    mismatch "a retained single-column table foreign key"
  expectKeyword "foreign"
  expectKeyword "key"
  expectSymbol "("
  expectName constraint.columns[0]!
  expectSymbol ")"
  expectKeyword "references"
  matchForeignReference key

def matchTablePrimary (constraint : TableConstraintDef) : MatchM Unit := do
  unless constraint.columns.size == 1 &&
      constraint.collations.size == 1 && constraint.descending.size == 1 &&
      constraint.check.isNone && constraint.references.isNone do
    mismatch "a single-column table PRIMARY KEY"
  if constraint.primaryKey then
    expectKeyword "primary"
    expectKeyword "key"
  else expectKeyword "unique"
  expectSymbol "("
  expectName constraint.columns[0]!
  if let some collation := constraint.collations[0]! then
    expectKeyword "collate"
    expectName collation
  if constraint.descending[0]! then expectKeyword "desc"
  else discard <| acceptKeyword "asc"
  if constraint.autoIncrement then expectKeyword "autoincrement"
  expectSymbol ")"
  if ← acceptKeyword "on" then
    expectKeyword "conflict"
    expectConflict constraint.conflict
  else unless constraint.conflict == .abort do mismatch "the default table-key conflict action"

/-- Table CONSTRAINT names are standalone grammar productions, optionally
separated by commas. They can precede, follow or stand without an actual key.
Every actual key must still match exactly one retained AST constraint. -/
def matchTableConstraints (constraints : Array TableConstraintDef) : MatchM Unit := do
  let mut position := 0
  let mut pendingCheckName : Option String := none
  let mut more ← acceptSymbol ","
  while more do
    if ← acceptKeyword "constraint" then pendingCheckName := some (← readConstraintName)
    else
      let some constraint := constraints[position]? | mismatch "a retained table constraint"
      if let some check := constraint.check then
        unless constraint.columns.isEmpty && !constraint.primaryKey do mismatch "a table CHECK constraint"
        expectKeyword "check"
        matchCheck check pendingCheckName
        if ← acceptKeyword "on" then
          expectKeyword "conflict"
          discard matchConflictAction
      else if let some key := constraint.references then matchTableForeign constraint key
      else matchTablePrimary constraint
      pendingCheckName := none
      position := position + 1
    if ← acceptSymbol "," then more := true
    else more := isKeyword (← peek) "constraint" || isKeyword (← peek) "primary" || isKeyword (← peek) "unique" || isKeyword (← peek) "check" || isKeyword (← peek) "foreign"
  unless position == constraints.size do mismatch "all retained table constraints"

def skipSpaceTokens (tokens : List Token) : List Token :=
  tokens.dropWhile fun token => match token with | .space _ => true | _ => false

def matchResultColumn (column : ResultColumn) : MatchM Unit := do
  match column.expr, column.alias with
  | .star _, some _ => mismatch "a result star without an alias"
  | _, _ => pure ()
  let before := skipSpaceTokens (← get).remaining
  matchExpr column.expr
  let after := skipSpaceTokens (← get).remaining
  let source := (String.join ((before.take (before.length - after.length)).map Token.render)).trimAscii.toString
  unless column.sourceSql == some source do mismatch "the original result-expression source"
  matchAlias column.alias

def matchResultColumns : List ResultColumn → MatchM Unit
  | [] => mismatch "at least one result column"
  | column :: columns => do
      matchResultColumn column
      for next in columns do
        expectSymbol ","
        matchResultColumn next

def matchOrderTerm (term : OrderTerm) : MatchM Unit := do
  matchExpr term.expr
  if term.descending then expectKeyword "desc"
  else discard <| acceptKeyword "asc"
  if let some first := term.nullsFirst then
    expectKeyword "nulls"
    expectKeyword (if first then "first" else "last")

def matchOrderTerms : List OrderTerm → MatchM Unit
  | [] => pure ()
  | term :: terms => do
      matchOrderTerm term
      for next in terms do
        expectSymbol ","
        matchOrderTerm next

/-- Captured query text is replayed token by token. The execution layer must
certify this text as a SELECT before evaluating the derived table. -/
def matchCapturedQuery (sql : String) : MatchM Unit := do
  traceReference (.captured sql false)
  let tokens ← match lex sql with
    | .ok tokens => pure tokens
    | .error message => throw message
  for token in significant tokens.toList do
    unless token == .eof do
      unless (← advance) == token do mismatch "the captured subquery token stream"

def matchTableFactor (source : TableRef) : MatchM Unit := do
  unless source.columnAliases.isEmpty do mismatch "a table source without a column alias list"
  match source.subquerySql with
  | none =>
      match source.schema with
      | none => traceReference (.table source) *> expectObjectName source.name
      | some schema =>
          unless source.name.startsWith (schema ++ ".") do mismatch "the qualified table name"
          expectName schema
          expectSymbol "."
          traceReference (.table source)
          expectName (String.ofList (source.name.toList.drop (schema.length + 1)))
      if let some arguments := source.functionArgs then
        expectSymbol "("
        matchExprList arguments.toList
        expectSymbol ")"
  | some sql =>
      unless source.functionArgs.isNone do mismatch "a derived table without function arguments"
      unless source.schema.isNone do mismatch "an unqualified derived table"
      unless source.name == "(subquery-0)" do mismatch "a captured derived-table source"
      expectSymbol "("
      matchCapturedQuery sql
      expectSymbol ")"
  matchAlias source.alias

def matchJoinSource (source : TableRef) : MatchM Unit := do
  -- NATURAL/constraint conflicts are semantic errors, checked after a
  -- possible CTAS schema no-op. ON followed by USING is invalid syntax.
  unless !(source.joinOn.isSome && !source.usingColumns.isEmpty) do
    mismatch "a single legal join constraint"
  let kind ← if ← acceptSymbol "," then pure ({} : SQLite.JoinType.Flags)
    else do
      let mut words := []
      while !isKeyword (← peek) "join" do
        let some word := SQLite.JoinType.keyword (← advance)
          | mismatch "a join keyword"
        words := words ++ [word]
        if words.length > 3 then mismatch "at most three join keywords"
      expectKeyword "join"
      let some kind := SQLite.JoinType.classify words | mismatch "a valid join type"
      pure kind
  unless source.leftJoin == kind.left && source.rightJoin == kind.right &&
      source.naturalJoin == kind.natural && source.crossJoin == kind.cross do
    mismatch "the declared join type"
  matchTableFactor source
  if let some condition := source.joinOn then
    expectKeyword "on"
    matchExpr condition
  unless source.usingColumns.isEmpty do
    expectKeyword "using"
    expectSymbol "("
    matchNameList source.usingColumns.toList
    expectSymbol ")"

def matchSources : List TableRef → MatchM Unit
  | [] => pure ()
  | source :: sources => do
      unless !source.leftJoin && !source.rightJoin && !source.naturalJoin &&
          !source.crossJoin && source.joinOn.isNone && source.usingColumns.isEmpty do
        mismatch "a first table source without join attributes"
      matchTableFactor source
      for next in sources do matchJoinSource next

def matchRows : List (Array Expr) → MatchM Unit
  | [] => mismatch "at least one VALUES row"
  | row :: rows => do
      expectSymbol "("
      matchExprList row.toList
      expectSymbol ")"
      for next in rows do
        expectSymbol ","
        expectSymbol "("
        matchExprList next.toList
        expectSymbol ")"

/-- Replay the first VALUES row twice: once as result metadata and once as
its actual value row. Neither AST copy may hide a different expression. -/
def matchValuesBase (query : Select) (rows : Array (Array Expr)) : MatchM Unit := do
  unless query.sources.isEmpty && query.where_.isNone && query.groupBy.isEmpty &&
      query.having.isNone && !query.distinct && rows.all (fun row => !row.isEmpty) do
    mismatch "a nonempty VALUES row list without SELECT clauses"
  let some first := rows[0]? | mismatch "at least one VALUES row"
  unless first.size == query.columns.size do mismatch "VALUES result column count"
  for i in [:first.size] do
    let some value := first[i]? | mismatch "VALUES first row"
    let some column := query.columns[i]? | mismatch "VALUES result column"
    unless column.alias == some s!"column{i + 1}" && column.sourceSql == some value.sql do
      mismatch "VALUES result-column metadata"
  expectKeyword "values"
  let start ← get
  matchRows [query.columns.map (·.expr)]
  let afterColumns ← get
  set start
  matchRows [first]
  unless (← get).remaining == afterColumns.remaining do mismatch "the same first VALUES row"
  for row in rows.toList.drop 1 do
    expectSymbol ","
    matchRows [row]

def matchSelectBase (query : Select) : MatchM Unit := do
  if let some rows := query.valueRows then return ← matchValuesBase query rows
  expectKeyword "select"
  if query.distinct then expectKeyword "distinct"
  else discard <| acceptKeyword "all"
  matchResultColumns query.columns.toList
  unless query.sources.isEmpty do
    expectKeyword "from"
    matchSources query.sources.toList
  match query.where_ with
  | some predicate => expectKeyword "where" *> matchExpr predicate
  | none => pure ()
  unless query.groupBy.isEmpty do
    expectKeyword "group"
    expectKeyword "by"
    matchExprList query.groupBy.toList
  match query.having with
  | some predicate => expectKeyword "having" *> matchExpr predicate
  | none => pure ()

def matchCompoundOp : CompoundOp → MatchM Unit
  | .unionAll => expectKeyword "union" *> expectKeyword "all"
  | .unionDistinct => do
      expectKeyword "union"
      discard <| acceptKeyword "distinct"
  | .except => expectKeyword "except"
  | .intersect => expectKeyword "intersect"

def matchSelectArm (query : Select) : MatchM Unit := do
  let previous := (← get).query
  modify fun state => { state with query := some query }
  unless query.compounds.isEmpty && query.orderBy.isEmpty &&
      query.limit.isNone && query.offset == 0 && query.limitClause.isNone do
    mismatch "a compound SELECT arm without a local tail clause"
  matchSelectBase query
  modify fun state => { state with query := previous }

def matchSelect (query : Select) (deferLimitErrors : Bool := false) : MatchM Unit := do
  let previous := (← get).query
  modify fun state => { state with query := some query }
  matchSelectBase query
  for arm in query.compounds do
    matchCompoundOp arm.1
    matchSelectArm arm.2
  let lastValues := (query.compounds.toList.getLast?).map
    (fun arm => arm.2.valueRows.isSome) |>.getD query.valueRows.isSome
  if lastValues && (isKeyword (← peek) "order" || isKeyword (← peek) "limit") then
    mismatch "a final SELECT arm before ORDER BY or LIMIT"
  unless query.orderBy.isEmpty do
    expectKeyword "order"
    expectKeyword "by"
    modify fun state => { state with outputAliases := true }
    matchOrderTerms query.orderBy.toList
    modify fun state => { state with outputAliases := false }
  matchLimit query deferLimitErrors
  modify fun state => { state with query := previous }

def viewCteSources : Nat → Select → String → List TableRef
  | 0, _, _ => []
  | fuel + 1, query, name =>
      (query.sources.toList.filter fun source => source.name.toLower == name.toLower &&
        source.schema.isNone && source.subquerySql.isSome) ++
      query.compounds.toList.flatMap (fun (_,arm) => viewCteSources fuel arm name)

def removeViewCte : Nat → Select → String → Select
  | 0, query, _ => query
  | fuel + 1, query, name => { query with
      sources := query.sources.map fun source =>
        if source.name.toLower == name.toLower && source.schema.isNone && source.subquerySql.isSome then
          { source with subquerySql := none, columnAliases := #[] }
        else source
      compounds := query.compounds.map fun (op,arm) => (op,removeViewCte fuel arm name) }

/-- Replay the retained, single referenced WITH source and its inlined AST
independently of the compatibility parser. Captured SQL is certified on use. -/
def matchViewSelect (query : Select) : MatchM Unit := do
  if ← acceptKeyword "with" then
    discard <| acceptKeyword "recursive"
    let some name := SQLite.Identifier.nameToken (← advance) | mismatch "a view CTE name"
    let sources := viewCteSources query.compoundHeight query name
    let some source := sources.head? | mismatch "a referenced view CTE"
    let some sql := source.subquerySql | mismatch "the captured view CTE"
    unless sources.all (fun other => other.subquerySql == some sql && other.columnAliases == source.columnAliases) do
      mismatch "the same view CTE at every reference"
    unless source.columnAliases.isEmpty do
      expectSymbol "("
      matchNameList source.columnAliases.toList
      expectSymbol ")"
    expectKeyword "as"
    if ← acceptKeyword "not" then expectKeyword "materialized"
    else discard <| acceptKeyword "materialized"
    expectSymbol "("
    matchCapturedQuery sql
    expectSymbol ")"
    matchSelect (removeViewCte query.compoundHeight query name)
  else matchSelect query

/-- Replay a tuple's target names against consecutive flattened AST pairs,
returning exactly their associated expressions and the untouched remainder. -/
def matchAssignmentNames : List (String × Expr) → MatchM (List Expr × List (String × Expr))
  | [] => mismatch "an assignment target"
  | (name, expression) :: rest => do
      expectName name
      if ← acceptSymbol ")" then return ([expression], rest)
      expectSymbol ","
      let (expressions, remaining) ← matchAssignmentNames rest
      return (expression :: expressions, remaining)

def matchAssignmentValues : Nat → List Expr → MatchM Unit
  | 0, _ => mismatch "bounded assignment parentheses"
  | fuel + 1, expressions => fun state =>
      let direct : MatchM Unit := match expressions with
        | [] => mismatch "an assignment value"
        | [expression] => matchExpr expression
        | _ => do
            expectSymbol "("
            matchExprList expressions
            expectSymbol ")"
      let grouped : MatchM Unit := do
        expectSymbol "("
        matchAssignmentValues fuel expressions
        expectSymbol ")"
      match direct state with
      | .ok result => .ok result
      | .error _ => grouped state

def matchAssignmentGroups : Nat → List (String × Expr) → MatchM Unit
  | 0, _ => mismatch "bounded assignment groups"
  | _ + 1, [] => pure ()
  | fuel + 1, (name, expression) :: rest => do
      let (expressions, remaining) ← do
        if ← acceptSymbol "(" then matchAssignmentNames ((name, expression) :: rest)
        else do expectName name; pure ([expression], rest)
      expectSymbol "="
      matchAssignmentValues ((← get).remaining.length + 1) expressions
      unless remaining.isEmpty do
        expectSymbol ","
        matchAssignmentGroups fuel remaining

def matchAssignments (assignments : List (String × Expr)) : MatchM Unit := do
  unless !assignments.isEmpty && assignments.length ≤ SQLite.Limits.maxColumns do
    mismatch "between 1 and 2000 UPDATE targets"
  matchAssignmentGroups (assignments.length + 1) assignments

end CoreTokenGrammar

end SQLeanite
