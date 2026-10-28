import SQLeanite.CoreTokenGrammar.Significant
import SQLeanite.SQLite.DefaultSyntax
import SQLeanite.SQLite.Limit

namespace SQLeanite
namespace CoreTokenGrammar

mutual
  def matchExprFuel : Nat → Expr → MatchM Unit
    | 0, _ => mismatch "an expression within the grammar depth bound"
    | fuel + 1, expression => fun state =>
        if isSymbol (nextSignificant state.remaining).1 "(" then
          let wrapped : MatchM Unit := do
            expectSymbol "("
            matchExprFuel fuel expression
            expectSymbol ")"
          match wrapped state with
          | .ok result => .ok result
          -- Parentheses may wrap the left operand, not the whole expression:
          -- (1+2)*3. Retry the AST node against the original token state.
          | .error _ => matchExprAlternative fuel expression state
        else matchExprAlternative fuel expression state

  def matchExprAlternative (fuel : Nat) (expression : Expr) : MatchM Unit :=
    fun state =>
      let between : MatchM Unit := do
        let (body, negated) := match expression with
          | .unary .not body => (body, true)
          | body => (body, false)
        match body with
        | .call "__sqlean_between" arguments false =>
            match arguments.toList with
            | [left, lower, upper] =>
                matchExprFuel fuel left
                if negated then expectKeyword "not"
                expectKeyword "between"
                matchExprFuel fuel lower
                expectKeyword "and"
                matchExprFuel fuel upper
            | _ => mismatch "three BETWEEN operands"
        | _ => mismatch "a BETWEEN expression"
      let pattern : MatchM Unit := do
        let (body, negated) := match expression with
          | .unary .not body => (body, true)
          | body => (body, false)
        match body with
        | .binary op left right =>
            unless op == .like || op == .glob do mismatch "LIKE or GLOB"
            matchExprFuel fuel left
            if negated then expectKeyword "not"
            expectBinaryOp op
            matchExprFuel fuel right
        | .call "regexp" arguments false =>
            match arguments.toList with
            | [pattern, input] =>
                matchExprFuel fuel input
                if negated then expectKeyword "not"
                expectKeyword "regexp"
                matchExprFuel fuel pattern
            | _ => mismatch "REGEXP expression"
        | .call "like" arguments false =>
            match arguments.toList with
            | [pattern, input, escape] =>
                matchExprFuel fuel input
                if negated then expectKeyword "not"
                expectKeyword "like"
                matchExprFuel fuel pattern
                expectKeyword "escape"
                matchExprFuel fuel escape
            | _ => mismatch "LIKE ... ESCAPE"
        | _ => mismatch "a pattern expression"
      let notIn : MatchM Unit := do
        let .unary .not (.inSubquery argument sql false) := expression | mismatch "NOT IN subquery"
        matchExprCore fuel (.inSubquery argument sql true)
      match between state with
      | .ok result => .ok result
      | .error _ => match pattern state with
          | .ok result => .ok result
          | .error _ => match notIn state with
              | .ok result => .ok result
              | .error _ => matchExprCore fuel expression state

  def matchExprCore : Nat → Expr → MatchM Unit
    | _, .literal value spelling => expectLiteralSpelling value spelling
    | _, .column none name => do
        traceReference (.column none name)
        expectPrimaryName false name
    | _, .column (some qualifier) name => do
        traceReference (.qualifier qualifier)
        expectPrimaryName true qualifier
        expectSymbol "."
        traceReference (.column (some qualifier) name)
        expectPrimaryName true name
    | _, .star none => expectSymbol "*"
    | _, .star (some qualifier) => do
        traceReference (.qualifier qualifier)
        expectPrimaryName true qualifier *> expectSymbol "." *> expectSymbol "*"
    | fuel, .unary operation argument => do
        match operation with
        | .plus => expectSymbol "+"
        | .neg => expectSymbol "-"
        | .not => expectKeyword "not"
        | .bitNot => expectSymbol "~"
        matchExprFuel fuel argument
    | fuel, .binary operation left right => do
        matchExprFuel fuel left
        expectBinaryOp operation
        matchExprFuel fuel right
    | fuel, .call name arguments star => do
        unless name == "__sqlean_aggregate_order" || arguments.size ≤ SQLite.Limits.maxFunctionArgs do
          mismatch "at most 1000 function arguments"
        if ["__sqlean_raise_ignore","__sqlean_raise_abort","__sqlean_raise_fail","__sqlean_raise_rollback"].contains name.toLower then
          unless isKeyword (← peek) "raise" do throw s!"no such function: {name}"
          unless !star do mismatch "RAISE expression syntax"
          expectKeyword "raise"
          expectSymbol "("
          let action := (name.toLower.drop 15).toString
          expectKeyword action
          if name.toLower == "__sqlean_raise_ignore" then
            unless arguments.isEmpty do mismatch "RAISE IGNORE without a message"
          else
            unless arguments.size == 1 do mismatch "a RAISE message expression"
            expectSymbol ","
            matchExprFuel fuel arguments[0]!
          expectSymbol ")"
        else if name == "__sqlean_aggregate_order" then
          match arguments.toList, star with
          | .call function inputs false :: ordering, false =>
              unless inputs.size ≤ SQLite.Limits.maxFunctionArgs &&
                  !ordering.isEmpty && ordering.length ≤ SQLite.Limits.maxColumns do
                mismatch "aggregate arguments and ORDER BY terms within their limits"
              expectName (aggregateFunctionName function)
              expectSymbol "("
              if isDistinctAggregateName function then expectKeyword "distinct"
              else discard <| acceptKeyword "all"
              match inputs.toList with
              | [] => pure ()
              | first :: rest =>
                  matchExprFuel fuel first
                  for next in rest do
                    expectSymbol ","
                    matchExprFuel fuel next
              expectKeyword "order"
              expectKeyword "by"
              let mut first := true
              for encoded in ordering do
                if !first then expectSymbol ","
                first := false
                let some term := AggregateOrder.decode? encoded | mismatch "an aggregate ORDER BY term"
                matchExprFuel fuel term.expr
                if term.descending then expectKeyword "desc"
                else discard <| acceptKeyword "asc"
                if let some nullsFirst := term.nullsFirst then
                  expectKeyword "nulls"
                  expectKeyword (if nullsFirst then "first" else "last")
              expectSymbol ")"
          | _, _ => mismatch "aggregate ORDER BY syntax"
        else if name.toLower == "__sqlean_encoded" || name.toLower == "__sqlean_bound_value" || name.toLower == "__sqlean_declared_collation" then
          throw s!"no such function: {name}"
        else if name == "__sqlean_window" then
          match arguments.toList, star with
          | [function, .literal (.text specification) none], false =>
              matchExprFuel fuel function
              expectKeyword "over"
              let tokens ← match lex specification with
                | .ok tokens => pure tokens
                | .error message => throw message
              for token in significant tokens.toList do
                unless token == .eof do
                  unless (← advance) == token do mismatch "the captured window specification"
          | _, _ => mismatch "function OVER window syntax"
        else if name == "__sqlean_aggregate_filter" then
          match arguments.toList, star with
          | [aggregate, condition], false =>
              matchExprFuel fuel aggregate
              expectKeyword "filter"
              expectSymbol "("
              expectKeyword "where"
              matchExprFuel fuel condition
              expectSymbol ")"
          | _, _ => mismatch "aggregate FILTER (WHERE expression)"
        else if aggregateFunctionName name == "__sqlean_between" then
          -- The alternative above is the only source syntax for this marker.
          mismatch "BETWEEN syntax, not an internal function call"
        else if name == "__sqlean_boolean_true" || name == "__sqlean_boolean_false" then
          unless arguments.isEmpty && !star do mismatch "a boolean keyword"
          expectKeyword (if name == "__sqlean_boolean_true" then "true" else "false")
        else if name == "lean_dqs" then
          match arguments.toList, star with
          | [.literal (.text expected)], false =>
              match ← advance with
              | .quotedIdent found _ =>
                  unless found.toLower == expected.toLower do
                    mismatch s!"quoted identifier {expected}"
              | _ => mismatch s!"quoted identifier {expected}"
          | _, _ => mismatch "a supported quoted identifier"
        else if name.toLower.startsWith "cast_" then
          match arguments.toList, star with
          | [argument], false =>
              expectKeyword "cast"
              expectSymbol "("
              matchExprFuel fuel argument
              expectKeyword "as"
              matchCastType (name.drop 5).toString
              expectSymbol ")"
          | _, _ => mismatch "CAST(expression AS type)"
        else
          let distinct := isDistinctAggregateName name
          let displayed := aggregateFunctionName name
          expectName displayed
          expectSymbol "("
          if star then
            expectSymbol "*"
          else
            if distinct then expectKeyword "distinct"
            else discard <| acceptKeyword "all"
            match arguments.toList with
            | [] => pure ()
            | argument :: rest =>
                matchExprFuel fuel argument
                for next in rest do
                  expectSymbol ","
                  matchExprFuel fuel next
          expectSymbol ")"
    | fuel, .isNull argument negated => do
        matchExprFuel fuel argument
        if !negated && (← acceptKeyword "isnull") then return
        if negated && (← acceptKeyword "notnull") then return
        if negated && (← acceptKeyword "not") then
          expectKeyword "null"
          return
        expectKeyword "is"
        if negated then expectKeyword "not"
        matchExprFuel fuel (.literal .null)
    | fuel, .inList argument values negated _ => do
        matchExprFuel fuel argument
        if negated then expectKeyword "not"
        expectKeyword "in"
        expectSymbol "("
        match values.toList with
        | [] => pure ()
        | value :: rest =>
            matchExprFuel fuel value
            for next in rest do
              expectSymbol ","
              matchExprFuel fuel next
        expectSymbol ")"
    | fuel, .collate argument name =>
        matchExprFuel fuel argument *> expectKeyword "collate" *> expectName name
    | fuel, .case_ base branches otherwise => do
        expectKeyword "case"
        if let some expression := base then matchExprFuel fuel expression
        if branches.isEmpty then mismatch "at least one WHEN branch"
        for (condition, result) in branches do
          expectKeyword "when"
          matchExprFuel fuel condition
          expectKeyword "then"
          matchExprFuel fuel result
        if let some expression := otherwise then
          expectKeyword "else"
          matchExprFuel fuel expression
        expectKeyword "end"
    | _, .scalarSubquery sql => do
        expectSymbol "("
        let tokens ← match lex sql with
          | .ok tokens => pure tokens
          | .error message => throw message
        traceReference (.captured sql)
        for token in significant tokens.toList do
          unless token == .eof do
            unless (← advance) == token do mismatch "the captured scalar subquery"
        expectSymbol ")"
    | fuel, .inSubquery argument sql negated => do
        matchExprFuel fuel argument
        if negated then expectKeyword "not"
        expectKeyword "in"
        let tokens ← match lex sql with
          | .ok tokens => pure tokens
          | .error message => throw message
        if ← acceptSymbol "(" then
          traceReference (.captured sql)
          for token in significant tokens.toList do
            unless token == .eof do
              unless (← advance) == token do mismatch "the captured IN subquery"
          expectSymbol ")"
        else matchInTable (significant tokens.toList)
    | _, .existsSubquery sql => do
        expectKeyword "exists"
        expectSymbol "("
        let tokens ← match lex sql with
          | .ok tokens => pure tokens
          | .error message => throw message
        traceReference (.captured sql)
        for token in significant tokens.toList do
          unless token == .eof do
            unless (← advance) == token do mismatch "the captured EXISTS subquery"
        expectSymbol ")"
end

def matchExpr (expression : Expr) : MatchM Unit := do
  -- The compatibility parser admits at most 1000 nested expression levels.
  -- A fixed allowance avoids recomputing the remaining token-list length for
  -- every literal in a bulk INSERT (which would make certification quadratic).
  matchExprFuel (expression.height + 1001) expression

/-- Replay the original expressions and independently derive the normalized
execution window. No computed count can substitute for source-token checking. -/
def matchLimit (query : Select) (deferErrors : Bool := false) : MatchM Unit := do
  match query.limitClause with
  | none =>
      unless query.limit.isNone && query.offset == 0 do mismatch "LIMIT/OFFSET clause"
  | some clause =>
      expectKeyword "limit"
      if clause.comma then
        let some offset := clause.offset | mismatch "a comma LIMIT offset"
        matchExpr offset
        expectSymbol ","
        matchExpr clause.count
      else
        matchExpr clause.count
        if let some offset := clause.offset then
          expectKeyword "offset"
          matchExpr offset
      let (limit, offset) ← match SQLite.Limit.resolve clause with
        | .ok result => pure result
        | .error _ =>
            if deferErrors then pure (none, 0)
            else mismatch "admitted LIMIT/OFFSET expressions"
      unless query.limit == limit && query.offset == offset do
        mismatch "the translated LIMIT/OFFSET values"

def matchExprList : List Expr → MatchM Unit
  | [] => pure ()
  | expression :: expressions => do
      matchExpr expression
      for next in expressions do
        expectSymbol ","
        matchExpr next

/-- ASC is the default index order. DESC remains rejected until the AST and
physical index metadata can retain and execute that ordering. -/
def matchAscendingIndexExprs : List Expr → MatchM Unit
  | [] => pure ()
  | expression :: expressions => do
      matchExpr expression
      discard <| acceptKeyword "asc"
      for next in expressions do
        expectSymbol ","
        matchExpr next
        discard <| acceptKeyword "asc"

def matchPragmaName (expected : String) : MatchM Unit := do
  let some found := SQLite.PragmaSyntax.nameToken false (← advance) |
    mismatch "a PRAGMA or schema name"
  unless found.toLower == expected.toLower do mismatch "the parsed PRAGMA or schema name"

/-- Replay one atom and its optional sign, independently of parsePragmaArgument.
In this context source spelling is retained even for compact integer literals. -/
def matchPragmaArgument (expression : Expr) : MatchM Unit := do
  let negative ← acceptSymbol "-"
  let positive ← if negative then pure false else acceptSymbol "+"
  let token ← advance
  match SQLite.PragmaSyntax.numeric negative token with
  | some (value, source) =>
      match expression with
      | .literal expected spelling =>
          unless expected == value && spelling == some source do
            mismatch "the PRAGMA numeric value and original spelling"
      | _ => mismatch "a numeric PRAGMA argument"
  | none =>
      if negative || positive then mismatch "a signed numeric PRAGMA argument"
      let some name := SQLite.PragmaSyntax.nameToken true token | mismatch "a PRAGMA name argument"
      match expression with
      | .column none expected | .literal (.text expected) none =>
          unless name == expected do mismatch "the original PRAGMA argument name"
      | _ => mismatch "a PRAGMA name argument"

def matchNameList : List String → MatchM Unit
  | [] => pure ()
  | name :: names => do
      expectName name
      for next in names do
        expectSymbol ","
        expectName next

def matchOptionalNameList : Option (Array String) → MatchM Unit
  | none => pure ()
  | some names =>
      expectSymbol "(" *> matchNameList names.toList <* expectSymbol ")"

def matchAlias : Option String → MatchM Unit
  | none => pure ()
  | some alias => do
      if ← acceptKeyword "as" then expectDeclaredName alias
      else
        let some found := SQLite.Identifier.aliasToken (← advance) | mismatch "an implicit alias"
        unless found == alias do mismatch "the declared implicit alias"

def matchDefault (expression : Expr) (source : String) : MatchM Unit := do
  let before := (← get).remaining.dropWhile fun token => match token with | .space _ => true | _ => false
  let token ← peek
  match token, expression with
  | .ident name, .literal (.text text) none =>
      unless SQLite.DefaultSyntax.identifier name && name == text &&
          !["true", "false", "current_time", "current_date", "current_timestamp"].contains name.toLower do
        mismatch "an identifier DEFAULT string"
      discard <| advance
  | .quotedIdent name _, .literal (.text text) none =>
      unless name == text do mismatch "a quoted DEFAULT string"
      discard <| advance
  | _, _ => matchExpr expression
  let after := (← get).remaining
  let consumed := before.take (before.length - after.length)
  unless SQLite.DefaultSyntax.shape (significant consumed) &&
      (String.join (consumed.map Token.render)).trimAscii.toString == source do
    mismatch "the complete original DEFAULT source"

def readConstraintName : MatchM String := do
  let some name := SQLite.PragmaSyntax.nameToken false (← advance) |
    mismatch "a legal constraint name"
  pure name

def matchConstraintName : MatchM Unit := discard readConstraintName

def matchCheck (check : CheckDef) (name : Option String) : MatchM Unit := do
  unless check.name == name do mismatch "the CHECK constraint name"
  expectSymbol "("
  let before := (← get).remaining
  matchExpr check.expression
  let after := (← get).remaining
  let actual := (String.join ((before.take (before.length - after.length)).map Token.render)).trimAscii.toString
  unless actual == check.sourceSql do mismatch "the exact CHECK expression source"
  expectSymbol ")"

def matchForeignReference (key : ForeignKeyDef) : MatchM Unit := do
  unless !key.onDeleteCascade do mismatch "an immediate NO ACTION foreign key"
  expectName key.table
  match key.column with
  | none => pure ()
  | some name => expectSymbol "(" *> expectName name <* expectSymbol ")"
  while ← acceptKeyword "on" do
    unless (← acceptKeyword "delete") || (← acceptKeyword "update") do
      mismatch "a foreign-key action event"
    expectKeyword "no"
    expectKeyword "action"

end CoreTokenGrammar

end SQLeanite
