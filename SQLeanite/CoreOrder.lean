import SQLeanite.CoreExpr
import SQLeanite.SQLite.Collation

/-! Single-source ORDER BY binding and the bounded sorter used by the live Core
expression path. Output aliases bind first only at the top of an ORDER term;
inside an expression, source columns take precedence over result aliases. -/
namespace SQLeanite.CoreOrder

/-- Expand stars before interpreting result-column positions. Function
admission is handled separately, so aggregate names can still be bound. -/
def expandResults (ctx : CoreExpr.Context) : List ResultColumn → Except String (List ResultColumn)
  | [] => .ok []
  | column :: columns => do
      let head ← match column.expr with
        | .star _ => do
            unless ctx.namesBound column.expr do throw "no such table in qualified star"
            pure (ctx.schema.catalogColumns.map fun c => ({ expr := .column none c.name } : ResultColumn))
        | _ => pure [column]
      return head ++ (← expandResults ctx columns)

def bareName? (expression : Expr) : Option String :=
  match expression with
  | .column none name => some name
  | _ => (SQLite.Scalar.quotedIdentifier? expression).orElse fun _ =>
      (SQLite.Scalar.booleanKeyword? expression).map SQLite.Scalar.booleanName

def aliasExpression? (columns : List ResultColumn) (name : String) : Option Expr :=
  (columns.find? fun column => column.alias.any (fun alias => alias.toLower == name.toLower)).map (·.expr)

/-- sqlite3ExprIsInteger recognizes signed unary chains whose underlying
literal fits its positive 31-bit payload. Larger literals are sort constants. -/
def ordinal? : Expr → Option Int
  | .literal (.integer value) =>
      if 0 ≤ value && value ≤ 2147483647 then some value else none
  | .unary .plus expression => ordinal? expression
  | .unary .neg expression => (ordinal? expression).map (- ·)
  | _ => none

def resolveNamesFuelWith (hasColumn : String → Bool) (columns : List ResultColumn) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
      let replacement := (bareName? expression).bind fun name =>
        if hasColumn name then none else aliasExpression? columns name
      match replacement with
      | some result => SQLite.Scalar.bindNames hasColumn result
      | none =>
          let resolve := resolveNamesFuelWith hasColumn columns fuel
          match expression with
          | .unary op arg => .unary op (resolve arg)
          | .binary op left right => .binary op (resolve left) (resolve right)
          | .call name args star =>
              if (SQLite.Scalar.quotedIdentifier? expression).isSome ||
                  (SQLite.Scalar.booleanKeyword? expression).isSome then SQLite.Scalar.bindNames hasColumn expression
              else .call name (args.map resolve) star
          | .isNull arg negated => .isNull (resolve arg) negated
          | .inList arg values negated affinity => .inList (resolve arg) (values.map resolve) negated affinity
          | .case_ base branches otherwise => .case_ (base.map resolve)
              (branches.map fun (condition, result) => (resolve condition, resolve result)) (otherwise.map resolve)
          | .collate arg name => .collate (resolve arg) name
          | _ => expression

def resolveNamesFuel (ctx : CoreExpr.Context) (columns : List ResultColumn) : Nat → Expr → Expr :=
  resolveNamesFuelWith (fun name => (ctx.column? none name).isSome) columns

theorem resolveNamesFuelWith_source (hasColumn : String → Bool) (columns : List ResultColumn)
    (fuel : Nat) (name : String) (bound : hasColumn name = true) :
    resolveNamesFuelWith hasColumn columns fuel (.column none name) = .column none name := by
  cases fuel <;> simp [resolveNamesFuelWith, bareName?, bound]

theorem resolveNamesFuelWith_alias (hasColumn : String → Bool) (columns : List ResultColumn)
    (fuel : Nat) (name : String) (expression : Expr) (absent : hasColumn name = false)
    (found : aliasExpression? columns name = some expression) :
    resolveNamesFuelWith hasColumn columns (fuel + 1) (.column none name) =
      SQLite.Scalar.bindNames hasColumn expression := by
  simp [resolveNamesFuelWith, bareName?, absent, found]

def resolveAliasesWith (hasColumn : String → Bool) (columns : List ResultColumn) (expression : Expr) : Expr :=
  let expression := SQLite.Scalar.prepare (SQLite.Scalar.bindNames hasColumn expression)
  resolveNamesFuelWith hasColumn columns expression.height expression

/-- Resolve top-level ORDER aliases before source names; nested references use
source-first resolution. Inserted result expressions are not recursively aliased. -/
def resolveOrderAliasesWith (hasColumn : String → Bool) (columns : List ResultColumn) : Expr → Expr
  | .collate expression name => .collate (resolveOrderAliasesWith hasColumn columns expression) name
  | expression => match (bareName? expression).bind (aliasExpression? columns) with
      | some result => SQLite.Scalar.bindNames hasColumn result
      | none => resolveAliasesWith hasColumn columns expression

def combineAliasConditions : Option Expr → Option Expr → Option Expr
  | none, right => right
  | left, none => left
  | some left, some right => some (.binary .and left right)

/-- WHERE splitting ignores COLLATE and valid probability-hint shells before
separating AND terms. Unary plus remains an ordinary expression operator. -/
def aliasOnTermsFuel : Nat → Expr → List Expr
  | 0, expression => [expression]
  | fuel + 1, expression => match expression with
    | .binary .and left right => aliasOnTermsFuel fuel left ++ aliasOnTermsFuel fuel right
    | .collate inner _ => aliasOnTermsFuel fuel inner
    | .call name arguments false => match SQLite.Probability.input? name arguments with
      | some inner => aliasOnTermsFuel fuel inner
      | none => [expression]
    | _ => [expression]

/-- SQLite's resolveAlias copies the output expression without EP_OuterON.
An alias replacing an entire WHERE-split ON term therefore becomes an ordinary
WHERE condition. A containing operator keeps its original ON status. -/
def resolveJoinOnTerm (hasColumn : String → Bool) (columns : List ResultColumn) (expression : Expr) :
    Option Expr × Option Expr :=
  match (bareName? expression).bind (fun name =>
      if hasColumn name then none else aliasExpression? columns name) with
  | some result => (none, some (SQLite.Scalar.bindNames hasColumn result))
  | none => (some (resolveAliasesWith hasColumn columns expression), none)

def resolveJoinOnAliases (hasColumn : String → Bool) (columns : List ResultColumn) (expression : Expr) :
    Option Expr × Option Expr :=
  let prepared := SQLite.Scalar.prepare (SQLite.Scalar.bindNames hasColumn expression)
  (aliasOnTermsFuel prepared.height prepared).foldl (fun prior term =>
    let resolved := resolveJoinOnTerm hasColumn columns term
    (combineAliasConditions prior.1 resolved.1, combineAliasConditions prior.2 resolved.2)) (none, none)

theorem resolveJoinOnTerm_alias (hasColumn : String → Bool) (columns : List ResultColumn)
    (name : String) (expression : Expr) (absent : hasColumn name = false)
    (found : aliasExpression? columns name = some expression) :
    resolveJoinOnTerm hasColumn columns (.column none name) =
      (none, some (SQLite.Scalar.bindNames hasColumn expression)) := by
  simp [resolveJoinOnTerm, bareName?, absent, found]

def needsAliasesWith (hasColumn : String → Bool) (columns : List ResultColumn) (expression : Expr) : Bool :=
  (SQLite.Scalar.prepare (SQLite.Scalar.bindNames hasColumn expression)).any fun node =>
    (bareName? node).any fun name => !hasColumn name && (aliasExpression? columns name).isSome

/-- WHERE resolves result aliases after parser-level simplification. Source
columns take precedence, and substituted result expressions are not recursively
resolved against other result aliases. -/
def resolveAliases (ctx : CoreExpr.Context) (columns : List ResultColumn) (expression : Expr) : Expr :=
  let expression := SQLite.Scalar.prepare (ctx.bindNames expression)
  resolveNamesFuel ctx columns expression.height expression

def needsAliases (ctx : CoreExpr.Context) (columns : List ResultColumn) (expression : Expr) : Bool :=
  (SQLite.Scalar.prepare (ctx.bindNames expression)).any fun node =>
    (bareName? node).any fun name =>
      (ctx.column? none name).isNone && (aliasExpression? columns name).isSome

theorem resolveAliases_literal (ctx : CoreExpr.Context) (columns : List ResultColumn)
    (value : Value) (spelling : Option String) :
    resolveAliases ctx columns (.literal value spelling) = .literal value spelling := rfl

def resolvePreparedTerm (ctx : CoreExpr.Context) (columns : List ResultColumn) : Expr → Except String Expr
  | .collate expression name => do
      let resolved ← resolvePreparedTerm ctx columns expression
      return .collate resolved name
  | expression => do
      if let some result := (bareName? expression).bind (aliasExpression? columns) then
        return ctx.bindNames result
      if let some position := ordinal? expression then
        unless 1 ≤ position && position.toNat ≤ columns.length do
          throw "ORDER BY position is outside the result columns"
        let some result := columns[position.toNat - 1]? | throw "ORDER BY position is out of range"
        return ctx.bindNames result.expr
      return resolveNamesFuel ctx columns expression.height expression

/-- Parser-level simplification precedes the resolver's ordinal recognition.
In particular a folded zero-AND becomes position zero and must be rejected. -/
def resolveTerm (ctx : CoreExpr.Context) (columns : List ResultColumn) (expression : Expr) :
    Except String Expr := resolvePreparedTerm ctx columns (SQLite.Scalar.prepare expression)

def ordinalLabel (index : Nat) : String :=
  let number := index + 1
  let suffix := if number % 100 ≥ 11 && number % 100 ≤ 13 then "th"
    else if number % 10 == 1 then "st" else if number % 10 == 2 then "nd"
    else if number % 10 == 3 then "rd" else "th"
  s!"{number}{suffix}"

def resolve (ctx : CoreExpr.Context) (columns : List ResultColumn) (terms : List OrderTerm) :
    Except String (List OrderTerm) := do
  let expanded ← expandResults ctx columns
  terms.zipIdx.mapM fun (term, index) => do
    let prepared := SQLite.ExprCollation.strip (SQLite.Scalar.prepare term.expr)
    if let some position := ordinal? prepared then
      unless 1 ≤ position && position.toNat ≤ expanded.length do
        throw s!"{ordinalLabel index} ORDER BY term out of range - should be between 1 and {expanded.length}"
    return { term with expr := ← resolveTerm ctx expanded term.expr }

/-- Explicit COLLATE operators propagate left first through the ordering AST,
matching sqlite3ExprCollSeq. Admitted stored columns currently use BINARY. -/
abbrev collationNameFuel := SQLite.ExprCollation.nameFuel

/-- Erase metadata only through operations whose values do not depend on a
collation. Comparisons, IN, CASE and scalar min/max/nullif retain their nested
wrappers for the collation-aware scalar evaluator. -/
def keyExpressionFuel : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
      let erase := keyExpressionFuel fuel
      match expression with
      | .collate arg _ => erase arg
      | .unary op arg => .unary op (erase arg)
      | .binary op left right =>
          if [.concat, .add, .sub, .mul, .div, .mod, .bitAnd, .bitOr,
              .shiftLeft, .shiftRight, .and, .or].contains op then .binary op (erase left) (erase right)
          else expression
      | .call name args star =>
          if ["min", "max", "nullif"].contains (SQLite.Scalar.scalarFunctionName name) then expression
          else .call name (args.map erase) star
      | .isNull arg negated => .isNull (erase arg) negated
      | _ => expression

def keyExpression (expression : Expr) : Expr := keyExpressionFuel expression.height expression

structure KeySpec where
  descending : Bool
  nullsFirst : Bool
  collation : SQLite.Collation.Kind

def specification (term : OrderTerm) : Except String KeySpec := do
  let collation ← match SQLite.ExprCollation.effectiveName term.expr with
    | none => pure SQLite.Collation.Kind.binary
    | some name => match SQLite.Collation.named? name with
        | some kind => pure kind
        | none => throw "no such collation sequence"
  return { descending := term.descending, nullsFirst := term.nullsFirst.getD (!term.descending), collation }

def validateTerm (ctx : CoreExpr.Context) (term : OrderTerm) : Except String Unit := do
  let _ ← specification term
  ctx.validate (keyExpression term.expr)

def keyLess (spec : KeySpec) (left right : Core.Value) : Bool :=
  match left, right with
  | .null, .null => false
  | .null, _ => spec.nullsFirst
  | _, .null => !spec.nullsFirst
  | _, _ =>
      let order := SQLite.Collation.compareValue spec.collation left right
      if spec.descending then order == .gt else order == .lt

/-- A separate NULL-placement flag applies before direction/collation. Equal
keys retain original input order, including NOCASE and RTRIM equalities. -/
def keysLess : List KeySpec → List Core.Value → List Core.Value → Bool
  | [], _, _ => false
  | _ :: _, [], _ => false
  | _ :: _, _, [] => false
  | spec :: specs, a :: as, b :: bs =>
      if keyLess spec a b then true
      else if keyLess spec b a then false else keysLess specs as bs

structure SortRow where
  projected : CoreExpr.ProjectedRow
  keys : List Core.Value

def insertStable (directions : List KeySpec) (row : SortRow) : List SortRow → List SortRow
  | [] => [row]
  | first :: rest =>
      if keysLess directions row.keys first.keys then row :: first :: rest
      else first :: insertStable directions row rest

/-- With LIMIT, SQLite compares the key to the current worst retained key
before evaluating a new output row. A row later evicted has still been
computed. DISTINCT must compute its output first to decide whether it is new. -/
def scanFuel (ctx : CoreExpr.Context) (condition : Option Expr) (expressions : List Expr)
    (terms : List OrderTerm) (directions : List KeySpec) (distinct : Bool) (capacity : Option Nat) :
    List (List Core.Value) → List (List Core.Value) → List SortRow → Except String (List SortRow)
  | [], _, sorted => .ok sorted
  | row :: rows, seen, sorted => do
      unless ← ctx.matches row condition do
        return ← scanFuel ctx condition expressions terms directions distinct capacity rows seen sorted
      let output ← if distinct || capacity.isNone then some <$> ctx.projectRow row expressions else pure none
      let key := output.map Core.distinctRowKey
      if distinct && key.any (fun output => seen.any (CoreExpr.distinctEqual expressions output)) then
        return ← scanFuel ctx condition expressions terms directions distinct capacity rows seen sorted
      let seen := if distinct then key.toList ++ seen else seen
      let keys ← ctx.projectRow row (terms.map (fun term => keyExpression term.expr))
      if capacity.any (fun count => sorted.length ≥ count) &&
          sorted.getLast?.any (fun last => !keysLess directions keys last.keys) then
        return ← scanFuel ctx condition expressions terms directions distinct capacity rows seen sorted
      let output ← match output with
        | some values => pure values
        | none => ctx.projectRow row expressions
      let next := insertStable directions { projected := { source := row, output }, keys } sorted
      let next := match capacity with | none => next | some count => next.take count
      scanFuel ctx condition expressions terms directions distinct capacity rows seen next

def scan (ctx : CoreExpr.Context) (condition : Option Expr) (expressions : List Expr)
    (terms : List OrderTerm) (distinct : Bool) (rows : List (List Core.Value))
    (offset : Nat) (limit : Option Nat) : Except String (List CoreExpr.ProjectedRow) := do
  if limit == some 0 then return []
  let directions ← terms.mapM specification
  let sorted ← scanFuel ctx condition expressions terms directions distinct (limit.map (· + offset)) rows [] []
  return (sorted.drop offset).map (·.projected)

theorem scan_limit_zero (ctx : CoreExpr.Context) (condition : Option Expr) (expressions : List Expr)
    (terms : List OrderTerm) (distinct : Bool) (rows : List (List Core.Value)) (offset : Nat) :
    scan ctx condition expressions terms distinct rows offset (some 0) = .ok [] := by
  simp [scan, pure, Except.pure]

theorem insertStable_length (directions : List KeySpec) (row : SortRow) (rows : List SortRow) :
    (insertStable directions row rows).length = rows.length + 1 := by
  induction rows with
  | nil => rfl
  | cons first rest ih => simp only [insertStable]; split <;> simp_all <;> omega

end SQLeanite.CoreOrder
