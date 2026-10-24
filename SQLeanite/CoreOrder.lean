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

def resolveNamesFuel (ctx : CoreExpr.Context) (columns : List ResultColumn) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
      let replacement := (bareName? expression).bind fun name =>
        if (ctx.column? none name).isSome then none else aliasExpression? columns name
      match replacement with
      | some result => ctx.bindNames result
      | none =>
          let resolve := resolveNamesFuel ctx columns fuel
          match expression with
          | .unary op arg => .unary op (resolve arg)
          | .binary op left right => .binary op (resolve left) (resolve right)
          | .call name args star =>
              if (SQLite.Scalar.quotedIdentifier? expression).isSome ||
                  (SQLite.Scalar.booleanKeyword? expression).isSome then ctx.bindNames expression
              else .call name (args.map resolve) star
          | .isNull arg negated => .isNull (resolve arg) negated
          | .inList arg values negated affinity => .inList (resolve arg) (values.map resolve) negated affinity
          | .case_ base branches otherwise => .case_ (base.map resolve)
              (branches.map fun (condition, result) => (resolve condition, resolve result)) (otherwise.map resolve)
          | .collate arg name => .collate (resolve arg) name
          | _ => expression

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

def resolve (ctx : CoreExpr.Context) (columns : List ResultColumn) (terms : List OrderTerm) :
    Except String (List OrderTerm) := do
  let expanded ← expandResults ctx columns
  terms.mapM fun term => do return { term with expr := ← resolveTerm ctx expanded term.expr }

/-- Explicit COLLATE operators propagate left first through the ordering AST,
matching sqlite3ExprCollSeq. Admitted stored columns currently use BINARY. -/
def collationNameFuel : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, expression =>
      let find := collationNameFuel fuel
      match expression with
      | .collate _ name => some name
      | .unary _ arg | .isNull arg _ | .inSubquery arg _ _ => find arg
      | .binary _ left right => (find left).orElse fun _ => find right
      | .call _ args _ => args.foldl (fun found arg => found.orElse fun _ => find arg) none
      | .inList arg values _ _ => values.foldl (fun found value => found.orElse fun _ => find value) (find arg)
      | .case_ base branches otherwise =>
          let found := branches.foldl (fun found (condition, result) =>
            found.orElse fun _ => (find condition).orElse fun _ => find result) (base.bind find)
          found.orElse fun _ => otherwise.bind find
      | _ => none

/-- Erase metadata only through operations whose values do not depend on a
collation. Comparisons, IN, CASE and scalar min/max/nullif retain their nested
wrappers and still require a future collation-aware scalar evaluator. -/
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
  let collation ← match collationNameFuel term.expr.height term.expr with
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
      if distinct && key.any seen.contains then
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
