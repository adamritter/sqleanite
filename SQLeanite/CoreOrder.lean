import SQLeanite.CoreExpr

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
          | .collate arg name =>
              if name.toLower == "binary" then resolve arg else .collate (resolve arg) name
          | _ => expression

def resolveTerm (ctx : CoreExpr.Context) (columns : List ResultColumn) : Expr → Except String Expr
  | .collate expression name => do
      let resolved ← resolveTerm ctx columns expression
      -- All admitted stored columns and this sorter use BINARY. Other
      -- collations retain their wrapper and fail scalar admission explicitly.
      return if name.toLower == "binary" then resolved else .collate resolved name
  | expression => do
      if let some result := (bareName? expression).bind (aliasExpression? columns) then
        return ctx.bindNames result
      if let some position := ordinal? expression then
        unless 1 ≤ position && position.toNat ≤ columns.length do
          throw "ORDER BY position is outside the result columns"
        let some result := columns[position.toNat - 1]? | throw "ORDER BY position is out of range"
        return ctx.bindNames result.expr
      return resolveNamesFuel ctx columns expression.height expression

def resolve (ctx : CoreExpr.Context) (columns : List ResultColumn) (terms : List OrderTerm) :
    Except String (List OrderTerm) := do
  let expanded ← expandResults ctx columns
  terms.mapM fun term => do return { term with expr := ← resolveTerm ctx expanded term.expr }

/-- BINARY key order keeps the first input when all keys compare equal. -/
def keysLess : List Bool → List Core.Value → List Core.Value → Bool
  | [], _, _ => false
  | _ :: _, [], _ => false
  | _ :: _, _, [] => false
  | descending :: directions, a :: as, b :: bs =>
      let order := PhysicalQuery.compareValue a b
      if order == .eq then keysLess directions as bs
      else if descending then order == .gt else order == .lt

structure SortRow where
  projected : CoreExpr.ProjectedRow
  keys : List Core.Value

def insertStable (directions : List Bool) (row : SortRow) : List SortRow → List SortRow
  | [] => [row]
  | first :: rest =>
      if keysLess directions row.keys first.keys then row :: first :: rest
      else first :: insertStable directions row rest

/-- With LIMIT, SQLite compares the key to the current worst retained key
before evaluating a new output row. A row later evicted has still been
computed. DISTINCT must compute its output first to decide whether it is new. -/
def scanFuel (ctx : CoreExpr.Context) (condition : Option Expr) (expressions : List Expr)
    (terms : List OrderTerm) (distinct : Bool) (capacity : Option Nat) :
    List (List Core.Value) → List (List Core.Value) → List SortRow → Except String (List SortRow)
  | [], _, sorted => .ok sorted
  | row :: rows, seen, sorted => do
      unless ← ctx.matches row condition do
        return ← scanFuel ctx condition expressions terms distinct capacity rows seen sorted
      let output ← if distinct || capacity.isNone then some <$> ctx.projectRow row expressions else pure none
      let key := output.map Core.distinctRowKey
      if distinct && key.any seen.contains then
        return ← scanFuel ctx condition expressions terms distinct capacity rows seen sorted
      let seen := if distinct then key.toList ++ seen else seen
      let keys ← ctx.projectRow row (terms.map (·.expr))
      let directions := terms.map (·.descending)
      if capacity.any (fun count => sorted.length ≥ count) &&
          sorted.getLast?.any (fun last => !keysLess directions keys last.keys) then
        return ← scanFuel ctx condition expressions terms distinct capacity rows seen sorted
      let output ← match output with
        | some values => pure values
        | none => ctx.projectRow row expressions
      let next := insertStable directions { projected := { source := row, output }, keys } sorted
      let next := match capacity with | none => next | some count => next.take count
      scanFuel ctx condition expressions terms distinct capacity rows seen next

def scan (ctx : CoreExpr.Context) (condition : Option Expr) (expressions : List Expr)
    (terms : List OrderTerm) (distinct : Bool) (rows : List (List Core.Value))
    (offset : Nat) (limit : Option Nat) : Except String (List CoreExpr.ProjectedRow) := do
  if limit == some 0 then return []
  let sorted ← scanFuel ctx condition expressions terms distinct (limit.map (· + offset)) rows [] []
  return (sorted.drop offset).map (·.projected)

theorem scan_limit_zero (ctx : CoreExpr.Context) (condition : Option Expr) (expressions : List Expr)
    (terms : List OrderTerm) (distinct : Bool) (rows : List (List Core.Value)) (offset : Nat) :
    scan ctx condition expressions terms distinct rows offset (some 0) = .ok [] := by
  simp [scan, pure, Except.pure]

theorem insertStable_length (directions : List Bool) (row : SortRow) (rows : List SortRow) :
    (insertStable directions row rows).length = rows.length + 1 := by
  induction rows with
  | nil => rfl
  | cons first rest ih => simp only [insertStable]; split <;> simp_all <;> omega

end SQLeanite.CoreOrder
