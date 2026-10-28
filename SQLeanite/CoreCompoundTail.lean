import SQLeanite.CoreCompound
import SQLeanite.CoreOrder

/-! Result-column binding, merge ordering and windows for compound SELECT.
The SQL boundary supplies validated leaf queries and their column collations. -/
namespace SQLeanite.CoreCompoundTail

structure Term where
  column : Nat
  specification : CoreOrder.KeySpec

/-- ORDER BY terms refer to existing result slots. They never evaluate a new
expression over a compound result row. -/
def keys (terms : List Term) (row : List Core.Value) : List Core.Value :=
  terms.map (fun term => row[term.column]?.getD .null)

def less (terms : List Term) (left right : List Core.Value) : Bool :=
  CoreOrder.keysLess (terms.map (·.specification)) (keys terms left) (keys terms right)

def sort (terms : List Term) (rows : List (List Core.Value)) : List (List Core.Value) :=
  rows.mergeSort (fun left right => !less terms right left)

def complete (kinds : List SQLite.Collation.Kind) (terms : List Term) : List Term :=
  terms ++ (List.range kinds.length).filterMap (fun column =>
    if terms.any (fun term => term.column == column) then none
    else some { column, specification := { descending := false, nullsFirst := true, collation := kinds[column]?.getD .binary } })

/-- SQLite's merge advances the left input on equal UNION keys, leaving the
right input's representative to be emitted. INTERSECT emits the left input. -/
def mergeFuel (operation : CompoundOp) (terms : List Term) :
    Nat → List (List Core.Value) → List (List Core.Value) → List (List Core.Value)
  | 0, _, _ => []
  | _ + 1, [], right => if operation == .unionAll || operation == .unionDistinct then right else []
  | _ + 1, left, [] => if operation == .intersect then [] else left
  | fuel + 1, a :: left, b :: right =>
      if less terms a b then
        if operation == .intersect then mergeFuel operation terms fuel left (b :: right)
        else a :: mergeFuel operation terms fuel left (b :: right)
      else if less terms b a then
        if operation == .unionAll || operation == .unionDistinct then
          b :: mergeFuel operation terms fuel (a :: left) right
        else mergeFuel operation terms fuel (a :: left) right
      else
        if operation == .unionAll || operation == .intersect then
          a :: mergeFuel operation terms fuel left (b :: right)
        else mergeFuel operation terms fuel left (b :: right)

def adjacentDistinct (kinds : List SQLite.Collation.Kind) :
    Option (List Core.Value) → List (List Core.Value) → List (List Core.Value)
  | _, [] => []
  | previous, row :: rows =>
      if previous.any (fun old => CoreCompound.compareCollated kinds old row == .eq) then
        adjacentDistinct kinds previous rows
      else row :: adjacentDistinct kinds (some row) rows

def merge (kinds : List SQLite.Collation.Kind) (operation : CompoundOp) (terms : List Term)
    (left right : List (List Core.Value)) : List (List Core.Value) :=
  let rows := mergeFuel operation terms (left.length + right.length + 1) left right
  if operation == .unionAll then rows else adjacentDistinct kinds none rows

def window (offset : Nat) (limit : Option Nat) (rows : List α) : List α :=
  match limit with
  | none => rows.drop offset
  | some count => (rows.drop offset).take count

structure Arm where
  columns : List ResultColumn
  context : Option CoreExpr.Context
  /-- Joined arms store source-bound result expressions and supply the same
  source binding for ORDER terms. Aliases are still checked before binding. -/
  bindExpression : Option (Expr → Option Expr) := none

/-- Resolve stored columns to their input positions before AST comparison.
Identifier and function spelling is case insensitive; string values are not. -/
def normalizeFuel (ctx : Option CoreExpr.Context) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
      let norm := normalizeFuel ctx fuel
      match expression with
      | .column qualifier name =>
          match ctx.bind (fun c => c.column? qualifier name) with
          | some index => .column none (toString index)
          | none => .column (qualifier.map String.toLower) name.toLower
      | .unary .neg (.literal (.real value) (some spelling)) =>
          if value == 9223372036854775808.0 && spelling.toInt? == some 9223372036854775808 then
            .literal (.integer (-9223372036854775808)) (some ("-" ++ spelling))
          else .unary .neg (.literal (.real value) (some spelling))
      | .unary op arg => .unary op (norm arg)
      | .binary op left right => .binary op (norm left) (norm right)
      | .call name args star => .call name.toLower (args.map norm) star
      | .isNull arg negated => .isNull (norm arg) negated
      | .inList arg values negated affinity => .inList (norm arg) (values.map norm) negated affinity
      | .collate arg name => .collate (norm arg) name.toLower
      | .case_ base branches otherwise => .case_ (base.map norm)
          (branches.map fun (condition, result) => (norm condition, norm result)) (otherwise.map norm)
      | _ => expression

def literalEqual : Value → Value → Bool
  | .null, .null => true
  | .integer a, .integer b => a == b
  | .real a, .real b => a.toBits == b.toBits
  | .text a, .text b => a == b
  | .textBytes a, .textBytes b | .blob a, .blob b => a == b
  | _, _ => false

/-- Structural comparison must keep operator nesting, CASE branches and
literal storage classes. SQL rendering is not an expression identity key. -/
def sameFuel : Nat → Expr → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, left, right =>
      let same := sameFuel fuel
      let optional (a b : Option Expr) := match a, b with
        | none, none => true | some a, some b => same a b | _, _ => false
      let arguments (a b : Array Expr) := a.size == b.size && (a.zip b).all (fun (a,b) => same a b)
      match left, right with
      | .literal a as, .literal b bs => literalEqual a b && as == bs
      | .column aq an, .column bq bn => aq == bq && an == bn
      | .star a, .star b => a == b
      | .unary ao a, .unary bo b => ao == bo && same a b
      | .binary ao al ar, .binary bo bl br => ao == bo && same al bl && same ar br
      | .call an aa ast, .call bn ba bst => an == bn && ast == bst && arguments aa ba
      | .isNull a an, .isNull b bn => an == bn && same a b
      | .inList a av an af, .inList b bv bn bf => an == bn && af == bf && same a b && arguments av bv
      | .collate a an, .collate b bn => an == bn && same a b
      | .case_ ab aa ae, .case_ bb ba be => optional ab bb && optional ae be &&
          aa.size == ba.size && (aa.zip ba).all (fun (a,b) => same a.1 b.1 && same a.2 b.2)
      | .scalarSubquery a, .scalarSubquery b | .existsSubquery a, .existsSubquery b => a == b
      | .inSubquery a aq an, .inSubquery b bq bn => an == bn && aq == bq && same a b
      | _, _ => false

def normalized (ctx : Option CoreExpr.Context) (expression : Expr) : Expr :=
  let bound := ctx.map (fun c => c.bindNames expression) |>.getD expression
  let prepared := SQLite.ExprCollation.strip (SQLite.Scalar.prepare bound)
  normalizeFuel ctx prepared.height prepared

def sameExpression (ctx : Option CoreExpr.Context) (left right : Expr) : Bool :=
  let left := normalized ctx left
  let right := normalized ctx right
  sameFuel (max left.height right.height) left right

/-- Connection/declared metadata is transparent when recognizing an output
alias. Value-changing operations remain part of the matching expression. -/
def aliasName? (expression : Expr) : Option String :=
  CoreOrder.bareName? (SQLite.ExprCollation.strip (SQLite.ExprCollation.stripDeclared expression))

theorem aliasName_encoded_input (encoding : Int) (name : String) :
    aliasName? (.call "__sqlean_encoded" #[.literal (.text "input"),.literal (.integer encoding),.column none name] false) = some name := rfl

def armPosition? (arm : Arm) (expression : Expr) : Option Nat := do
  if let some name := aliasName? expression then
    if let some index := arm.columns.findIdx? (fun c => c.alias.any (fun a => a.toLower == name.toLower)) then
      return index
  if let some bind := arm.bindExpression then
    let resolved ← bind expression
    return ← arm.columns.findIdx? (fun column => sameExpression none column.expr resolved)
  let resolved := match arm.context with
    | some ctx => CoreOrder.resolveNamesFuel ctx arm.columns expression.height expression
    | none => expression
  if arm.context.any (fun ctx => !ctx.namesBound resolved) then none
  else arm.columns.findIdx? (fun column => sameExpression arm.context column.expr resolved)

def resolve (arms : List Arm) (names : List (Option String)) (term : OrderTerm) : Except String Term := do
  let expression := SQLite.ExprCollation.strip (SQLite.Scalar.prepare term.expr)
  let column ← match CoreOrder.ordinal? expression with
    | some position =>
        if 1 ≤ position && position.toNat ≤ names.length then pure (position.toNat - 1)
        else throw "ORDER BY position is outside the result columns"
    | none => match arms.findSome? (fun arm => armPosition? arm expression) with
        | some index => pure index
        | none => throw "ORDER BY term does not match any column in the result set"
  let selected := (SQLite.ExprCollation.name term.expr).orElse (fun _ => names[column]?.getD none)
  let collation ← SQLite.ExprCollation.require (SQLite.ExprCollation.ofName selected)
  return { column, specification := { descending := term.descending, nullsFirst := term.nullsFirst.getD (!term.descending), collation } }

def orderTerm (term : Term) : OrderTerm :=
  { expr := .collate (.literal (.integer (Int.ofNat (term.column + 1))))
      (match term.specification.collation with | .binary | .binary16le | .binary16be => "BINARY" | .nocase => "NOCASE" | .rtrim => "RTRIM"),
    descending := term.specification.descending, nullsFirst := some term.specification.nullsFirst }

theorem window_zero (offset : Nat) (rows : List α) : window offset (some 0) rows = [] := by
  simp [window]

theorem window_subset (offset : Nat) (limit : Option Nat) (rows : List α) :
    window offset limit rows ⊆ rows := by
  cases limit with
  | none => exact List.drop_subset _ _
  | some count => exact List.Subset.trans (List.take_subset _ _) (List.drop_subset _ _)

theorem sort_perm (terms : List Term) (rows : List (List Core.Value)) :
    (sort terms rows).Perm rows := List.mergeSort_perm _ _

theorem adjacentDistinct_subset (kinds : List SQLite.Collation.Kind)
    (previous : Option (List Core.Value)) (rows : List (List Core.Value)) :
    adjacentDistinct kinds previous rows ⊆ rows := by
  induction rows generalizing previous with
  | nil => simp [adjacentDistinct]
  | cons row rows ih =>
      simp only [adjacentDistinct]
      split
      · exact List.Subset.trans (ih previous) (List.subset_cons_self _ _)
      · exact List.cons_subset_cons _ (ih (some row))

theorem mergeFuel_subset (operation : CompoundOp) (terms : List Term)
    (fuel : Nat) (left right : List (List Core.Value)) :
    mergeFuel operation terms fuel left right ⊆ left ++ right := by
  intro row member
  induction fuel generalizing left right with
  | zero => simp [mergeFuel] at member
  | succ fuel ih =>
      cases left with
      | nil =>
          simp only [mergeFuel] at member
          split at member <;> simp_all
      | cons a left =>
          cases right with
          | nil =>
              simp only [mergeFuel] at member
              split at member <;> simp_all
          | cons b right =>
              simp only [mergeFuel] at member
              repeat' (split at member)
              all_goals simp only [List.mem_cons, List.mem_append] at member ⊢
              all_goals grind

theorem merge_subset (kinds : List SQLite.Collation.Kind) (operation : CompoundOp)
    (terms : List Term) (left right : List (List Core.Value)) :
    merge kinds operation terms left right ⊆ left ++ right := by
  unfold merge
  split
  · exact mergeFuel_subset _ _ _ _ _
  · exact List.Subset.trans (adjacentDistinct_subset _ _ _) (mergeFuel_subset _ _ _ _ _)

theorem sameFuel_real_spelling (fuel : Nat) (value : Float) (left right : String) :
    sameFuel (fuel + 1) (.literal (.real value) (some left))
      (.literal (.real value) (some right)) = (left == right) := by
  simp [sameFuel, literalEqual]

end SQLeanite.CoreCompoundTail
