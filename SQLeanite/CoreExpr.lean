import SQLeanite.CoreDistinct
import SQLeanite.SQLSurface
import SQLeanite.PhysicalQuery

/-! Row expressions on the production Core values. Binding is checked on the
whole syntax tree before evaluation, even for empty tables and dead branches. -/
namespace SQLeanite.CoreExpr

structure Context where
  schema : Core.Schema
  sourceName : String

def Context.column? (ctx : Context) (qualifier : Option String) (name : String) : Option Nat := do
  if qualifier.any (fun q => q.toLower != ctx.sourceName.toLower) then none
  else
    match ctx.schema.columns.findIdx? (fun c => c.name == name.toLower) with
    | some i => some i
    | none => if ["rowid", "oid", "_rowid_"].contains name.toLower then
        some ctx.schema.primaryKey else none

def Context.affinity (ctx : Context) (expression : Expr) : Option SQLite.Affinity :=
  match expression with
  | .column qualifier name => do
      let index ← ctx.column? qualifier name
      return (← ctx.schema.columns[index]?).affinity
  | _ => SQLite.Scalar.expressionAffinity expression

def Context.admitted (ctx : Context) (expression : Expr) : Bool :=
  !expression.any (fun e => match e with
    | .column qualifier name => (ctx.column? qualifier name).isNone
    | _ => SQLite.Scalar.forbidden e)

def Context.validate (ctx : Context) (expression : Expr) : Except String Unit :=
  if ctx.admitted expression then .ok ()
  else .error "unsupported or unbound row expression"

/-- TEXT decoding is checked; no replacement character can silently change a
stored byte sequence while converting it to the expression representation. -/
def value : Core.Value → Except String Value
  | .null => .ok .null
  | .integer i => .ok (.integer i.value)
  | .realBits bits => .ok (.real (Float.ofBits (UInt64.ofNat bits.val)))
  | .blob payload => .ok (.blob payload.bytes.toArray)
  | .text payload => match String.fromUTF8? (ByteArray.mk payload.bytes.toArray) with
      | some s => .ok (.text s)
      | none => .error "unsupported verified SQL: invalid UTF-8 stored TEXT"

def Context.lookup (ctx : Context) (row : List Core.Value)
    (qualifier : Option String) (name : String) : Except String Value := do
  let index ← match ctx.column? qualifier name with
    | some i => .ok i
    | none => .error s!"no such column: {name}"
  match row[index]? with
  | some v => value v
  | none => .error "row expression column is outside the input row"

def Context.eval (ctx : Context) (row : List Core.Value) (expression : Expr) :
    Except String Value :=
  SQLite.Scalar.evalWith (ctx.lookup row) ctx.affinity expression

/-- Expand each star in place, keeping visible-column order and result width. -/
def Context.projection (ctx : Context) (columns : List ResultColumn) : Except String (List Expr) := do
  let mut expressions := []
  for column in columns do
    match column.expr with
    | .star qualifier =>
        if qualifier.any (fun q => q.toLower != ctx.sourceName.toLower) then
          throw "no such table or alias in qualified star"
        expressions := expressions ++ ctx.schema.catalogColumns.map (fun c => .column none c.name)
    | expression =>
        ctx.validate expression
        expressions := expressions ++ [expression]
  return expressions

def Context.projectRow (ctx : Context) (row : List Core.Value) : List Expr →
    Except String (List Core.Value)
  | [] => .ok []
  | e :: rest => do
      let v ← SQLSurface.value (← ctx.eval row e)
      return v :: (← ctx.projectRow row rest)

structure ProjectedRow where
  source : List Core.Value
  output : List Core.Value

/-- Share SQL numeric equivalence with direct-column Core queries. Keep the
first original output and its source row for the subsequent ordering step. -/
def distinctRows (rows : List ProjectedRow) : List ProjectedRow :=
  Core.stableDistinctBy (fun row => Core.distinctRowKey row.output) rows

def sourceLess : List (Nat × Bool) → ProjectedRow → ProjectedRow → Bool
  | [], _, _ => false
  | (index, descending) :: rest, a, b =>
      let order := PhysicalQuery.compareValue (a.source[index]?.getD .null)
        (b.source[index]?.getD .null)
      if order == .eq then sourceLess rest a b
      else if descending then order == .gt else order == .lt

def Context.projectRows (ctx : Context) (expressions : List Expr) (rows : List (List Core.Value)) :
    Except String (List ProjectedRow) :=
  rows.mapM (fun row => do return { source := row, output := ← ctx.projectRow row expressions })

theorem projectRow_width (ctx : Context) (row : List Core.Value)
    (expressions : List Expr) (output : List Core.Value)
    (success : ctx.projectRow row expressions = .ok output) :
    output.length = expressions.length := by
  induction expressions generalizing output with
  | nil => simp [Context.projectRow] at success; cases success; rfl
  | cons e rest ih =>
      simp only [Context.projectRow] at success
      cases ev : ctx.eval row e with
      | error message => simp [ev, bind, Except.bind] at success
      | ok v =>
          cases converted : SQLSurface.value v with
          | error message => simp [ev, converted, bind, Except.bind] at success
          | ok physical =>
              cases projected : ctx.projectRow row rest with
              | error message => simp [ev, converted, projected, bind, Except.bind] at success
              | ok tail =>
                  simp [ev, converted, projected, bind, Except.bind, pure, Except.pure] at success
                  cases success
                  simp [ih tail projected]

theorem eval_column (ctx : Context) (row : List Core.Value)
    (qualifier : Option String) (name : String) :
    ctx.eval row (.column qualifier name) = ctx.lookup row qualifier name := rfl

end SQLeanite.CoreExpr
