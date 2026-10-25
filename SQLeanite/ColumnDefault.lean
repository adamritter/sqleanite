import SQLeanite.CoreTokenGrammar
import SQLeanite.SQLSurface

/-! A checked SQL source, evaluated only when its value is needed. Persisting
source preserves both DEFAULT timing and PRAGMA spelling. No evaluated value
or unverified AST is hidden in the schema certificate. -/
namespace SQLeanite.ColumnDefault

def expression (source : String) : Except String Expr := do
  let parsed ← CoreTokenGrammar.parseCertified ("CREATE TABLE t(a DEFAULT " ++ source ++ "\n)")
  let [.createTable "t" definitions constraints false] := parsed.statements.toList
    | throw "invalid DEFAULT declaration"
  let [column] := definitions.toList | throw "invalid DEFAULT column count"
  unless constraints.isEmpty && column.name == "a" && column.declaredType.isEmpty &&
      !column.notNull && !column.primaryKey && !column.unique && column.generated.isNone &&
      column.collation == "binary" && column.earlierDefaults.isEmpty &&
      column.defaultSql == some source do throw "invalid DEFAULT source boundary"
  let some expression := column.defaultValue | throw "missing DEFAULT expression"
  let expression := SQLite.Scalar.prepare expression
  if expression.any (fun node => match node with
      | .column .. | .star .. | .scalarSubquery .. | .inSubquery .. | .existsSubquery .. => true
      | .call "lean_dqs" _ _ => true
      | _ => false) then throw "default value is not constant"
  return expression

def valid (source : String) : Bool := (expression source).isOk

structure Spec where
  source : String
  checked : valid source = true
  deriving DecidableEq, Repr

def fromSource (source : String) : Option Spec :=
  if checked : valid source = true then some ⟨source, checked⟩ else none

theorem fromSource_spec (spec : Spec) : fromSource spec.source = some spec := by
  simp [fromSource, spec.checked]

/-- The pragma span excludes one outer pair of parentheses, then trims space. -/
def metadata (spec : Spec) : String :=
  let chars := spec.source.toList
  if chars.head? == some '(' then
    (String.ofList ((chars.drop 1).take (chars.length - 2))).trimAscii.toString
  else spec.source

/-- DEFAULT expressions are not name-bound as SELECT expressions are.
SQLite's code generator can eliminate statically true/false boolean subtrees
before checking the functions inside them. Other function errors stay delayed
until INSERT preparation, including errors in nonselected CASE branches. -/
def emittedFuel : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
      let recurse := emittedFuel fuel
      match expression with
      | .binary op left right =>
          if (op == .and || op == .or) && (SQLite.Scalar.staticTruth expression).isSome then
            .literal (.integer (if (SQLite.Scalar.staticTruth expression).getD false then 1 else 0))
          else .binary op (recurse left) (recurse right)
      | .unary op argument => .unary op (recurse argument)
      | .call name arguments star => .call name (arguments.map recurse) star
      | .isNull argument negated => .isNull (recurse argument) negated
      | .inList argument values negated affinity => .inList (recurse argument) (values.map recurse) negated affinity
      | .collate argument name => .collate (recurse argument) name
      | .case_ base branches otherwise => .case_ (base.map recurse)
          (branches.map fun pair => (recurse pair.1, recurse pair.2)) (otherwise.map recurse)
      | _ => expression

theorem emitted_boolean (fuel : Nat) (left right : Expr) (truth : Bool)
    (known : SQLite.Scalar.staticTruth (.binary .and left right) = some truth) :
    emittedFuel (fuel + 1) (.binary .and left right) =
      .literal (.integer (if truth then 1 else 0)) := by
  simp [emittedFuel, known]

def validateUse (spec : Spec) : Except String Unit := do
  let expression ← expression spec.source
  unless SQLite.Scalar.admitted (emittedFuel expression.height expression) do
    throw "unsupported or invalid DEFAULT expression"

def evaluate (spec : Spec) : Except String PhysicalCodec.Value := do
  let expression ← expression spec.source
  SQLSurface.literal (emittedFuel expression.height expression)

/-- The forms sqlite3ValueFromExpr can supply for pre-ADD-COLUMN records.
Arbitrary arithmetic and function calls require per-row execution instead. -/
def recordConstantFuel : Nat → Expr → Bool
  | 0, _ => false
  | _ + 1, .literal .. => true
  | fuel + 1, .unary .plus value | fuel + 1, .unary .neg value => recordConstantFuel fuel value
  | fuel + 1, .call name args false =>
      (SQLite.Scalar.booleanKeyword? (.call name args false)).isSome ||
        (name.startsWith "cast_" && args.size == 1 && (args.toList.all (recordConstantFuel fuel)))
  | _, _ => false

def recordConstant (value : Expr) : Bool := recordConstantFuel value.height value

def storedValue (spec : Spec) : Except String PhysicalCodec.Value := do
  let value ← expression spec.source
  unless recordConstant value do throw "Cannot add a column with non-constant default"
  SQLSurface.literal value

end SQLeanite.ColumnDefault
