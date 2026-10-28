import SQLeanite.Syntax
import SQLeanite.SQLite.Collation

/-! Explicit expression collation selection from expr.c. Stored column
collations remain a separate schema property; the supported schema uses BINARY. -/
namespace SQLeanite.SQLite.ExprCollation

/-- FILTER's predicate does not contribute result collation metadata. -/
def callArguments (name : String) (arguments : Array Expr) (star : Bool) : Array Expr :=
  match arguments.toList with
  | aggregate :: _ :: rest =>
      if !star && (name == "__sqlean_aggregate_order" ||
          (name == "__sqlean_aggregate_filter" && rest.isEmpty)) then #[aggregate] else arguments
  | _ => arguments

theorem callArguments_map (name : String) (arguments : Array Expr) (star : Bool)
    (transform : Expr → Expr) :
    callArguments name (arguments.map transform) star = (callArguments name arguments star).map transform := by
  apply Array.toList_inj.mp
  cases arguments using Array.recOn with
  | mk expressions =>
      cases expressions with
      | nil => simp [callArguments]
      | cons first rest =>
          cases rest with
          | nil => simp [callArguments]
          | cons second rest =>
              simp only [callArguments, Array.toList_map, List.map_cons, List.isEmpty_map]
              split <;> simp_all

def nameFuel : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, expression =>
      let find := nameFuel fuel
      match expression with
      | .collate _ name => some name
      | .unary _ arg | .isNull arg _ | .inSubquery arg _ _ => find arg
      | .binary _ left right => (find left).orElse fun _ => find right
      | .call name args star =>
          (callArguments name args star).foldl (fun found arg => found.orElse fun _ => find arg) none
      | .inList arg values _ _ => values.foldl (fun found value => found.orElse fun _ => find value) (find arg)
      | .case_ base branches otherwise =>
          let found := branches.foldl (fun found (condition, result) =>
            found.orElse fun _ => (find condition).orElse fun _ => find result) (base.bind find)
          found.orElse fun _ => otherwise.bind find
      | _ => none

def name (expression : Expr) : Option String := nameFuel expression.height expression

/-- A column's declared BINARY collation propagates through unary plus and
CAST, even without an explicit COLLATE node. Other supported operators only
propagate explicit collation metadata. -/
def columnDefaultFuel : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      match expression with
      | .column .. => true
      | .unary .plus arg => columnDefaultFuel fuel arg
      | .call name args false =>
          if name.toLower.startsWith "cast_" then
            match args.toList with | [arg] => columnDefaultFuel fuel arg | _ => false
          else false
      | _ => false

/-- A declaration is implicit metadata, distinct from a COLLATE operator.
The source compiler creates this node only after binding an actual column. -/
def declared (expression : Expr) (collation : String) : Expr :=
  .call "__sqlean_declared_collation" #[expression, .literal (.text collation)] false

def declaredNameFuel : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, expression => match expression with
      | .unary .plus argument => declaredNameFuel fuel argument
      | .call name arguments false =>
          if name == "__sqlean_declared_collation" then
            match arguments.toList with | [_, .literal (.text collation) _] => some collation | _ => none
          else if name.toLower.startsWith "cast_" then
            match arguments.toList with | [argument] => declaredNameFuel fuel argument | _ => none
          else none
      | _ => none

def stripDeclared : Expr → Expr
  | .call "__sqlean_declared_collation" #[expression, .literal (.text _) _] false => stripDeclared expression
  | .collate expression collation => .collate (stripDeclared expression) collation
  | expression => expression

def effectiveName (expression : Expr) : Option String :=
  (name expression).orElse fun _ =>
    (declaredNameFuel expression.height expression).orElse fun _ =>
      if columnDefaultFuel expression.height expression then some "binary" else none

def ofName (name : Option String) : Option Collation.Kind :=
  match name with | none => some .binary | some name => Collation.named? name

def kind? (expression : Expr) : Option Collation.Kind := ofName (effectiveName expression)

def binaryKind? (left right : Expr) : Option Collation.Kind :=
  let explicit := (name left).orElse (fun _ => name right)
  ofName (explicit.orElse fun _ => (effectiveName left).orElse fun _ => effectiveName right)

def argumentsKind? (arguments : Array Expr) : Option Collation.Kind :=
  ofName (arguments.toList.findSome? effectiveName)

/-- Scalar min/max/nullif use the first argument with any collation,
including a declared column's BINARY default, before considering later args. -/
theorem argumentsKind_first (first : Expr) (rest : List Expr) (selected : String)
    (found : effectiveName first = some selected) :
    argumentsKind? (first :: rest).toArray = ofName (some selected) := by
  simp [argumentsKind?, found, List.findSome?]

theorem argumentsKind_column (qualifier : Option String) (column : String) (rest : List Expr) :
    argumentsKind? (Expr.column qualifier column :: rest).toArray = ofName (some "binary") := by
  simp [argumentsKind?, effectiveName, name, nameFuel, declaredNameFuel, columnDefaultFuel, Expr.height,
    List.findSome?]

def require (kind : Option Collation.Kind) : Except String Collation.Kind :=
  match kind with | some kind => .ok kind | none => .error "no such collation sequence"

/-- COLLATE preserves affinity. Unary plus still removes it. -/
def strip : Expr → Expr
  | .collate expression _ => strip expression
  | expression => expression

def compare (kind : Collation.Kind) (left right : Value) : Ordering :=
  match left, right with
  | .text a, .text b => Collation.compareText kind a.toUTF8.data.toList b.toUTF8.data.toList
  | .text a, .textBytes b => Collation.compareText kind a.toUTF8.data.toList b.toList
  | .textBytes a, .text b => Collation.compareText kind a.toList b.toUTF8.data.toList
  | .textBytes a, .textBytes b => Collation.compareText kind a.toList b.toList
  | _, _ => left.compare right

theorem name_collate (expression : Expr) (collation : String) :
    name (.collate expression collation) = some collation := rfl

theorem compare_text_self (kind : Collation.Kind) (text : String) :
    compare kind (.text text) (.text text) = .eq := by
  exact Collation.compareText_self kind text.toUTF8.data.toList

theorem explicit_overrides_declared (qualifier : Option String) (column : String) :
    binaryKind? (declared (.column qualifier column) "nocase")
      (.collate (.literal (.text "a")) "binary") = ofName (some "binary") := rfl

theorem effective_declared_column (qualifier : Option String) (column : String) :
    effectiveName (declared (.column qualifier column) "nocase") = some "nocase" := rfl

end SQLeanite.SQLite.ExprCollation
