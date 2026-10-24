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

def effectiveName (expression : Expr) : Option String :=
  (name expression).orElse fun _ =>
    if columnDefaultFuel expression.height expression then some "binary" else none

def ofName (name : Option String) : Option Collation.Kind :=
  match name with | none => some .binary | some name => Collation.named? name

def kind? (expression : Expr) : Option Collation.Kind := ofName (name expression)

def binaryKind? (left right : Expr) : Option Collation.Kind :=
  ofName ((name left).orElse fun _ => name right)

def argumentsKind? (arguments : Array Expr) : Option Collation.Kind :=
  ofName (arguments.foldl (fun found arg => found.orElse fun _ => name arg) none)

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

end SQLeanite.SQLite.ExprCollation
