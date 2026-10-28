import SQLeanite.Syntax.UnaryOp

/-! Semantic handling of SQLite's probability hints. These preserve their
first operand. LIKELIHOOD's second argument is checked as a REAL literal at
preparation, following resolve.c:exprProbability; INTEGER literals, unary
operators, COLLATE and computed constants do not meet that syntax rule. -/
namespace SQLeanite.SQLite.Probability

def recognizesName (name : String) : Bool :=
  ["likely", "unlikely", "likelihood"].contains (aggregateFunctionName name)

def probability : Expr → Bool
  | .literal (.real value) source =>
      !(source.any (fun spelling => spelling.toLower.startsWith "0x")) && 0.0 ≤ value && value ≤ 1.0
  | _ => false

def input? (name : String) (arguments : Array Expr) : Option Expr :=
  match aggregateFunctionName name, arguments.toList with
  | "likely", [argument] | "unlikely", [argument] => some argument
  | "likelihood", [argument, chance] => if probability chance then some argument else none
  | _, _ => none

theorem input_likely (name : String) (argument : Expr)
    (normalized : aggregateFunctionName name = "likely") :
    input? name #[argument] = some argument := by
  simp [input?, normalized]

theorem probability_integer (value : Int) (spelling : Option String) :
    probability (.literal (.integer value) spelling) = false := rfl

end SQLeanite.SQLite.Probability
