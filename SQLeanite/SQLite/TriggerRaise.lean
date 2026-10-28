import SQLeanite.Syntax.UnaryOp

namespace SQLeanite.SQLite.TriggerRaise

/-- Context specialization for certified RAISE syntax. The executable private
name cannot be introduced by a public function call. Traversal evaluates no
branch or message, preserving ordinary scalar preparation and lazy execution. -/
def bindFuel : Nat → Expr → Expr
  | 0,expression => expression
  | fuel+1,expression =>
      let visit := bindFuel fuel
      match expression with
      | .call name arguments star =>
          let name := if name.toLower == "__sqlean_raise_abort" && !star then "__sqlean_trigger_abort" else name
          .call name (arguments.map visit) star
      | .unary op argument => .unary op (visit argument)
      | .binary op left right => .binary op (visit left) (visit right)
      | .isNull argument negated => .isNull (visit argument) negated
      | .inList argument values negated affinity => .inList (visit argument) (values.map visit) negated affinity
      | .inSubquery argument sql negated => .inSubquery (visit argument) sql negated
      | .collate argument name => .collate (visit argument) name
      | .case_ base branches other => .case_ (base.map visit)
          (branches.map fun (condition,value) => (visit condition,visit value)) (other.map visit)
      | other => other

def bind (enabled : Bool) (expression : Expr) : Expr :=
  if enabled then bindFuel expression.height expression else expression

theorem bind_disabled (expression : Expr) : bind false expression = expression := rfl

theorem bindFuel_scalarSubquery (fuel : Nat) (sql : String) :
    bindFuel (fuel+1) (.scalarSubquery sql) = .scalarSubquery sql := rfl

end SQLeanite.SQLite.TriggerRaise
