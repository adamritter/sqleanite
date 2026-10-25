import SQLeanite.CoreAggregate

/-! RETURNING expressions use the modified table's original name, not its
DELETE alias. Output is materialized before a successful statement is exposed.
Callers support scalar INSERT and DELETE RETURNING on admitted Core tables. -/
namespace SQLeanite.CoreReturning

/-- Function binding in trigger.c's RETURNING expansion precedes zero-AND
simplification. Column binding still follows the ordinary expression rules. -/
def prepare (ctx : CoreExpr.Context) (columns : List ResultColumn) : Except String (List Expr) := do
  for column in columns do
    if column.expr.any (fun expression => match expression with
        | .star (some _) => true | _ => false) then
      throw "RETURNING may not use TABLE.* wildcards"
    if CoreAggregate.containsAggregate column.expr then
      throw "misuse of aggregate function in RETURNING"
    if (ctx.bindNames column.expr).any (fun expression => match expression with
        | .call .. => SQLite.Scalar.forbidden expression | _ => false) then
      throw "unsupported function or invalid function arguments in RETURNING"
  let expressions ← ctx.projection columns
  unless expressions.length ≤ SQLite.Limits.maxColumns do throw "too many columns in RETURNING"
  return expressions

/-- Only exact rowid deletions produced by the DELETE planner can supply an
old row. Missing rows and other command shapes are errors, never omissions. -/
def deletedRow? (stored : Core.Table) : Core.Command → Option Core.Row
  | .deleteWhere table (some (.equal column (.integer rowid))) =>
      if table == stored.schema.name && column == stored.schema.primaryKey then stored.findRowid? rowid
      else none
  | _ => none

def deletionOutput (stored : Core.Table) (ctx : CoreExpr.Context) (expressions : List Expr) :
    List Core.Command → Except String (List (List Core.Value))
  | [] => .ok []
  | command :: commands => do
      let some row := deletedRow? stored command | throw "RETURNING deletion row is missing"
      let output ← ctx.projectRow row.values expressions
      let outputs ← deletionOutput stored ctx expressions commands
      return output :: outputs

/-- Successful materialization emits exactly one output per planned deletion. -/
theorem deletionOutput_length (stored : Core.Table) (ctx : CoreExpr.Context) (expressions : List Expr)
    (commands : List Core.Command) (outputs : List (List Core.Value))
    (success : deletionOutput stored ctx expressions commands = .ok outputs) :
    outputs.length = commands.length := by
  induction commands generalizing outputs with
  | nil => simpa [deletionOutput] using success
  | cons command commands ih =>
      cases found : deletedRow? stored command with
      | none => simp [deletionOutput, found] at success
      | some row =>
          cases projected : ctx.projectRow row.values expressions with
          | error message => simp [deletionOutput, found, projected, bind, Except.bind] at success
          | ok output =>
              cases rest : deletionOutput stored ctx expressions commands with
              | error message => simp [deletionOutput, found, projected, rest, bind, Except.bind] at success
              | ok tail =>
                  simp [deletionOutput, found, projected, rest, bind, Except.bind, pure, Except.pure] at success
                  subst outputs
                  simpa using ih tail rest

end SQLeanite.CoreReturning
