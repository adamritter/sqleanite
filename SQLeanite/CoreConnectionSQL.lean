import SQLeanite.CoreSourceSQL
import SQLeanite.SQLite.TriggerRaise

namespace SQLeanite.CoreConnectionSQL

/-- Connection counters are bound at statement entry, including inside scalar
expressions. Transaction rollback does not roll back these connection counters. -/
def bindExpr (changes total : Nat) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
    let bind := bindExpr changes total fuel
    match expression with
    | .call name args star =>
        if args.isEmpty && !star && name.toLower == "changes" then
          .literal (.integer changes)
        else if args.isEmpty && !star && name.toLower == "total_changes" then
          .literal (.integer total)
        else .call name (args.map bind) star
    | .unary op arg => .unary op (bind arg)
    | .binary op left right => .binary op (bind left) (bind right)
    | .isNull arg negated => .isNull (bind arg) negated
    | .inList arg values negated affinity => .inList (bind arg) (values.map bind) negated affinity
    | .collate arg name => .collate (bind arg) name
    | .case_ base branches other =>
        .case_ (base.map bind) (branches.map fun (a,b) => (bind a,bind b)) (other.map bind)
    | .inSubquery arg sql negated => .inSubquery (bind arg) sql negated
    | other => other

def counterExpression (state : Core.State) (expr : Expr) : Expr :=
  let expr := SQLite.TriggerRaise.bind (state.triggerDepth != 0 || state.raiseContext) expr
  let expression := bindExpr state.lastChanges state.totalChanges expr.height expr
  SQLite.TextEncoding.bind state.catalog.current.textEncoding expression.height expression

def expression (state : Core.State) (expr : Expr) : Expr :=
  CoreLastInsert.bind state (counterExpression state expr)

def columns (state : Core.State) (values : Array ResultColumn) : Array ResultColumn :=
  values.map fun column => { column with expr := expression state column.expr }

def select (state : Core.State) (fuel : Nat) (query : Select) : Select :=
  CoreLastInsert.mapSelect (expression state) fuel query

def statement (state : Core.State) : Statement → Statement
  | .select query => .select (select state query.compoundHeight query)
  | .values rows => .values (rows.map (·.map (expression state)))
  | .insert table cols rows conflict returning =>
      .insert table cols (rows.map (·.map (counterExpression state))) conflict
        (returning.map fun col => { col with expr := counterExpression state col.expr })
  | .insertSelect table cols query conflict returning =>
      .insertSelect table cols (CoreLastInsert.mapSelect (counterExpression state) query.compoundHeight query) conflict
        (returning.map fun col => { col with expr := counterExpression state col.expr })
  | .update table alias assignments condition conflict returning =>
      .update table alias (assignments.map fun (name,value) => (name, expression state value))
        (condition.map (expression state)) conflict (columns state returning)
  | .delete table alias condition returning =>
      .delete table alias (condition.map (expression state)) (columns state returning)
  | other => other

def isDML : Statement → Bool
  | .insert .. | .insertSelect .. | .update .. | .delete .. => true
  | _ => false

def account (before next : Core.State) (sql : Statement) (results : List Core.Result) : Core.State :=
  let rowid := match sql with
    | .insert target .. | .insertSelect target .. =>
        if (CoreNames.table? before.database target).any (fun (table : Core.Table) => table.withoutRowid) then
          before.lastInsertRowid else next.lastInsertRowid
    | _ => before.lastInsertRowid
  let next := { next with lastInsertRowid := rowid }
  if isDML sql then
    let count := (results.map (·.changes)).sum
    { next with lastChanges := count, totalChanges := before.totalChanges + count }
  else { next with lastChanges := before.lastChanges, totalChanges := before.totalChanges }

theorem account_database (before next : Core.State) (sql : Statement) (results : List Core.Result) :
    (account before next sql results).database = next.database := by
  cases sql <;> simp [account] <;> split <;> rfl

theorem account_total (before next : Core.State) (sql : Statement) (results : List Core.Result)
    (dml : isDML sql = true) :
    (account before next sql results).totalChanges = before.totalChanges + (results.map (·.changes)).sum := by
  simp [account, dml]

theorem account_lastInsertRowid (before next : Core.State) (sql : Statement)
    (results : List Core.Result)
    (notInsert : (match sql with | .insert .. | .insertSelect .. => false | _ => true) = true) :
    (account before next sql results).lastInsertRowid = before.lastInsertRowid := by
  cases sql <;> simp_all [account, isDML]

def executeStatement (state : Core.State) (sql : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  if state.catalog.current.textEncoding == 2 || state.catalog.current.textEncoding == 3 then
    if let .select query := sql then
      unless query.compounds.isEmpty do
        let query := select state query.compoundHeight query
        let selected ← CoreSQL.executeSelectEncoded state query
        let results := [selected.result]
        return (account state selected.state sql results,results)
  let (next, results) ← CoreSourceSQL.executeStatement state (statement state sql) source
  return (account state next sql results, results)

end SQLeanite.CoreConnectionSQL
