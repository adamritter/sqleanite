import SQLeanite.CoreSourceSQL

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

def expression (state : Core.State) (expr : Expr) : Expr :=
  bindExpr state.lastChanges state.totalChanges expr.height expr

def columns (state : Core.State) (values : Array ResultColumn) : Array ResultColumn :=
  values.map fun column => { column with expr := expression state column.expr }

def select (state : Core.State) : Nat → Select → Select
  | 0, query => query
  | fuel + 1, query => { query with
      columns := columns state query.columns
      valueRows := query.valueRows.map (·.map (·.map (expression state)))
      sources := query.sources.map fun source => { source with joinOn := source.joinOn.map (expression state) }
      where_ := query.where_.map (expression state)
      groupBy := query.groupBy.map (expression state)
      having := query.having.map (expression state)
      orderBy := query.orderBy.map fun term => { term with expr := expression state term.expr }
      compounds := query.compounds.map fun (op,arm) => (op, select state fuel arm) }

def statement (state : Core.State) : Statement → Statement
  | .select query => .select (select state query.compoundHeight query)
  | .values rows => .values (rows.map (·.map (expression state)))
  | .insert table cols rows conflict returning =>
      .insert table cols (rows.map (·.map (expression state))) conflict (columns state returning)
  | .insertSelect table cols query conflict returning =>
      .insertSelect table cols (select state query.compoundHeight query) conflict (columns state returning)
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
  if isDML sql then
    let count := (results.map (·.changes)).sum
    { next with lastChanges := count, totalChanges := before.totalChanges + count }
  else { next with lastChanges := before.lastChanges, totalChanges := before.totalChanges }

theorem account_database (before next : Core.State) (sql : Statement) (results : List Core.Result) :
    (account before next sql results).database = next.database := by
  simp [account]; split <;> rfl

theorem account_total (before next : Core.State) (sql : Statement) (results : List Core.Result)
    (dml : isDML sql = true) :
    (account before next sql results).totalChanges = before.totalChanges + (results.map (·.changes)).sum := by
  simp [account, dml]

def executeStatement (state : Core.State) (sql : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  let (next, results) ← CoreSourceSQL.executeStatement state (statement state sql) source
  return (account state next sql results, results)

end SQLeanite.CoreConnectionSQL
