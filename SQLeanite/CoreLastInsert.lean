import SQLeanite.CoreReturning

namespace SQLeanite.CoreLastInsert

/-- Read the connection register at the point where an expression is evaluated. -/
def bindFuel (rowid : Int) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
    let bind := bindFuel rowid fuel
    match expression with
    | .call name args star =>
        if args.isEmpty && !star && name.toLower == "last_insert_rowid" then
          .literal (.integer rowid)
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

def bind (state : Core.State) (expression : Expr) : Expr :=
  bindFuel state.lastInsertRowid expression.height expression

def uses (expression : Expr) : Bool := expression.any fun node => match node with
  | .call name _ _ => name.toLower == "last_insert_rowid"
  | _ => false

def mapSelect (visit : Expr → Expr) : Nat → Select → Select
  | 0, query => query
  | fuel + 1, query => { query with
      columns := query.columns.map fun col => { col with expr := visit col.expr }
      valueRows := query.valueRows.map (·.map (·.map visit))
      sources := query.sources.map fun source => { source with joinOn := source.joinOn.map visit }
      where_ := query.where_.map visit
      groupBy := query.groupBy.map visit
      having := query.having.map visit
      orderBy := query.orderBy.map fun term => { term with expr := visit term.expr }
      compounds := query.compounds.map fun (op,arm) => (op, mapSelect visit fuel arm) }

def select (state : Core.State) (query : Select) : Select :=
  mapSelect (bind state) query.compoundHeight query

def queryUses : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, query =>
      query.columns.any (fun col => uses col.expr) || query.where_.any uses ||
      query.groupBy.any uses || query.having.any uses ||
      query.orderBy.any (fun term => uses term.expr) ||
      query.valueRows.any (fun rows => rows.any (fun row => row.any uses)) ||
      query.sources.any (fun source => source.joinOn.any uses) ||
      query.compounds.any (fun arm => queryUses fuel arm.2)

def expandProjection (ctx : CoreExpr.Context) (columns : List ResultColumn) : List Expr :=
  columns.flatMap fun column => match column.expr with
    | .star _ => ctx.schema.catalogColumns.map (fun c => .column none c.name)
    | expression => [expression]

def prepareProjection (state : Core.State) (ctx : CoreExpr.Context)
    (columns : List ResultColumn) : Except String (List Expr) := do
  let _ ← ctx.projection (columns.map fun column => { column with expr := bind state column.expr })
  return expandProjection ctx columns

/-- Validate RETURNING before any writes, but retain register reads until the
accepted row has been inserted. Star expansion uses the same catalog columns. -/
def prepareReturning (state : Core.State) (ctx : CoreExpr.Context)
    (columns : List ResultColumn) : Except String (List Expr) := do
  let _ ← CoreReturning.prepare ctx (columns.map fun column =>
    { column with expr := bind state column.expr })
  return expandProjection ctx columns

theorem bind_call (state : Core.State) (name : String)
    (spelling : name.toLower = "last_insert_rowid") :
    bind state (.call name #[] false) =
      .literal (.integer state.lastInsertRowid) := by
  simp [bind, bindFuel, Expr.height, spelling]

end SQLeanite.CoreLastInsert
