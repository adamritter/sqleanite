import SQLeanite.CoreIndexPrepare
import SQLeanite.CoreExpr
import SQLeanite.CoreIndexExpression
import SQLeanite.CoreFile.TableInteriorPage

/-! Partial-index predicates and real physical key rows, shared by SQL and
independent file decoding. No SQL statement executor is imported here. -/
namespace SQLeanite.CorePartialIndex

structure Prepared where
  source : CoreCatalogData.FilteredIndex
  table : Core.Table
  index : Core.Index
  context : CoreExpr.Context

def prepare (database : Core.Database) (source : CoreCatalogData.FilteredIndex) : Except String Prepared := do
  let some table := CoreNames.table? database source.owner | throw s!"no such table: {source.owner}"
  let column ← match source.definition.column with
    | some name => CoreIndexPrepare.indexColumn table.schema name
    | none => pure 0
  if let some declaration := table.catalogSource then
    unless (← declaration.compiledCollations).isEmpty do throw "unsupported declared collation partial index"
  let context : CoreExpr.Context := { schema := table.schema, sourceName := table.schema.name }
  let key := source.definition.key
  CoreIndexExpression.validateDeterminism key false
  if key.any (fun node => match node with | .column (some _) _ => true | _ => false) then
    throw "the \".\" operator prohibited in index expressions"
  if key.any (fun node => match node with
      | .scalarSubquery _ | .existsSubquery _ | .inSubquery .. => true | _ => false) then
    throw "subqueries prohibited in index expressions"
  if let some message := SQLite.Scalar.resolutionError
      (fun qualifier name => qualifier.isNone && (table.schema.declaredColumn? name).isSome) key then
    throw message
  if let some message := SQLite.Scalar.functionError key.height key then throw message
  if key.any (fun node => match node with
      | .collate _ collation => collation.toLower != "binary" | _ => false) then
    throw "unsupported index expression collation"
  if let some message := SQLite.Scalar.aggregateMisuse key then throw message
  context.validate key
  let expression := source.definition.predicate
  CoreIndexExpression.validateDeterminism expression true
  if expression.any (fun node => match node with
      | .scalarSubquery _ | .existsSubquery _ | .inSubquery .. => true
      | _ => false) then throw "subqueries prohibited in partial index WHERE clauses"
  if let some message := SQLite.Scalar.resolutionError
      (fun qualifier name => (context.column? qualifier name).isSome) expression then throw message
  if let some message := SQLite.Scalar.functionError expression.height expression then throw message
  context.validate expression
  return { source, table, index := { name := source.definition.name, column, unique := source.definition.unique }, context }

def selectRows (context : CoreExpr.Context) (predicate : Expr) :
    List Core.Row → Except String (List Core.Row)
  | [] => .ok []
  | row :: rest => do
      let selected ← CoreIndexExpression.acceptsPredicate context row.values predicate
      let tail ← selectRows context predicate rest
      return if selected then row :: tail else tail

def rows (prepared : Prepared) : Except String (List Core.Row) :=
  selectRows prepared.context prepared.source.definition.predicate prepared.table.rows

def adjacentUnique (index : Core.Index) : List Core.Row → Bool
  | left :: right :: tail => !index.rowConflict left right && adjacentUnique index (right :: tail)
  | _ => true

theorem adjacentUnique_single (index : Core.Index) (row : Core.Row) :
    adjacentUnique index [row] = true := rfl

def keyValue (prepared : Prepared) (values : List Core.Value) : Except String Core.Value := do
  SQLSurface.value (← CoreIndexExpression.eval prepared.context values prepared.source.definition.key)

def keyRow (prepared : Prepared) (row : Core.Row) : Except String Core.Row := do
  let key ← keyValue prepared row.values
  return { row with values := row.values.set prepared.index.column key }

@[simp] theorem keyRow_rowid (prepared : Prepared) (row projected : Core.Row)
    (success : keyRow prepared row = .ok projected) : projected.rowid = row.rowid := by
  unfold keyRow at success
  cases evaluated : keyValue prepared row.values with
  | error message => simp [evaluated, bind, Except.bind] at success
  | ok key => simp [evaluated, bind, Except.bind, pure, Except.pure] at success; cases success; rfl

/-- The same existing BINARY key comparator orders real qualifying keys.
The full-column Core index itself remains unchanged. -/
def orderedRows (prepared : Prepared) : Except String (List Core.Row) := do
  let selected ← rows prepared
  let projected ← selected.mapM (keyRow prepared)
  return projected.mergeSort (fun left right => !CoreFile.indexRowLess prepared.index right left)

def sortedRows (prepared : Prepared) : Except String (List Core.Row) := do
  let ordered ← orderedRows prepared
  unless adjacentUnique prepared.index ordered do
    if let some name := prepared.source.definition.column then
      let name := (prepared.table.schema.catalogColumns[prepared.index.column]?.map (·.name)).getD name
      throw s!"UNIQUE constraint failed: {prepared.table.schema.name}.{name}"
    else throw s!"UNIQUE constraint failed: index '{prepared.source.definition.name}'"
  return ordered

theorem selectRows_member (context : CoreExpr.Context) (predicate : Expr)
    (inputs selected : List Core.Row) (success : selectRows context predicate inputs = .ok selected)
    (row : Core.Row) (member : row ∈ selected) : row ∈ inputs := by
  induction inputs generalizing selected with
  | nil => simp [selectRows] at success; cases success; simp at member
  | cons head tail ih =>
      cases matched : CoreIndexExpression.acceptsPredicate context head.values predicate with
      | error message => simp [selectRows, matched, bind, Except.bind] at success
      | ok allowed =>
          cases result : selectRows context predicate tail with
          | error message => simp [selectRows, matched, result, bind, Except.bind] at success
          | ok more =>
              cases allowed <;> simp [selectRows, matched, result, bind, Except.bind, pure, Except.pure] at success
              · cases success
                exact List.mem_cons.mpr (.inr (ih _ result member))
              · cases success
                rcases List.mem_cons.mp member with same | remaining
                · exact List.mem_cons.mpr (.inl same)
                · exact List.mem_cons.mpr (.inr (ih _ result remaining))


theorem selectRows_satisfy (context : CoreExpr.Context) (predicate : Expr)
    (inputs selected : List Core.Row) (success : selectRows context predicate inputs = .ok selected)
    (row : Core.Row) (member : row ∈ selected) : CoreIndexExpression.acceptsPredicate context row.values predicate = .ok true := by
  induction inputs generalizing selected with
  | nil => simp [selectRows] at success; cases success; simp at member
  | cons head tail ih =>
      cases matched : CoreIndexExpression.acceptsPredicate context head.values predicate with
      | error message => simp [selectRows, matched, bind, Except.bind] at success
      | ok allowed =>
          cases result : selectRows context predicate tail with
          | error message => simp [selectRows, matched, result, bind, Except.bind] at success
          | ok more =>
              cases allowed <;> simp [selectRows, matched, result, bind, Except.bind, pure, Except.pure] at success
              · cases success; exact ih _ result member
              · cases success
                rcases List.mem_cons.mp member with same | remaining
                · subst row; exact matched
                · exact ih _ result remaining

end SQLeanite.CorePartialIndex
