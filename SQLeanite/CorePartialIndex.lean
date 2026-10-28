import SQLeanite.CoreIndexPrepare
import SQLeanite.CoreIndexExpression
import SQLeanite.CoreIndexKey

/-! Source-certified index programs and actual physical key tuples, shared by
SQL execution and independent file decoding. No SQL executor is imported. -/
namespace SQLeanite.CorePartialIndex

structure Key where
  expression : Expr
  column : Option Nat
  collation : SQLite.Collation.Kind
  collationName : String

structure Prepared where
  source : CoreCatalogData.FilteredIndex
  table : Core.Table
  index : Core.Index
  context : CoreExpr.Context
  key : Expr
  predicate : Expr
  collation : SQLite.Collation.Kind
  collationName : String
  keys : List Key

def prepareKey (context : CoreExpr.Context) (declarations : List CoreCollationSyntax.Spec)
    (annotate : Expr → Expr) (key : Expr) : Except String Key := do
  CoreIndexExpression.validateDeterminism key false
  if key.any (fun node => match node with | .column (some _) _ => true | _ => false) then
    throw "the \".\" operator prohibited in index expressions"
  if key.any (fun node => match node with
      | .scalarSubquery _ | .existsSubquery _ | .inSubquery .. => true | _ => false) then
    throw "subqueries prohibited in index expressions"
  if let some message := SQLite.Scalar.resolutionError
      (fun qualifier name => qualifier.isNone && (context.schema.declaredColumn? name).isSome) key then
    throw message
  if let some message := SQLite.Scalar.functionError key.height key then throw message
  CoreIndexExpression.validateCollations (annotate key)
  if let some message := SQLite.Scalar.aggregateMisuse key then throw message
  context.validate key
  let column ← match CoreCatalogData.indexColumnName? key with
    | some name => some <$> CoreIndexPrepare.indexColumn context.schema name
    | none => pure none
  let collationName := match key with
    | .collate _ name => name
    | _ => (CoreCatalogData.indexColumnName? key |>.bind (fun name =>
        (declarations.find? (fun spec => spec.1.toLower == name.toLower)).map (·.2))).getD "binary"
  let some collation := SQLite.Collation.named? collationName | throw s!"no such collation sequence: {collationName}"
  return { expression := annotate key, column, collation, collationName := collationName.toUpper }

def prepare (database : Core.Database) (source : CoreCatalogData.FilteredIndex) : Except String Prepared := do
  let some table := CoreNames.table? database source.owner | throw s!"no such table: {source.owner}"
  let declarations ← match table.catalogSource with
    | none => pure []
    | some declaration => declaration.compiledCollations
  let annotate := CoreCollationSyntax.annotate (fun qualifier name => do
    if qualifier.any (fun qualifier => qualifier.toLower != table.schema.name.toLower) then none else do
      return (← declarations.find? (fun spec => spec.1.toLower == name.toLower)).2)
  let context : CoreExpr.Context := { schema := table.schema, sourceName := table.schema.name }
  let keys ← source.definition.keys.toList.mapM (prepareKey context declarations annotate)
  let first :: _ := keys | throw "empty index key list"
  let expression := source.definition.predicate
  CoreIndexExpression.validateDeterminism expression true
  if expression.any (fun node => match node with
      | .scalarSubquery _ | .existsSubquery _ | .inSubquery .. => true
      | _ => false) then throw "subqueries prohibited in partial index WHERE clauses"
  if let some message := SQLite.Scalar.resolutionError
      (fun qualifier name => (context.column? qualifier name).isSome) expression then throw message
  if let some message := SQLite.Scalar.functionError expression.height expression then throw message
  CoreIndexExpression.validateCollations (annotate expression)
  context.validate expression
  return {
    source, table, index := { name := source.definition.name, column := first.column.getD 0, unique := source.definition.unique }
    context, key := first.expression, predicate := annotate expression
    collation := first.collation, collationName := first.collationName, keys }

/-- Ordinary column catalogs retain their existing independent admission. -/
def required (prepared : Prepared) : Bool :=
  CoreCatalogData.auxiliaryIndex prepared.source.definition.keys
    (if prepared.source.definition.partialIndex then some prepared.source.definition.predicate else none) ||
      prepared.keys.any (fun key => key.collation != .binary)

def selectRows (context : CoreExpr.Context) (predicate : Expr) :
    List Core.Row → Except String (List Core.Row)
  | [] => .ok []
  | row :: rest => do
      let selected ← CoreIndexExpression.acceptsPredicate context row.values predicate
      let tail ← selectRows context predicate rest
      return if selected then row :: tail else tail

def rows (prepared : Prepared) : Except String (List Core.Row) :=
  selectRows prepared.context prepared.predicate prepared.table.rows

/-- Retained single-key component API. Tuple uniqueness below uses all keys. -/
def adjacentUnique (index : Core.Index) : List Core.Row → Bool
  | left :: right :: tail => !index.rowConflict left right && adjacentUnique index (right :: tail)
  | _ => true

theorem adjacentUnique_single (index : Core.Index) (row : Core.Row) :
    adjacentUnique index [row] = true := rfl

def keyValue (prepared : Prepared) (values : List Core.Value) : Except String Core.Value := do
  SQLSurface.value (← CoreIndexExpression.eval prepared.context values prepared.key)

def keyRow (prepared : Prepared) (row : Core.Row) : Except String Core.Row := do
  let key ← keyValue prepared row.values
  return { row with values := row.values.set prepared.index.column key }

@[simp] theorem keyRow_rowid (prepared : Prepared) (row projected : Core.Row)
    (success : keyRow prepared row = .ok projected) : projected.rowid = row.rowid := by
  unfold keyRow at success
  cases evaluated : keyValue prepared row.values with
  | error message => simp [evaluated, bind, Except.bind] at success
  | ok key => simp [evaluated, bind, Except.bind, pure, Except.pure] at success; cases success; rfl

def keyValues (prepared : Prepared) (values : List Core.Value) : Except String (List Core.Value) :=
  prepared.keys.mapM (fun key => do SQLSurface.value (← CoreIndexExpression.eval prepared.context values key.expression))

def keyEntry (prepared : Prepared) (row : Core.Row) : Except String CoreIndexKey.Entry := do
  return { values := ← keyValues prepared row.values, rowid := row.rowid }

@[simp] theorem keyEntry_rowid (prepared : Prepared) (row : Core.Row) (entry : CoreIndexKey.Entry)
    (success : keyEntry prepared row = .ok entry) : entry.rowid = row.rowid := by
  unfold keyEntry at success
  cases evaluated : keyValues prepared row.values with
  | error message => simp [evaluated, bind, Except.bind] at success
  | ok values => simp [evaluated, bind, Except.bind, pure, Except.pure] at success; cases success; rfl

def Prepared.collations (prepared : Prepared) : List SQLite.Collation.Kind := prepared.keys.map (·.collation)

def orderedKeyRows (prepared : Prepared) : Except String (List (Core.Row × CoreIndexKey.Entry)) := do
  let selected ← rows prepared
  let keyed ← selected.mapM (fun row => do return (row,← keyEntry prepared row))
  return keyed.mergeSort (fun left right => CoreIndexKey.entryLe prepared.collations left.2 right.2)

def uniqueError (prepared : Prepared) : String :=
  if prepared.keys.all (fun key => key.column.isSome) then
    let names := prepared.keys.map fun key =>
      let name := ((key.column.bind (prepared.table.schema.catalogColumns[·]?)).map (·.name)).getD ""
      s!"{prepared.table.schema.name}.{name}"
    "UNIQUE constraint failed: " ++ String.intercalate ", " names
  else s!"UNIQUE constraint failed: index '{prepared.source.definition.name}'"

def orderedKeys (prepared : Prepared) : Except String (List CoreIndexKey.Entry) := do
  return (← orderedKeyRows prepared).map (·.2)

def ensureUnique (prepared : Prepared) (ordered : List CoreIndexKey.Entry) : Except String Unit := do
  unless CoreIndexKey.adjacentUnique prepared.index.unique prepared.collations ordered do
    throw (uniqueError prepared)

def sortedKeys (prepared : Prepared) : Except String (List CoreIndexKey.Entry) := do
  let ordered ← orderedKeys prepared
  ensureUnique prepared ordered
  return ordered

/-- The retained component interface projects only the first physical key;
its ordering and uniqueness still consume the complete actual key tuples. -/
def projectedRow (prepared : Prepared) (entry : Core.Row × CoreIndexKey.Entry) : Core.Row :=
  { entry.1 with values := entry.1.values.set prepared.index.column (entry.2.values.headD .null) }

def orderedRows (prepared : Prepared) : Except String (List Core.Row) := do
  return (← orderedKeyRows prepared).map (projectedRow prepared)

def sortedRows (prepared : Prepared) : Except String (List Core.Row) := do
  let ordered ← orderedKeyRows prepared
  ensureUnique prepared (ordered.map (·.2))
  return ordered.map (projectedRow prepared)

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
