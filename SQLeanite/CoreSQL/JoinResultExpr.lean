import SQLeanite.CoreSQL.SchemaReplacementRows

namespace SQLeanite
namespace CoreSQL

def joinResultExpr (context : JoinContext) : Expr → Except String (List CoreJoin.Operand)
  | .column qualifier name => return [← joinNamedOperand context qualifier name]
  | .star none =>
      .ok ((joinVisibleColumns .left context.leftSchema ++
        (joinVisibleColumns .right context.rightSchema).filter
          (fun reference => !CoreJoinUsing.suppressesRight context.shared reference.column)).map
            (joinStarOperand context))
  | .star (some qualifier) =>
      let owner := canonical qualifier
      if owner == context.leftName then
        .ok ((joinVisibleColumns .left context.leftSchema).map
          (joinStarOperand context))
      else if owner == context.rightName then
        .ok ((joinVisibleColumns .right context.rightSchema).map CoreJoin.Operand.column)
      else .error s!"no such table or alias: {qualifier}"
  | expression => do
      unless joinLiteralExpression expression do unsupported "join projection"
      return [.literal (← literal expression)]

def joinResultColumn (context : JoinContext) (column : ResultColumn) :
    Except String (List CoreJoin.Operand) :=
  joinResultExpr context (joinBindNames context column.expr)

def joinProjection (context : JoinContext) : List ResultColumn →
    Except String (List CoreJoin.Operand)
  | [] => .ok []
  | result :: results =>
      return (← joinResultColumn context result) ++ (← joinProjection context results)

/-- Only explicit aliases and expanded stars provide ORDER BY result names.
A plain selected source column retains ordinary ambiguity checks. -/
def joinOrderName (context : JoinContext) (column : ResultColumn)
    (operand : CoreJoin.Operand) : Option String :=
  match column.expr, operand with
  | .star _, .column reference =>
      let schema := if reference.side == .left then context.leftSchema else context.rightSchema
      (schema.columns[reference.column]?).map (·.name)
  | .star _, .mergedColumn _ left _ => (context.leftSchema.columns[left]?).map (·.name)
  | .star _, _ => none
  | _, _ => column.alias

def joinOrderColumns (context : JoinContext) : List ResultColumn →
    Except String (List (CoreJoin.Operand × Option String))
  | [] => .ok []
  | column :: columns => do
      let references ← joinResultColumn context column
      return references.map (fun reference => (reference, joinOrderName context column reference)) ++
        (← joinOrderColumns context columns)

theorem joinOrderColumns_projection (context : JoinContext) (columns : List ResultColumn) :
    (joinOrderColumns context columns).map (List.map Prod.fst) = joinProjection context columns := by
  induction columns with
  | nil => rfl
  | cons column columns ih =>
      cases head : joinResultColumn context column with
      | error message => simp [joinOrderColumns, joinProjection, head, bind, Except.bind, Except.map]
      | ok references =>
          cases tail : joinOrderColumns context columns with
          | error message =>
              simp [tail, Except.map] at ih
              simp [joinOrderColumns, joinProjection, head, tail, ← ih, bind, Except.bind, Except.map]
          | ok named =>
              simp [tail, Except.map] at ih
              simp [joinOrderColumns, joinProjection, head, tail, ← ih, bind, Except.bind,
                pure, Except.pure, Except.map, List.map_append, List.map_map, Function.comp_def]

/-- Unary operations on literals stay constant and cannot fail during sorting.
Integer ordinal recognition runs before this test. -/
def joinOrderConstant : Expr → Bool
  | .literal .. => true
  | .unary _ expression => joinOrderConstant expression
  | _ => false

def joinOrderOutputReference : CoreJoin.Operand → Except String (Option CoreJoin.ColumnRef)
  | .column reference => .ok (some reference)
  | .literal _ => .ok none
  | .coercedColumn .. | .mergedColumn .. => unsupported "computed join output ordering"

def joinOrderReference (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (expression : Expr) :
    Except String (Option CoreJoin.ColumnRef) := do
  let expression := SQLite.Scalar.prepare (CoreOrder.keyExpression expression)
  if let some name := CoreOrder.bareName? expression then
    if let some output := columns.find? (fun output => output.2.any (fun alias => canonical alias == canonical name)) then
      return ← joinOrderOutputReference output.1
  if let some position := CoreOrder.ordinal? expression then
    unless 1 ≤ position && position.toNat ≤ columns.length do
      throw "ORDER BY position is outside the result columns"
    let some output := columns[position.toNat - 1]? | throw "ORDER BY position is out of range"
    return ← joinOrderOutputReference output.1
  if joinOrderConstant expression then return none
  if let some name := SQLite.Scalar.quotedIdentifier? expression then
    return some (← joinColumn context none name)
  if let some truth := SQLite.Scalar.booleanKeyword? expression then
    let name := SQLite.Scalar.booleanName truth
    if (findColumn? context.leftSchema name).isSome || (findColumn? context.rightSchema name).isSome then
      return some (← joinColumn context none name)
    return none
  match expression with
  | .column qualifier name => return some (← joinColumn context qualifier name)
  | _ => unsupported "join ORDER BY expression"

def joinOrderBy (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) : List OrderTerm →
    Except String (List CoreJoin.OrderTerm)
  | [] => .ok []
  | term :: terms => do
      let specification ← CoreOrder.specification term
      let reference ← joinOrderReference context columns term.expr
      let rest ← joinOrderBy context columns terms
      match reference with
      | none => return rest
      | some reference =>
          return {
            reference
            descending := specification.descending
            nullsFirst := some specification.nullsFirst
            collation := specification.collation } :: rest

/-- A rowid equality conjunct makes each surviving pair unique on either
side. It can satisfy later ORDER terms without an inner table sort. -/
def joinHasRowidEquality (left right : Core.Schema) : CoreJoin.Predicate → Bool
  | .and first second => joinHasRowidEquality left right first ||
      joinHasRowidEquality left right second
  | predicate => decide (predicate = CoreJoin.rowidOn left.primaryKey right.primaryKey ∨
      predicate = .equal (.column ⟨.right, right.primaryKey⟩) (.column ⟨.left, left.primaryKey⟩))

/-- A leading rowid ORDER term can determine table traversal. INNER joins
may exchange their sources; CROSS and LEFT joins retain the left outer loop.
Terms of the outer row are constant within an inner scan. A leading inner
rowid term can reverse that scan; other terms use a subsequent block sorter. -/
def joinDistinctScanOrder (left right : Core.Schema) (mayExchange oneToOne : Bool)
    (terms : List (CoreJoin.ColumnRef × Bool)) : List (CoreJoin.ColumnRef × Bool) :=
  match terms with
  | (reference, descending) :: rest =>
      let outerSchema := if reference.side == .left then left else right
      let innerSchema := if reference.side == .left then right else left
      let innerSide := if reference.side == .left then CoreJoin.Side.right else .left
      let inner := rest.find? (fun term => term.1.side == innerSide)
      let fullyOrdered := oneToOne || inner.all (fun term => term.1.column == innerSchema.primaryKey)
      if reference.column == outerSchema.primaryKey &&
          (reference.side == .left || (mayExchange && fullyOrdered)) then
        let innerDescending := inner.any fun term =>
          term.1.column == innerSchema.primaryKey && term.2
        [(reference, descending), (⟨innerSide, innerSchema.primaryKey⟩, innerDescending)]
      else []
  | [] => []

/-- A rowid equality can make the left table the point-lookup inner side.
Coercion of the right operand does not change which source drives that scan. -/
def joinProbesLeftRowid (left : Core.Schema) : CoreJoin.Predicate → Bool
  | .and first second => joinProbesLeftRowid left first || joinProbesLeftRowid left second
  | .equal (.column ⟨.left, index⟩) (.column ⟨.right, _⟩)
  | .equal (.column ⟨.left, index⟩) (.coercedColumn _ ⟨.right, _⟩)
  | .equal (.column ⟨.right, _⟩) (.column ⟨.left, index⟩)
  | .equal (.coercedColumn _ ⟨.right, _⟩) (.column ⟨.left, index⟩) => index == left.primaryKey
  | _ => false

def joinLookupScanOrder (left right : Core.Schema) (mayExchange : Bool)
    (on where_ : Option CoreJoin.Predicate) (terms : List CoreJoin.OrderTerm) :
    List (CoreJoin.ColumnRef × Bool) :=
  if mayExchange &&
      !(on.any (joinHasRowidEquality left right) || where_.any (joinHasRowidEquality left right)) &&
      (on.any (joinProbesLeftRowid left) || where_.any (joinProbesLeftRowid left)) then
    let descending := terms.head?.any fun term =>
      term.reference.side == .right && term.reference.column == right.primaryKey && term.descending
    [(⟨.right, right.primaryKey⟩, descending), (⟨.left, left.primaryKey⟩, false)]
  else []

/-- SQL compound operations use numeric comparison keys; output rows retain
SQLite's selected original storage classes. -/
def combineRows (operation : CompoundOp) (left right : List (List Core.Value)) :
    List (List Core.Value) := CoreCompound.combine operation left right

/-- Membership is stated over SQL keys, not raw representations: INTEGER 1
and REAL 1.0 name the same set member. -/
theorem mem_combineRows (operation : CompoundOp) (left right : List (List Core.Value))
    (key : List Core.Value) :
    key ∈ (combineRows operation left right).map Core.distinctRowKey ↔
      match operation with
      | .unionAll | .unionDistinct => key ∈ left.map Core.distinctRowKey ∨ key ∈ right.map Core.distinctRowKey
      | .intersect => key ∈ left.map Core.distinctRowKey ∧ key ∈ right.map Core.distinctRowKey
      | .except => key ∈ left.map Core.distinctRowKey ∧ key ∉ right.map Core.distinctRowKey :=
  CoreCompound.combine_keys operation left right key

theorem combineRows_nodup (operation : CompoundOp)
    (notAll : operation ≠ .unionAll) (left right : List (List Core.Value)) :
    (combineRows operation left right).Nodup :=
  List.Pairwise.of_map Core.distinctRowKey (fun _ _ h equal => h (congrArg _ equal))
    (CoreCompound.combine_keys_nodup operation left right notAll)

def RowsHaveWidth (width : Nat) (rows : List (List Core.Value)) : Prop :=
  ∀ row ∈ rows, row.length = width

theorem combineRows_width (operation : CompoundOp) (width : Nat)
    {left right : List (List Core.Value)}
    (leftWidth : RowsHaveWidth width left)
    (rightWidth : RowsHaveWidth width right) :
    RowsHaveWidth width (combineRows operation left right) := by
  intro row member
  rcases List.mem_append.mp (CoreCompound.combine_subset operation left right member) with member | member
  · exact leftWidth row member
  · exact rightWidth row member

theorem combineRows_denotes (operation : CompoundOp) (left right : List (List Core.Value)) :
    RelationalAlgebra.ofList ((combineRows operation left right).map Core.distinctRowKey) =
      CoreCompound.denotation operation
        (RelationalAlgebra.ofList (left.map Core.distinctRowKey))
        (RelationalAlgebra.ofList (right.map Core.distinctRowKey)) :=
  CoreCompound.combine_denotes operation left right

structure SelectExecution where
  state : Core.State
  result : Core.Result
  width : Nat

def joinContext (leftSource rightSource : TableRef) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String JoinContext := do
  return {
    leftTable, rightTable
    leftName := canonical (leftSource.alias.getD leftSource.name)
    rightName := canonical (rightSource.alias.getD rightSource.name)
    leftSchema, rightSchema
    shared := ← CoreJoinUsing.columns leftSchema rightSchema rightSource
    preferRightShared := rightSource.rightJoin && !rightSource.leftJoin
    coalesceShared := rightSource.rightJoin && rightSource.leftJoin }

/-- BETWEEN remains one predicate during fixed-column preparation. Its
virtual range bounds are exposed only to cursor-constraint selection. -/
def joinSearchRangeTerms (terms : List Expr) : List Expr :=
  terms.flatMap fun term => match SQLite.ExprCollation.strip term with
    | .call "__sqlean_between" arguments false =>
        match arguments.toList with
        | [argument, lower, upper] => [.binary .ge argument lower, .binary .le argument upper]
        | _ => [term]
    | _ => [term]

theorem joinSearchRangeTerms_between (argument lower upper : Expr) :
    joinSearchRangeTerms [.call "__sqlean_between" #[argument, lower, upper] false] =
      [.binary .ge argument lower, .binary .le argument upper] := rfl

/-- Computed cursor keys cannot be erased by an empty-pair adapter. A bare
column is required on the inner side; unary plus disqualifies it as in SQLite. -/
def joinComputedCursorKey (context : JoinContext) (expression : Expr) : Bool :=
  let expression := SQLite.Scalar.prepare (joinBindNames context expression)
  let target := fun expression => match SQLite.ExprCollation.strip expression with
    | .column qualifier name => (joinColumn context qualifier name).toOption.any (fun ref => ref.side == .right)
    | _ => false
  let value := fun expression => !(joinOperand context expression).isOk &&
    !expression.any (fun node => match node with
      | .column qualifier name => !(joinColumn context qualifier name).toOption.any (fun ref => ref.side == .left)
      | _ => false)
  (joinSearchRangeTerms (SQLite.Scalar.conditionTerms expression)).any fun term => match SQLite.ExprCollation.strip term with
    | .binary operation left right =>
        [.eq, .is, .lt, .le, .gt, .ge].contains operation &&
          ((target left && value right) || (target right && value left))
    | .inList column values false _ => target column && values.any value
    | _ => false

/-- Constant rowid membership can drive the first source loop. The general
cursor path owns its ordering rather than a left-major Cartesian product. -/
def joinConstantRowidMembership (context : JoinContext) (expression : Expr) : Bool :=
  (SQLite.Scalar.conditionTerms (SQLite.Scalar.prepare (joinBindNames context expression))).any fun term =>
    match SQLite.ExprCollation.strip term with
    | .inList column values false _ =>
        match SQLite.ExprCollation.strip column with
        | .column qualifier name =>
            (joinColumn context qualifier name).toOption.any (fun ref =>
              ref.column == (if ref.side == .left then context.leftSchema else context.rightSchema).primaryKey) &&
              values.all SQLite.Scalar.constantExpression
        | _ => false
    | _ => false

/-- Index affinity is determined by the declared columns, independently of
the stored row values. USING can use only the compatible side's transient
index when numeric comparison rules exclude the other side. -/
def joinUsingIndexEligible (context : JoinContext) (side : CoreJoin.Side) : Bool :=
  context.shared.any fun shared =>
    let column := if side == .left then shared.left else shared.right
    let schema := if side == .left then context.leftSchema else context.rightSchema
    column != schema.primaryKey &&
      (match context.leftSchema.columns[shared.left]?, context.rightSchema.columns[shared.right]? with
        | some left, some right =>
            let indexed := if side == .left then left.affinity else right.affinity
            let comparison := SQLite.Scalar.comparisonAffinity (some left.affinity) (some right.affinity)
            comparison == .blob || (comparison == .text && indexed == .text) ||
              (SQLite.Scalar.numericAffinity comparison && SQLite.Scalar.numericAffinity indexed)
        | _, _ => false)

theorem joinUsingIndexEligible_without_shared (context : JoinContext) (side : CoreJoin.Side)
    (empty : context.shared = []) : joinUsingIndexEligible context side = false := by
  simp [joinUsingIndexEligible, empty]

/-- Translate the supported two-source SQL shape independently of a materialized
database.  Both the ordinary engine and cold page-directed execution use this
single interpretation, preventing the fast path from acquiring subtly
different alias, projection, or predicate semantics. -/
def joinQueryBound (select : Select) (rightSource : TableRef) (context : JoinContext) :
    Except String CoreJoin.Query := do
  if context.leftName == context.rightName then
    throw "join sources require distinct names or aliases"
  if (rightSource.leftJoin || rightSource.rightJoin) && rightSource.joinOn.any (joinComputedCursorKey context) then
    return ← unsupported "outer condition requires executable cursor planning"
  if !rightSource.leftJoin && !rightSource.rightJoin && !rightSource.crossJoin &&
      rightSource.joinOn.any (joinConstantRowidMembership context) then
    return ← unsupported "constant rowid membership requires cursor planning"
  if !rightSource.leftJoin && !rightSource.rightJoin && !rightSource.crossJoin &&
      !context.shared.any (fun column => column.right == context.rightSchema.primaryKey) &&
      joinUsingIndexEligible context .left && !joinUsingIndexEligible context .right then
    return ← unsupported "USING affinity requires executable cursor planning"
  let explicitOn ← rightSource.joinOn.mapM (fun expression => joinPredicate context expression (rightSource.leftJoin || rightSource.rightJoin))
  let sharedOn ← joinUsingPredicate context
  let on := match explicitOn, sharedOn with
    | none, predicate | predicate, none => predicate
    | some left, some right => some (CoreJoin.Predicate.and left right)
  let where_ ← select.where_.mapM (joinPredicate context)
  let orderColumns ← joinOrderColumns context select.columns.toList
  let orderBy ← joinOrderBy context orderColumns select.orderBy.toList
  let mayExchange := !rightSource.leftJoin && !rightSource.rightJoin && !rightSource.crossJoin
  let lookupScanOrder := joinLookupScanOrder context.leftSchema context.rightSchema mayExchange on where_ orderBy
  return {
    columns := ← joinProjection context select.columns.toList
    on
    kind := if rightSource.leftJoin || rightSource.rightJoin then .left else .inner
    rightWidth := context.rightSchema.columns.length
    where_
    orderBy
    limit := select.limit
    offset := select.offset
    distinct := select.distinct
    lookupScanOrder
    distinctScanOrder := joinDistinctScanOrder context.leftSchema context.rightSchema
      mayExchange
      (on.any (joinHasRowidEquality context.leftSchema context.rightSchema) ||
        where_.any (joinHasRowidEquality context.leftSchema context.rightSchema))
      (orderBy.map (fun term => (term.reference, term.descending))) }

def joinAliasesNeeded (select : Select) (left right : Core.Schema) : Bool :=
  let hasColumn := fun name => (findColumn? left name).isSome || (findColumn? right name).isSome
  let needed := CoreOrder.needsAliasesWith hasColumn select.columns.toList
  select.sources.toList.any (fun source => source.joinOn.any needed) || select.where_.any needed

def joinQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query := do
  if joinAliasesNeeded select leftSchema rightSchema then unsupported "unresolved joined result alias"
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless leftSource.schema.isNone && leftSource.functionArgs.isNone && leftSource.subquerySql.isNone && rightSource.schema.isNone && rightSource.functionArgs.isNone && rightSource.subquerySql.isNone &&
      leftSource.joinOn.isNone && !rightSource.rightJoin do
    throw "unsupported general verified-MVP SQL: only two-table INNER/CROSS/comma/LEFT JOIN"
  unless select.groupBy.isEmpty && select.having.isNone do
    throw "unsupported general verified-MVP SQL: join SELECT shape"
  unless canonical leftSource.name = canonical leftTable &&
      canonical rightSource.name = canonical rightTable do
    throw "join source/schema mismatch"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  joinQueryBound select rightSource context

/-- LIMIT zero still resolves the original predicates and validates every
operation that SQLite would generate, but emits no predicate value evaluation.
Projection, ordering and source checks retain the ordinary join translator. -/
def joinZeroLayout (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query := do
  if joinAliasesNeeded select leftSchema rightSchema then unsupported "unresolved joined result alias"
  unless select.limit == some 0 do unsupported "zero-limit join requires LIMIT 0"
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  for expression in rightSource.joinOn.toList do
    let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
    unless joinStaticAdmitted context prepared rightSource.leftJoin do
      unsupported "unbound or invalid zero-limit join ON"
  for expression in select.where_.toList do
    let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
    unless joinStaticAdmitted context prepared do
      unsupported "unbound or invalid zero-limit join WHERE"
  joinQuery { select with sources := #[leftSource, { rightSource with joinOn := none }], where_ := none }
    leftTable rightTable leftSchema rightSchema

def joinZeroQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query :=
  (fun query => { query with limit := some 0 }) <$>
    joinZeroLayout select leftTable rightTable leftSchema rightSchema

theorem joinZeroQuery_limit (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (query : CoreJoin.Query)
    (success : joinZeroQuery select leftTable rightTable leftSchema rightSchema = .ok query) :
    query.limit = some 0 := by
  cases translated : joinZeroLayout select leftTable rightTable leftSchema rightSchema with
  | error message => simp [joinZeroQuery, translated, Functor.map, Except.map] at success
  | ok layout =>
      simp [joinZeroQuery, translated, Functor.map, Except.map] at success
      subst query
      rfl

def joinQueryWithZero (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) : Except String CoreJoin.Query :=
  match joinQuery select leftTable rightTable leftSchema rightSchema with
  | .ok query => .ok query
  | .error message =>
      if select.limit == some 0 then joinZeroQuery select leftTable rightTable leftSchema rightSchema
      else .error message

theorem joinQueryWithZero_existing (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (query : CoreJoin.Query)
    (success : joinQuery select leftTable rightTable leftSchema rightSchema = .ok query) :
    joinQueryWithZero select leftTable rightTable leftSchema rightSchema = .ok query := by
  simp [joinQueryWithZero, success]

/-- An outer ON expression has no cursor to initialize when the left
input is empty. Resolution/code-generation checks still use the original ON;
WHERE and every other query component retain ordinary translation. -/
def joinEmptyOnQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query := do
  if select.where_.isSome then return ← unsupported "empty outer ON with WHERE requires cursor planning"
  if joinAliasesNeeded select leftSchema rightSchema then unsupported "unresolved joined result alias"
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless rightSource.leftJoin && (leftRows.isEmpty || rightRows.isEmpty) do
    unsupported "outer ON requires an empty input"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  if !leftRows.isEmpty && rightSource.joinOn.any (joinComputedCursorKey context) then
    unsupported "empty inner cursor still evaluates its search key"
  for expression in rightSource.joinOn.toList do
    let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
    unless joinStaticAdmitted context prepared true do
      unsupported "unbound or invalid empty-input outer ON"
  joinQueryWithZero { select with sources := #[leftSource, { rightSource with joinOn := none }] }
    leftTable rightTable leftSchema rightSchema

theorem joinEmptyOnQuery_where_failure (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (left right : List Core.Row)
    (present : select.where_.isSome = true) :
    (joinEmptyOnQuery select leftTable rightTable leftSchema rightSchema left right).isOk = false := by
  simp [joinEmptyOnQuery, present, unsupported, bind, Except.bind, Except.isOk]
  rfl

def joinQueryForRows (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query :=
  match joinQueryWithZero select leftTable rightTable leftSchema rightSchema with
  | .ok query => .ok query
  | .error message =>
      match joinEmptyOnQuery select leftTable rightTable leftSchema rightSchema leftRows rightRows with
      | .ok query => .ok query
      | .error _ => .error message

theorem joinQueryForRows_existing (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) (query : CoreJoin.Query)
    (success : joinQuery select leftTable rightTable leftSchema rightSchema = .ok query) :
    joinQueryForRows select leftTable rightTable leftSchema rightSchema leftRows rightRows = .ok query := by
  simp [joinQueryForRows, joinQueryWithZero, success]

end CoreSQL

end SQLeanite
