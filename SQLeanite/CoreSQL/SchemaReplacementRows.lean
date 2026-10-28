import SQLeanite.CoreJoinUsing
import SQLeanite.CoreSQL.InsertRowsEqRunCoreCommands
import SQLeanite.CoreUpdateRow

namespace SQLeanite
namespace CoreSQL

def schemaReplacementRows (state : Core.State) (tableName : String) (ctx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) :
    List Core.Integer → Except String (Core.State × List Core.Result)
  | [] => .ok (state, [])
  | rowid :: rowids => do
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {tableName}"
      match stored.findRowid? rowid with
      | none => schemaReplacementRows state tableName ctx assignments rowids
      | some row => do
          let updates ← evaluateAssignments ctx row assignments
          let (next, result) ← executeSchemaRow state tableName (Core.applyAssignments row.values updates) (some rowid)
          let (finalState, results) ← schemaReplacementRows next tableName ctx assignments rowids
          return (finalState, result :: results)

def executeSchemaUpdate (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (assignments : List (String × Expr)) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  if CoreDefaultConflict.primaryPolicy stored.schema != .replace then
    return ← executeSchemaScanUpdate state tableName alias stored assignments condition
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  CoreNullConflict.validate stored.schema (bound.map Prod.fst) none
  let trace ← expressionDeletePlan tableName alias stored condition
  let rowids ← CoreUpdateReplace.pending tableName stored.schema.primaryKey trace
  let (next, results) ← schemaReplacementRows state tableName ctx bound rowids
  return (next, [{ changes := (results.map (·.changes)).sum }])

/-- Source compilers can prepare a complete physical candidate while keeping
its typed registers and the actual UPDATE footprint. Ordinary Core callers
omit the preparation pass and retain their original command semantics. -/
structure RowInput where
  cells : List CoreReturning.Cell
  assigned : Option (List Nat) := none
  converted : List Nat := []

/-- Preserve the source distinction between an omitted target list and an
explicit list even when both lower to the same physical column positions. -/
structure InsertTargets where
  columns : Option (Array String)
  implicitWidth : Option Nat := none

structure RowPreparation where
  row : Core.State → Core.Table → ConflictAction → RowInput → Except String (Option RowInput)
  targets : Option (Array String) → Except String InsertTargets := fun columns => .ok { columns }

def prepareInsertTargets (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) (preparation : Option RowPreparation) :
    Except String InsertTargets := do
  let targets ← match preparation with
    | none => pure ({ columns } : InsertTargets)
    | some prepare => prepare.targets columns
  match source with
  | .inl rows =>
      if targets.implicitWidth.isSome && rows.size == 1 && rows[0]!.isEmpty then
        return { targets with columns := none }
      return targets
  | .inr _ => return targets

theorem prepareInsertTargets_ordinary (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) :
    prepareInsertTargets columns source none = .ok { columns } := by
  cases source <;> rfl

/-- RETURNING forces the two-phase UPDATE path even for IGNORE. Values are
read from the current pending row; its original name binds RETURNING while the
UPDATE alias remains the source for RHS and WHERE expressions. -/
def updateReturningRow (state : Core.State) (tableName : String) (ctx outputCtx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (conflict : ConflictAction) (projection : List Expr)
    (rowid : Core.Integer) (preparation : Option RowPreparation := none) : Except String (Core.State × Option (List Core.Value)) := do
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {tableName}"
  let some row := stored.findRowid? rowid | return (state, none)
  let updates ← evaluateAssignmentsTyped ctx row assignments
  let cells := updates.foldl (fun values (index, input) => values.set index input)
    (row.values.map CoreReturning.Cell.plain)
  let some input ← (match preparation with
    | none => pure (some ({ cells, assigned := some (assignments.map Prod.fst), converted := List.range stored.schema.columns.length } : RowInput))
    | some prepare => prepare.row state stored conflict { cells, assigned := some (assignments.map Prod.fst), converted := List.range stored.schema.columns.length }) | return (state, none)
  let cells := input.cells
  let assigned := input.assigned.getD (assignments.map Prod.fst)
  let prepared ← if conflict == .default || conflict == .replace || conflict == .abort then
      CoreReturning.prepareValues ctx.schema cells true
        (if conflict == .replace then some .replace else if conflict == .abort then some .abort else none)
    else pure (some cells)
  let some cells := prepared | return (state, none)
  let values := cells.map (·.value)
  let outcome ← if stored.hasChecks then
      CoreUpdateRow.apply state stored rowid values assigned conflict
    else if conflict == .default then
      executeSchemaRow state tableName values (some rowid)
    else if conflict == .ignore then
      CoreUpdateIgnore.row state tableName ctx.schema rowid values
    else if conflict == .replace then do
      let trace ← CoreUpdateReplace.plan stored rowid values
      let (next, _) ← runCoreCommands state trace
      pure (next, { changes := 1 })
    else do
      let _ ← Core.Row.create ctx.schema values
      let (removed, _) ← Core.execute state (.deleteWhere tableName
        (some (.equal ctx.schema.primaryKey (.integer rowid))))
      Core.execute removed (.insert tableName values)
  let outcome := if outcome.2.changes == 0 then outcome else
    match values[ctx.schema.primaryKey]? with
    | some (.integer rowid) =>
        (outcome.1.recordForeignWrite tableName rowid (some assigned), outcome.2)
    | _ => outcome
  CoreReturning.updatedOutput outputCtx cells projection outcome

theorem updateReturningRow_missing (state : Core.State) (tableName : String)
    (ctx outputCtx : CoreExpr.Context) (assignments : List (Nat × Expr)) (conflict : ConflictAction)
    (projection : List Expr) (rowid : Core.Integer) (stored : Core.Table)
    (found : state.database.findTable? tableName = some stored) (missing : stored.findRowid? rowid = none) :
    updateReturningRow state tableName ctx outputCtx assignments conflict projection rowid = .ok (state, none) := by
  simp [updateReturningRow, found, missing, bind, Except.bind, pure, Except.pure]

def updateReturningRows (state : Core.State) (tableName : String) (ctx outputCtx : CoreExpr.Context)
    (assignments : List (Nat × Expr)) (conflict : ConflictAction) (projection : List Expr)
    (rowids : List Core.Integer) (preparation : Option RowPreparation := none) :
    Except String (Core.State × List (List Core.Value)) :=
  match rowids with
  | [] => .ok (state, [])
  | rowid :: rowids => do
      let (next, output) ← updateReturningRow state tableName ctx outputCtx assignments conflict projection rowid preparation
      let (finalState, outputs) ← updateReturningRows next tableName ctx outputCtx assignments conflict projection rowids preparation
      return (finalState, output.toList ++ outputs)

theorem updateReturningRows_length_le (state : Core.State) (tableName : String)
    (ctx outputCtx : CoreExpr.Context) (assignments : List (Nat × Expr)) (conflict : ConflictAction)
    (projection : List Expr) (rowids : List Core.Integer) (next : Core.State) (outputs : List (List Core.Value))
    (success : updateReturningRows state tableName ctx outputCtx assignments conflict projection rowids = .ok (next, outputs)) :
    outputs.length ≤ rowids.length := by
  induction rowids generalizing state next outputs with
  | nil =>
      simp [updateReturningRows] at success
      rcases success with ⟨_, rfl⟩
      simp
  | cons rowid rowids ih =>
      cases head : updateReturningRow state tableName ctx outputCtx assignments conflict projection rowid with
      | error message => simp [updateReturningRows, head, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨middle, output⟩
          cases tail : updateReturningRows middle tableName ctx outputCtx assignments conflict projection rowids with
          | error message => simp [updateReturningRows, head, tail, bind, Except.bind] at success
          | ok pair =>
              rcases pair with ⟨finalState, more⟩
              simp [updateReturningRows, head, tail, bind, Except.bind, pure, Except.pure] at success
              rcases success with ⟨_, rfl⟩
              have bound := ih middle finalState more tail
              cases output <;> simp_all <;> omega

def executeUpdateReturning (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (assignments : List (String × Expr)) (condition : Option Expr)
    (conflict : ConflictAction) (returning : Array ResultColumn) (preparation : Option RowPreparation := none) :
    Except String (Core.State × List Core.Result) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD tableName }
  let outputCtx : CoreExpr.Context := { schema := stored.schema, sourceName := tableName }
  let bound ← expressionAssignmentsWith true ctx assignments
  if conflict == .default || conflict == .replace then
    CoreNullConflict.validate stored.schema (bound.map Prod.fst) (if conflict == .replace then some .replace else none)
  let projection ← CoreReturning.prepare outputCtx returning.toList
  let trace ← expressionDeletePlan tableName alias stored condition
  let rowids ← CoreUpdateReplace.pending tableName stored.schema.primaryKey trace
  let (next, outputs) ← updateReturningRows state tableName ctx outputCtx bound conflict projection rowids preparation
  return (next, [{ rows := outputs, changes := outputs.length }])

def executeExpressionDelete (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (condition : Option Expr) :
    Except String (Core.State × List Core.Result) := do
  let commands ← expressionDeletePlan tableName alias stored condition
  let (next, results) ← runCoreCommands state commands
  return (next, [{ changes := (results.map (·.changes)).sum }])

/-- Preserve the original selected rows for DELETE RETURNING. All output is
computed before Core mutation/publication; an expression error cannot commit a
prefix of the deletions or emit a partial RETURNING result. -/
def executeDeleteReturning (state : Core.State) (tableName : String) (alias : Option String)
    (stored : Core.Table) (condition : Option Expr) (columns : Array ResultColumn) :
    Except String (Core.State × List Core.Result) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := tableName }
  let expressions ← CoreReturning.prepare ctx columns.toList
  let commands ← expressionDeletePlan tableName alias stored condition
  let rows ← CoreReturning.deletionOutput stored ctx expressions commands
  let (next, results) ← runCoreCommands state commands
  return (next, [{ rows, changes := (results.map (·.changes)).sum }])

theorem executeExpressionDelete_eq_runCoreCommands
    (state : Core.State) (tableName : String) (alias : Option String) (stored : Core.Table)
    (condition : Option Expr) (commands : List Core.Command)
    (translated : expressionDeletePlan tableName alias stored condition = .ok commands) :
    executeExpressionDelete state tableName alias stored condition =
      (fun outcome => (outcome.1, [{ changes := (outcome.2.map (·.changes)).sum }])) <$>
        runCoreCommands state commands := by
  simp only [executeExpressionDelete, translated, bind, Except.bind]
  cases executed : runCoreCommands state commands with
  | error message => rfl
  | ok outcome => rfl

theorem rowDeleteCommands_length_le (tableName : String) (ctx : CoreExpr.Context)
    (condition : Option Expr) (rows : List Core.Row) (commands : List Core.Command)
    (translated : rowDeleteCommands tableName ctx condition rows = .ok commands) :
    commands.length ≤ rows.length := by
  induction rows generalizing commands with
  | nil => simp [rowDeleteCommands] at translated; subst commands; simp
  | cons row rows ih =>
    simp only [rowDeleteCommands] at translated
    cases selected : ctx.matches row.values condition with
    | error message => simp [selected, bind, Except.bind] at translated
    | ok keep =>
      cases tail : rowDeleteCommands tableName ctx condition rows with
      | error message => simp [selected, tail, bind, Except.bind] at translated
      | ok rest =>
        have bound := ih _ tail
        cases keep <;>
          simp [selected, tail, bind, Except.bind, pure, Except.pure] at translated <;>
          subst commands <;> simp only [List.length_cons] <;> omega

structure JoinContext where
  leftTable : String
  rightTable : String
  leftName : String
  rightName : String
  leftSchema : Core.Schema
  rightSchema : Core.Schema
  shared : List CoreJoinUsing.Column := []
  preferRightShared : Bool := false
  coalesceShared : Bool := false

def joinColumn (context : JoinContext) (qualifier : Option String) (name : String) :
    Except String CoreJoin.ColumnRef := do
  let columnName := canonical name
  match qualifier.map canonical with
  | some owner =>
      if owner == context.leftName then
        return ⟨.left, ← column context.leftSchema columnName⟩
      else if owner == context.rightName then
        return ⟨.right, ← column context.rightSchema columnName⟩
      else throw s!"no such table or alias: {owner}"
  | none =>
      let sources : List CoreExpr.Context := [
        { schema := context.leftSchema, sourceName := context.leftName },
        { schema := context.rightSchema, sourceName := context.rightName }]
      match CoreJoinUsing.nameCandidates sources none columnName with
      | [(0, index)] => .ok ⟨.left, index⟩
      | [(1, index)] => .ok ⟨.right, index⟩
      | [(0, li), (1, ri)] =>
          if CoreJoinUsing.merges context.shared name li ri then
            .ok (if context.preferRightShared then ⟨.right, ri⟩ else ⟨.left, li⟩)
          else .error s!"ambiguous column name: {name}"
      | [] => .error s!"no such column: {name}"
      | _ => .error s!"ambiguous column name: {name}"

/-- FULL USING resolves an unqualified shared name to a nullable coalesce.
Qualified references still address their original source cells. -/
def joinNamedOperand (context : JoinContext) (qualifier : Option String) (name : String) :
    Except String CoreJoin.Operand := do
  let reference ← joinColumn context qualifier name
  if context.coalesceShared && qualifier.isNone then
    if let some shared := context.shared.find? (fun shared => shared.name == name.toLower) then
      return .mergedColumn none shared.left shared.right
  return .column reference

def joinHasColumn (context : JoinContext) (name : String) : Bool :=
  (findColumn? context.leftSchema name).isSome || (findColumn? context.rightSchema name).isSome

def joinBindNames (context : JoinContext) (expression : Expr) : Expr :=
  SQLite.Scalar.bindNames (joinHasColumn context) expression

/-- Unary plus and COLLATE preserve a column's value. Their affinity and
comparison-collation effects are handled separately from source binding. -/
def joinColumnAtomFuel? : Nat → Expr → Option (Option String × String)
  | 0, _ => none
  | fuel + 1, expression => match expression with
    | .column qualifier name => some (qualifier, name)
    | .unary .plus expression | .collate expression _ => joinColumnAtomFuel? fuel expression
    | .call name arguments false =>
        (SQLite.Probability.input? name arguments).bind (joinColumnAtomFuel? fuel)
    | _ => none

def joinColumnAtom? (expression : Expr) : Option (Option String × String) :=
  joinColumnAtomFuel? expression.height expression

def joinOperand (context : JoinContext) (expression : Expr) : Except String CoreJoin.Operand :=
  let bound := joinBindNames context expression
  match joinColumnAtom? bound with
  | some (qualifier, name) => joinNamedOperand context qualifier name
  | none => .literal <$> literal bound

def joinColumnDefinition (context : JoinContext) (reference : CoreJoin.ColumnRef) :
    Except String Core.Column :=
  let schema := match reference.side with
    | .left => context.leftSchema
    | .right => context.rightSchema
  match schema.columns[reference.column]? with
  | some column => .ok column
  | none => .error "join column is out of range"

def joinOperandAffinity (context : JoinContext) (expression : Expr)
    (operand : CoreJoin.Operand) : Except String (Option SQLite.Affinity) :=
  let unaffined := match SQLite.ExprCollation.strip expression with
    | .unary .plus _ => true
    | .call name _ _ => SQLite.Probability.recognizesName name
    | _ => false
  if unaffined then .ok none
  else match operand with
    | .column reference | .coercedColumn _ reference =>
        do return some (← joinColumnDefinition context reference).affinity
    | .literal _ => .ok (SQLite.Scalar.expressionAffinity expression)
    | .mergedColumn _ left _ =>
        do return some (← joinColumnDefinition context ⟨.left, left⟩).affinity

theorem joinOperandAffinity_plus (context : JoinContext) (expression : Expr)
    (operand : CoreJoin.Operand) : joinOperandAffinity context (.unary .plus expression) operand = .ok none := rfl

def joinOperandCoerce (context : JoinContext) (aff : SQLite.Affinity) :
    CoreJoin.Operand → Except String CoreJoin.Operand
  | .literal value => .ok (.literal (SQLite.PhysicalAffinity.comparison aff value))
  | operand@(.column reference) => do
      let target ← joinColumnDefinition context reference
      if aff == .blob || aff.comparison == target.affinity.comparison then return operand
      return .coercedColumn aff reference
  | .mergedColumn prior left right =>
      .ok (.mergedColumn (if aff == .blob then prior else some aff) left right)
  | .coercedColumn _ _ => unsupported "repeated join operand coercion"

def joinComparison (context : JoinContext)
    (operation : CoreJoin.Operand → CoreJoin.Operand → CoreJoin.Predicate)
    (left right : Expr) : Except String CoreJoin.Predicate := do
  let kind ← SQLite.ExprCollation.require (SQLite.ExprCollation.binaryKind? left right)
  let a ← joinOperand context left
  let b ← joinOperand context right
  let aff := SQLite.Scalar.comparisonAffinity
    (← joinOperandAffinity context left a) (← joinOperandAffinity context right b)
  return CoreJoin.Predicate.withCollation kind
    (operation (← joinOperandCoerce context aff a) (← joinOperandCoerce context aff b))

/-- USING applies ordinary left-to-right equality affinity to each declared
shared column. The result is an ON predicate, before LEFT null-extension. -/
def joinUsingPredicate (context : JoinContext) : Except String (Option CoreJoin.Predicate) :=
  context.shared.foldlM (fun prior column => do
    let left : CoreJoin.Operand := .column ⟨.left, column.left⟩
    let right : CoreJoin.Operand := .column ⟨.right, column.right⟩
    let a ← joinColumnDefinition context ⟨.left, column.left⟩
    let b ← joinColumnDefinition context ⟨.right, column.right⟩
    let aff := SQLite.Scalar.comparisonAffinity (some a.affinity) (some b.affinity)
    let comparison : CoreJoin.Predicate := .equal
      (← joinOperandCoerce context aff left) (← joinOperandCoerce context aff right)
    return some ((prior.map (fun predicate => .and predicate comparison)).getD comparison)) none

/-- The unshadowed TRUE/FALSE keyword on the right of IS selects truth
conversion. Other operands use ordinary comparison affinity with NULL safety. -/
def joinIsComparison (context : JoinContext) (negated : Bool) (left right : Expr) :
    Except String CoreJoin.Predicate := do
  let predicate ← match SQLite.Scalar.isTruthKeyword? right with
    | some expected => do
        let operand ← joinOperand context left
        pure (CoreJoin.Predicate.isTruth operand expected)
    | none => joinComparison context CoreJoin.Predicate.isEqual left right
  return if negated then .not predicate else predicate

def joinOperandList (context : JoinContext) : List Expr → Except String (List CoreJoin.Operand)
  | [] => .ok []
  | expression :: rest => List.cons <$> joinOperand context expression <*> joinOperandList context rest

/-- IN-list comparison ignores right-operand affinity and collation. Parser
preparation separately handles empty lists and a single constant choice. -/
def joinInList (context : JoinContext) (argument : Expr) (values : Array Expr)
    (negated applyLeftAffinity : Bool) : Except String CoreJoin.Predicate := do
  let left ← joinOperand context argument
  let right ← joinOperandList context values.toList
  let kind ← SQLite.ExprCollation.require (SQLite.ExprCollation.kind? argument)
  let affinity ← if applyLeftAffinity then
      (fun found => found.getD .blob) <$> joinOperandAffinity context argument left
    else pure .blob
  let left ← joinOperandCoerce context affinity left
  let right ← right.mapM (joinOperandCoerce context affinity)
  let predicate := CoreJoin.Predicate.membership kind left right
  return if negated then .not predicate else predicate

def joinPredicateRaw (context : JoinContext) : Expr →
    Except String CoreJoin.Predicate
  | .inList argument values negated affinity => joinInList context argument values negated affinity
  | .binary .is left right => joinIsComparison context false left right
  | .binary .isNot left right => joinIsComparison context true left right
  | .binary .eq left right =>
      joinComparison context .equal left right
  | .binary .ne left right =>
      joinComparison context .notEqual left right
  | .binary .lt left right =>
      joinComparison context (.compare .less) left right
  | .binary .le left right =>
      joinComparison context (.compare .lessEqual) left right
  | .binary .gt left right =>
      joinComparison context (.compare .greater) left right
  | .binary .ge left right =>
      joinComparison context (.compare .greaterEqual) left right
  | .isNull operand false => .isNull <$> joinOperand context operand
  | .isNull operand true => .not <$> (.isNull <$> joinOperand context operand)
  | .unary .not expression => .not <$> joinPredicateRaw context expression
  | .binary .and left right =>
      .and <$> joinPredicateRaw context left <*> joinPredicateRaw context right
  | .binary .or left right =>
      .or <$> joinPredicateRaw context left <*> joinPredicateRaw context right
  | expression => .truthy <$> joinOperand context expression

/-- All names/functions resolve before code generation. Each top-level AND
term is generated separately, even when an earlier false term skips its value. -/
def joinStaticAdmitted (context : JoinContext) (prepared : Expr) (outer : Bool := false) : Bool :=
  !(prepared.any (fun expression => match expression with
      | .column qualifier name => !(joinColumn context qualifier name).isOk
      | _ => SQLite.StaticCondition.resolutionForbidden expression)) &&
    (SQLite.Scalar.conditionTerms prepared).all (fun term => SQLite.StaticCondition.codegenAdmitted term outer)

/-- Name binding precedes parser preparation. A statically decided condition
still validates every resolved name and every required generated operation. -/
def joinPredicate (context : JoinContext) (expression : Expr) (outer : Bool := false) : Except String CoreJoin.Predicate := do
  let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
  match SQLite.StaticCondition.classify outer prepared with
  | none => joinPredicateRaw context prepared
  | some truth =>
      unless joinStaticAdmitted context prepared outer do unsupported "unbound or invalid static join condition"
      return CoreJoin.Predicate.constant truth

def joinSideColumns (side : CoreJoin.Side) (count : Nat) :
    List CoreJoin.ColumnRef :=
  (List.range count).map fun index => ⟨side, index⟩

def joinVisibleColumns (side : CoreJoin.Side) (schema : Core.Schema) :
    List CoreJoin.ColumnRef :=
  schema.visibleColumnIndices.map fun index => ⟨side, index⟩

/-- Literal/unary atoms are total before row evaluation. Boolean keywords
are constants only after source-column name binding has left them unbound. -/
def joinLiteralExpression : Expr → Bool
  | .literal .. => true
  | .unary _ expression => joinLiteralExpression expression
  | expression => (SQLite.Scalar.booleanKeyword? expression).isSome

/-- Expanded left stars keep their original positions/names but RIGHT USING
reads the merged value from the right input, including qualified left stars. -/
def joinMergedStar (context : JoinContext) (reference : CoreJoin.ColumnRef) : CoreJoin.ColumnRef :=
  if context.preferRightShared && reference.side == .left then
    match context.shared.find? (fun column => column.left == reference.column) with
    | some column => ⟨.right, column.right⟩
    | none => reference
  else reference

theorem joinMergedStar_right (context : JoinContext) (index : Nat) (shared : CoreJoinUsing.Column)
    (prefer : context.preferRightShared = true)
    (found : context.shared.find? (fun column => column.left == index) = some shared) :
    joinMergedStar context ⟨.left, index⟩ = ⟨.right, shared.right⟩ := by
  simp [joinMergedStar, prefer, found]

def joinStarOperand (context : JoinContext) (reference : CoreJoin.ColumnRef) : CoreJoin.Operand :=
  if context.coalesceShared && reference.side == .left then
    match context.shared.find? (fun shared => shared.left == reference.column) with
    | some shared => .mergedColumn none shared.left shared.right
    | none => .column reference
  else .column (joinMergedStar context reference)

end CoreSQL

end SQLeanite
