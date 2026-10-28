import SQLeanite.CoreDistinct
import SQLeanite.SQLite.StoredText

/-! Row expressions on the production Core values. Binding is checked on the
whole syntax tree before evaluation, even for empty tables and dead branches. -/
namespace SQLeanite.CoreExpr

structure Context where
  schema : Core.Schema
  sourceName : String
  /-- Columns fixed by the selected equality search, only for WHERE's IN
  materialization. Projection and assignment evaluation use their normal AST. -/
  fixedColumns : List Nat := []
  storedTexts : List SQLite.StoredText := []
  storedSources : List SQLite.StoredText.Source := []
  scalarQuery : Option (List Core.Value → SQLite.Scalar.QueryRequest → Except String SQLite.ScalarValue) := none
  queryAffinity : String → Option SQLite.Affinity := fun _ => none

def Context.column? (ctx : Context) (qualifier : Option String) (name : String) : Option Nat := do
  if qualifier.any (fun q => q.toLower != ctx.sourceName.toLower) then none
  else ctx.schema.column? name

/-- An actual source column shadows a bare TRUE/FALSE keyword before any
constant folding, affinity inference or scan planning. Quoted identifiers bind
as columns, without a string-literal fallback. -/
def Context.bindNames (ctx : Context) (expression : Expr) : Expr :=
  SQLite.Scalar.bindNames (fun name => (ctx.column? none name).isSome) expression

def Context.hasBooleanColumn (ctx : Context) (expression : Expr) : Bool :=
  expression.any fun node => (SQLite.Scalar.booleanKeyword? node).any fun truth =>
    (ctx.column? none (SQLite.Scalar.booleanName truth)).isSome

def Context.affinity (ctx : Context) (expression : Expr) : Option SQLite.Affinity :=
  match SQLite.ExprCollation.strip (SQLite.ExprCollation.stripDeclared (ctx.bindNames expression)) with
  | .column qualifier name => do
      let index ← ctx.column? qualifier name
      return (← ctx.schema.columns[index]?).affinity
  | .scalarSubquery sql => ctx.queryAffinity sql
  | _ => SQLite.Scalar.expressionAffinity expression

/-- Resolve source names independently of scalar/aggregate function admission.
Parser-level zero-AND elimination precedes name checking, as in SQLite. -/
def Context.namesBound (ctx : Context) (expression : Expr) : Bool :=
  !(SQLite.Scalar.prepare (ctx.bindNames expression)).any (fun e => match e with
    | .column qualifier name => (ctx.column? qualifier name).isNone
    | .star qualifier => qualifier.any (fun q => q.toLower != ctx.sourceName.toLower)
    | _ => false)

def Context.admitted (ctx : Context) (expression : Expr) : Bool :=
  !(SQLite.Scalar.prepare (ctx.bindNames expression)).any (fun e => match e with
    | .column qualifier name => (ctx.column? qualifier name).isNone
    | .scalarSubquery _ | .existsSubquery _ | .inSubquery .. => ctx.scalarQuery.isNone
    | _ => SQLite.Scalar.forbidden e)

def Context.validate (ctx : Context) (expression : Expr) : Except String Unit := do
  if let some message := SQLite.Scalar.resolutionError (fun q n => (ctx.column? q n).isSome) expression then throw message
  if let some message := SQLite.Scalar.aggregateMisuse (ctx.bindNames expression) then throw message
  if ctx.admitted expression then pure ()
  else throw "unsupported or unbound row expression"

/-- Invalid UTF-8 TEXT retains its original bytes in the scalar representation;
no replacement character can change a stored sequence during expression reads. -/
def value : Core.Value → Except String Value
  | .null => .ok .null
  | .integer i => .ok (.integer i.value)
  | .realBits bits => .ok (.real (Float.ofBits (UInt64.ofNat bits.val)))
  | .blob payload => .ok (.blob payload.bytes.toArray)
  | .text payload => match String.fromUTF8? (ByteArray.mk payload.bytes.toArray) with
      | some s => .ok (.text s)
      | none => .ok (.textBytes payload.bytes.toArray)

theorem value_invalid_text (payload : PhysicalCodec.Text)
    (invalid : String.fromUTF8? (ByteArray.mk payload.bytes.toArray) = none) :
    value (.text payload) = .ok (.textBytes payload.bytes.toArray) := by
  simp [value, invalid]

def Context.lookup (ctx : Context) (row : List Core.Value)
    (qualifier : Option String) (name : String) : Except String Value := do
  let index ← match ctx.column? qualifier name with
    | some i => .ok i
    | none => .error s!"no such column: {name}"
  match row[index]? with
  | some v => value v
  | none => .error "row expression column is outside the input row"

/-- Native bytes originate in the same validated physical snapshot. The
logical value must match before its original representation can be attached. -/
def Context.lookupScalar (ctx : Context) (row : List Core.Value)
    (qualifier : Option String) (name : String) : Except String SQLite.ScalarValue := do
  let value ← ctx.lookup row qualifier name
  let plain := SQLite.Scalar.plainScalar value
  if ctx.storedTexts.isEmpty then return plain
  let textual := match value with | .text _ | .textBytes _ => true | _ => false
  unless textual do return plain
  let some column := ctx.column? qualifier name | return plain
  let sources : List SQLite.StoredText.Source := if ctx.storedSources.isEmpty then
      [{ table := ctx.schema.name, rowidColumn := ctx.schema.primaryKey, offset := 0, width := ctx.schema.columns.length }]
    else ctx.storedSources
  let some original := sources.findSome? (fun (source : SQLite.StoredText.Source) => do
      unless source.offset ≤ column && column < source.offset + source.width do none
      let some (PhysicalCodec.Value.integer rowid) := row[source.rowidColumn]? | none
      ctx.storedTexts.find? (fun original => original.table == source.table &&
        original.rowid == rowid.value && original.column == column - source.offset)) | return plain
  unless SQLite.TextEncoding.fromStorage original.encoding original.bytes == SQLite.Text.bytes value do return plain
  return { value, textEncoding := original.encoding, encodedText := some original.bytes }

theorem lookupScalar_value (ctx : Context) (row : List Core.Value)
    (qualifier : Option String) (name : String) :
    (ctx.lookupScalar row qualifier name).map (·.value) = ctx.lookup row qualifier name := by
  cases outcome : ctx.lookup row qualifier name with
  | error message => simp [Context.lookupScalar, outcome, bind, Except.bind, pure, Except.pure, Except.map]
  | ok value =>
      simp only [Context.lookupScalar, outcome, bind, Except.bind]
      repeat' (first | rfl | split)

def Context.eval (ctx : Context) (row : List Core.Value) (expression : Expr) :
    Except String Value :=
  (·.value) <$> SQLite.Scalar.evalTypedQueryWith
    (ctx.lookupScalar row)
    ctx.affinity ((ctx.scalarQuery.map (fun execute => execute row)).getD
      (fun _ => .error "unsupported constant expression")) (ctx.bindNames expression)

/-- Evaluation before a value crosses the storage boundary retains the subtype
returned by the expression, including the selected arm of CASE or COALESCE. -/
def Context.evalTyped (ctx : Context) (row : List Core.Value) (expression : Expr) :
    Except String SQLite.ScalarValue :=
  SQLite.Scalar.evalTypedQueryWith
    (ctx.lookupScalar row)
    ctx.affinity ((ctx.scalarQuery.map (fun execute => execute row)).getD
      (fun _ => .error "unsupported constant expression")) (ctx.bindNames expression)

/-- Expand each star in place, keeping visible-column order and result width. -/
def Context.projection (ctx : Context) (columns : List ResultColumn) : Except String (List Expr) := do
  let mut expressions := []
  for column in columns do
    match column.expr with
    | .star qualifier =>
        if qualifier.any (fun q => q.toLower != ctx.sourceName.toLower) then
          throw "no such table or alias in qualified star"
        expressions := expressions ++ ctx.schema.catalogColumns.map (fun c => .column none c.name)
    | expression =>
        ctx.validate expression
        expressions := expressions ++ [expression]
  return expressions

def Context.projectRow (ctx : Context) (row : List Core.Value) : List Expr →
    Except String (List Core.Value)
  | [] => .ok []
  | e :: rest => do
      let v ← SQLSurface.value (← ctx.eval row e)
      return v :: (← ctx.projectRow row rest)

structure ProjectedRow where
  source : List Core.Value
  output : List Core.Value

/-- DISTINCT compares each result with that result expression's collation.
Stored schema collations remain BINARY; an explicit wrapper can override it. -/
def distinctEqual : List Expr → List Core.Value → List Core.Value → Bool
  | [], [], [] => true
  | expression :: expressions, left :: lefts, right :: rights =>
      SQLite.Collation.compareValue ((SQLite.ExprCollation.kind? expression).getD .binary)
        left right == .eq && distinctEqual expressions lefts rights
  | _, _, _ => false

def validateDistinct (expressions : List Expr) : Except String Unit := do
  for expression in expressions do
    discard <| SQLite.ExprCollation.require (SQLite.ExprCollation.kind? expression)

/-- Share SQL numeric equivalence with direct-column Core queries. Keep the
first original output and its source row for the subsequent ordering step. -/
def distinctRows (rows : List ProjectedRow) : List ProjectedRow :=
  Core.stableDistinctBy (fun row => Core.distinctRowKey row.output) rows

def sourceLess : List (Nat × Bool) → ProjectedRow → ProjectedRow → Bool
  | [], _, _ => false
  | (index, descending) :: rest, a, b =>
      let order := PhysicalQuery.compareValue (a.source[index]?.getD .null)
        (b.source[index]?.getD .null)
      if order == .eq then sourceLess rest a b
      else if descending then order == .gt else order == .lt

def Context.projectRows (ctx : Context) (expressions : List Expr) (rows : List (List Core.Value)) :
    Except String (List ProjectedRow) :=
  rows.mapM (fun row => do return { source := row, output := ← ctx.projectRow row expressions })

def Context.constantExpression (ctx : Context) (expression : Expr) : Bool :=
  !(ctx.bindNames expression).any (fun e => match e with
    | .column qualifier name => !(ctx.column? qualifier name).any ctx.fixedColumns.contains
    | .scalarSubquery .. | .inSubquery .. | .existsSubquery .. => true
    | _ => false)

/-- Top-level AND terms use the same WHERE branch evaluator as constant SELECT. -/
def Context.matches (ctx : Context) (row : List Core.Value) (condition : Option Expr) :
    Except String Bool :=
  match condition with
  | none => .ok true
  | some expression => SQLite.Scalar.testTermsTypedWithConstants (ctx.lookupScalar row) ctx.affinity
      ctx.constantExpression
      (SQLite.Scalar.conditionTerms (SQLite.Scalar.prepare (ctx.bindNames expression)))

/-- Constant constraints run before the table loop, including on an empty
input. Preserve their relative order; names are checked independently first. -/
def Context.constantMatchesOn (ctx : Context) (row : List Core.Value)
    (condition : Option Expr) : Except String Bool :=
  match condition with
  | none => .ok true
  | some expression => SQLite.Scalar.testTermsTypedWithConstants (ctx.lookupScalar row) ctx.affinity
      ctx.constantExpression
      ((SQLite.Scalar.conditionTerms (SQLite.Scalar.prepare (ctx.bindNames expression))).filter ctx.constantExpression)

def Context.constantMatches (ctx : Context) (condition : Option Expr) : Except String Bool :=
  ctx.constantMatchesOn [] condition

/-- Evaluate the condition before output expressions; DISTINCT compares the
computed outputs while retaining their source rows for subsequent ordering. -/
def Context.candidate (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) (seen : List (List Core.Value)) (row : List Core.Value) :
    Except String (Option ProjectedRow) := do
  unless ← ctx.matches row condition do return none
  let output ← ctx.projectRow row expressions
  if distinct && seen.any (distinctEqual expressions output) then return none
  return some { source := row, output }

/-- A scan stops immediately after the requested number of surviving outputs.
This matters for errors in predicates and projections beyond a LIMIT. -/
def Context.scan (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) : List (List Core.Value) → Option Nat → List (List Core.Value) →
      Except String (List ProjectedRow)
  | [], _, _ => .ok []
  | row :: rows, remaining, seen => do
      if remaining == some 0 then return []
      match ← ctx.candidate condition expressions distinct seen row with
      | none => ctx.scan condition expressions distinct rows remaining seen
      | some projected =>
          let tail ← ctx.scan condition expressions distinct rows
            (remaining.map (· - 1)) (Core.distinctRowKey projected.output :: seen)
          return projected :: tail

theorem scan_limit_zero (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) (rows seen : List (List Core.Value)) :
    ctx.scan condition expressions distinct rows (some 0) seen = .ok [] := by
  cases rows <;> simp [Context.scan, pure, Except.pure]

theorem scan_length_le (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) (rows : List (List Core.Value)) (remaining : Option Nat)
    (seen : List (List Core.Value)) (output : List ProjectedRow)
    (success : ctx.scan condition expressions distinct rows remaining seen = .ok output) :
    output.length ≤ rows.length := by
  induction rows generalizing remaining seen output with
  | nil => simp [Context.scan] at success; subst output; simp
  | cons row rows ih =>
      simp only [Context.scan] at success
      split at success
      · simp [pure, Except.pure] at success; subst output; simp
      · cases candidate : ctx.candidate condition expressions distinct seen row with
        | error message => simp [candidate, bind, Except.bind] at success
        | ok value =>
          cases value with
          | none =>
            simp only [candidate, bind, Except.bind] at success
            exact Nat.le_trans (ih _ _ _ success) (by simp)
          | some projected =>
            cases tail : ctx.scan condition expressions distinct rows
                (remaining.map (· - 1)) (Core.distinctRowKey projected.output :: seen) with
            | error message => simp [candidate, tail, bind, Except.bind] at success
            | ok rest =>
              simp [candidate, tail, bind, Except.bind, pure, Except.pure] at success
              subst output
              simpa using Nat.succ_le_succ (ih _ _ _ tail)

/-- OFFSET skips surviving source rows before ordinary projection. DISTINCT
must compute each skipped output to recognize duplicates. Once the skip count
is exhausted, reuse the existing LIMIT-aware scan. -/
def Context.scanWindow (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) : List (List Core.Value) → Nat → Option Nat → List (List Core.Value) →
      Except String (List ProjectedRow)
  | rows, 0, remaining, seen => ctx.scan condition expressions distinct rows remaining seen
  | [], _ + 1, _, _ => .ok []
  | row :: rows, skip + 1, remaining, seen => do
      if remaining == some 0 then return []
      if distinct then
        match ← ctx.candidate condition expressions true seen row with
        | none => return ← ctx.scanWindow condition expressions true rows (skip + 1) remaining seen
        | some projected =>
            return ← ctx.scanWindow condition expressions true rows skip remaining
              (Core.distinctRowKey projected.output :: seen)
      else
        let selected ← ctx.matches row condition
        return ← ctx.scanWindow condition expressions false rows
          (if selected then skip else skip + 1) remaining seen

theorem scanWindow_offset_zero (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) (rows seen : List (List Core.Value)) (remaining : Option Nat) :
    ctx.scanWindow condition expressions distinct rows 0 remaining seen =
      ctx.scan condition expressions distinct rows remaining seen := by
  cases rows <;> rfl

theorem scanWindow_limit_zero (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) (rows seen : List (List Core.Value)) (skip : Nat) :
    ctx.scanWindow condition expressions distinct rows skip (some 0) seen = .ok [] := by
  cases skip with
  | zero => rw [scanWindow_offset_zero, scan_limit_zero]
  | succ skip => cases rows <;> simp [Context.scanWindow, pure, Except.pure]

/-- Observation retains already emitted rows even when a later candidate
fails. Erasing that prefix on failure gives the ordinary scan result. -/
structure ScanReport where
  rows : List ProjectedRow := []
  error : Option String := none

def ScanReport.toExcept (report : ScanReport) : Except String (List ProjectedRow) :=
  match report.error with
  | none => .ok report.rows
  | some message => .error message

def ScanReport.prepend (row : ProjectedRow) (report : ScanReport) : ScanReport :=
  { report with rows := row :: report.rows }

theorem ScanReport.prepend_toExcept (row : ProjectedRow) (report : ScanReport) :
    (report.prepend row).toExcept = (List.cons row) <$> report.toExcept := by
  cases report with
  | mk rows error => cases error <;> rfl

def Context.scanObserved (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) : List (List Core.Value) → Option Nat → List (List Core.Value) → ScanReport
  | [], _, _ => {}
  | row :: rows, remaining, seen =>
      if remaining == some 0 then {} else
      match ctx.candidate condition expressions distinct seen row with
      | .error message => { error := some message }
      | .ok none => ctx.scanObserved condition expressions distinct rows remaining seen
      | .ok (some projected) =>
          (ctx.scanObserved condition expressions distinct rows
            (remaining.map (· - 1)) (Core.distinctRowKey projected.output :: seen)).prepend projected

theorem scanObserved_refines (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) (rows : List (List Core.Value)) (remaining : Option Nat)
    (seen : List (List Core.Value)) :
    (ctx.scanObserved condition expressions distinct rows remaining seen).toExcept =
      ctx.scan condition expressions distinct rows remaining seen := by
  induction rows generalizing remaining seen with
  | nil => rfl
  | cons row rows ih =>
      simp only [Context.scanObserved, Context.scan]
      split
      · rfl
      · cases candidate : ctx.candidate condition expressions distinct seen row with
        | error message => simp [ScanReport.toExcept, bind, Except.bind]
        | ok value =>
          cases value with
          | none => simpa [candidate, bind, Except.bind] using ih remaining seen
          | some projected =>
              simp only [bind, Except.bind, ScanReport.prepend_toExcept, ih]
              cases ctx.scan condition expressions distinct rows (remaining.map (· - 1))
                (Core.distinctRowKey projected.output :: seen) <;> rfl

def Context.scanWindowObserved (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) : List (List Core.Value) → Nat → Option Nat → List (List Core.Value) → ScanReport
  | rows, 0, remaining, seen => ctx.scanObserved condition expressions distinct rows remaining seen
  | [], _ + 1, _, _ => {}
  | row :: rows, skip + 1, remaining, seen =>
      if remaining == some 0 then {} else
      if distinct then
        match ctx.candidate condition expressions true seen row with
        | .error message => { error := some message }
        | .ok none => ctx.scanWindowObserved condition expressions true rows (skip + 1) remaining seen
        | .ok (some projected) => ctx.scanWindowObserved condition expressions true rows skip remaining
            (Core.distinctRowKey projected.output :: seen)
      else
        match ctx.matches row condition with
        | .error message => { error := some message }
        | .ok selected => ctx.scanWindowObserved condition expressions false rows
            (if selected then skip else skip + 1) remaining seen

theorem scanWindowObserved_refines (ctx : Context) (condition : Option Expr) (expressions : List Expr)
    (distinct : Bool) (rows : List (List Core.Value)) (skip : Nat) (remaining : Option Nat)
    (seen : List (List Core.Value)) :
    (ctx.scanWindowObserved condition expressions distinct rows skip remaining seen).toExcept =
      ctx.scanWindow condition expressions distinct rows skip remaining seen := by
  induction rows generalizing distinct skip remaining seen with
  | nil => cases skip <;> rfl
  | cons row rows ih =>
      cases skip with
      | zero => exact scanObserved_refines ctx condition expressions distinct (row :: rows) remaining seen
      | succ skip =>
          simp only [Context.scanWindowObserved, Context.scanWindow]
          split
          · rfl
          · split
            · cases candidate : ctx.candidate condition expressions true seen row with
              | error message => simp [ScanReport.toExcept, bind, Except.bind]
              | ok value => cases value <;> simp [bind, Except.bind, ih]
            · cases selected : ctx.matches row condition with
              | error message => simp [ScanReport.toExcept, bind, Except.bind]
              | ok value => simp [bind, Except.bind, ih]

theorem projectRow_width (ctx : Context) (row : List Core.Value)
    (expressions : List Expr) (output : List Core.Value)
    (success : ctx.projectRow row expressions = .ok output) :
    output.length = expressions.length := by
  induction expressions generalizing output with
  | nil => simp [Context.projectRow] at success; cases success; rfl
  | cons e rest ih =>
      simp only [Context.projectRow] at success
      cases ev : ctx.eval row e with
      | error message => simp [ev, bind, Except.bind] at success
      | ok v =>
          cases converted : SQLSurface.value v with
          | error message => simp [ev, converted, bind, Except.bind] at success
          | ok physical =>
              cases projected : ctx.projectRow row rest with
              | error message => simp [ev, converted, projected, bind, Except.bind] at success
              | ok tail =>
                  simp [ev, converted, projected, bind, Except.bind, pure, Except.pure] at success
                  cases success
                  simp [ih tail projected]

theorem eval_column (ctx : Context) (row : List Core.Value)
    (qualifier : Option String) (name : String) :
    ctx.eval row (.column qualifier name) = ctx.lookup row qualifier name := by
  change (ctx.lookupScalar row qualifier name).map (·.value) = ctx.lookup row qualifier name
  exact lookupScalar_value ctx row qualifier name

end SQLeanite.CoreExpr
