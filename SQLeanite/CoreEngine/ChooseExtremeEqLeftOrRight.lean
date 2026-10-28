import SQLeanite.CoreCatalogData
import SQLeanite.CoreEngine.MaxDivLeMax
import SQLeanite.CoreJoin.QueryEvalEmptyLeft
import SQLeanite.SQLite.ApplicationHeader
import SQLeanite.SQLite.SchemaHash

namespace SQLeanite
namespace Core

theorem chooseExtreme_eq_left_or_right (minimum : Bool) (left right : Value) :
    chooseExtreme minimum left right = left ∨
      chooseExtreme minimum left right = right := by
  cases left <;> cases right
  all_goals
    rw [chooseExtreme]
    first | (split <;> simp) | simp
  all_goals simp_all

theorem extremeValues_mem_or_null (minimum : Bool) (values : List Value) :
    extremeValues minimum values = .null ∨
      extremeValues minimum values ∈ values := by
  induction values with
  | nil => simp [extremeValues]
  | cons value values induction =>
      simp only [extremeValues]
      rcases chooseExtreme_eq_left_or_right minimum value
          (extremeValues minimum values) with chosen | chosen
      · exact .inr (by simp [chosen])
      · rcases induction with empty | member
        · exact .inl (by simpa [chosen] using empty)
        · exact .inr (by simp [chosen, member])

inductive GroupOutput where
  /-- Project a position in the query's group-key tuple. -/
  | key (position : Nat)
  | countStar
  | countColumn (column : Nat)
  | sumColumn (column : Nat)
  | averageColumn (column : Nat)
  | totalColumn (column : Nat)
  | minColumn (column : Nat)
  | maxColumn (column : Nat)
  deriving DecidableEq, Repr

structure GroupQuery where
  groupBy : List Nat
  outputs : List GroupOutput
  predicate : Option Predicate := none

def GroupQuery.originalKey (query : GroupQuery) (row : Row) : List Value :=
  query.groupBy.map row.value

/-- GROUP BY uses the same exact BINARY numeric equivalence as DISTINCT. -/
def GroupQuery.rowKey (query : GroupQuery) (row : Row) : List Value :=
  distinctRowKey (query.originalKey row)

def GroupQuery.selectedRows (query : GroupQuery) (rows : List Row) : List Row :=
  rows.filter (selects query.predicate)

/-- Canonical comparison keys, presented in SQLite's ascending group order.
Original group output values are read from a representative source row. -/
def GroupQuery.groupKeys (query : GroupQuery) (rows : List Row) : List (List Value) :=
  (deduplicate ((query.selectedRows rows).map query.rowKey)).mergeSort
    (fun a b => PhysicalQuery.compareValues a b != .gt)

theorem GroupQuery.groupKeys_nodup (query : GroupQuery) (rows : List Row) :
    (query.groupKeys rows).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (deduplicate_nodup _)

theorem GroupQuery.mem_groupKeys_iff (query : GroupQuery) (rows : List Row)
    (key : List Value) :
    key ∈ query.groupKeys rows ↔
      ∃ row ∈ rows, selects query.predicate row = true ∧ query.rowKey row = key := by
  rw [GroupQuery.groupKeys, (List.mergeSort_perm _ _).mem_iff, mem_deduplicate]
  simp only [GroupQuery.selectedRows, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨row, ⟨member, selected⟩, equal⟩
    exact ⟨row, member, selected, equal⟩
  · rintro ⟨row, member, selected, equal⟩
    exact ⟨row, ⟨member, selected⟩, equal⟩

def GroupQuery.keyCount (query : GroupQuery) (rows : List Row)
    (key : List Value) : Nat :=
  (query.selectedRows rows).countP fun row => query.rowKey row == key

def GroupQuery.keyRows (query : GroupQuery) (rows : List Row)
    (key : List Value) : List Row :=
  (query.selectedRows rows).filter fun row => query.rowKey row == key

/-- A MIN/MAX step updates bare columns only on improvement. If every input
is NULL, SQLite keeps loading the current row because no best value exists. -/
def extremeRepresentativeStep (minimum : Bool) (column : Nat) (best row : Row) : Row :=
  if best.value column == .null then row
  else if row.value column == .null then best
  else
    let order := PhysicalQuery.compareValue (row.value column) (best.value column)
    if (minimum && order == .lt) || (!minimum && order == .gt) then row else best

theorem extremeRepresentativeStep_member (minimum : Bool) (column : Nat) (best row : Row) :
    extremeRepresentativeStep minimum column best row = best ∨
      extremeRepresentativeStep minimum column best row = row := by
  unfold extremeRepresentativeStep
  split
  · exact Or.inr rfl
  · split
    · exact Or.inl rfl
    · dsimp only
      split
      · exact Or.inr rfl
      · exact Or.inl rfl

def extremeRepresentative (minimum : Bool) (column : Nat) (first : Row) : List Row → Row
  | [] => first
  | row :: rows => extremeRepresentative minimum column
      (extremeRepresentativeStep minimum column first row) rows

theorem extremeRepresentative_mem (minimum : Bool) (column : Nat) (first : Row) (rows : List Row) :
    extremeRepresentative minimum column first rows ∈ first :: rows := by
  induction rows generalizing first with
  | nil => simp [extremeRepresentative]
  | cons row rows ih =>
      change extremeRepresentative minimum column (extremeRepresentativeStep minimum column first row) rows ∈ first :: row :: rows
      have member := ih (extremeRepresentativeStep minimum column first row)
      rcases List.mem_cons.mp member with same | tail
      · rw [same]
        rcases extremeRepresentativeStep_member minimum column first row with best | current
        · simp [best]
        · simp [current]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ tail)

/-- Repeated aggregate expressions share one SQLite accumulator. The last
unique MIN/MAX accumulator controls bare-column row selection. -/
def GroupQuery.controllingExtreme (query : GroupQuery) : Option (Bool × Nat) :=
  (stableDistinctBy id query.outputs).foldl (fun current output =>
    match output with
    | .minColumn column => some (true, column)
    | .maxColumn column => some (false, column)
    | _ => current) none

def GroupQuery.representative (query : GroupQuery) (rows : List Row) (key : List Value) : Option Row :=
  match query.keyRows rows key with
  | [] => none
  | first :: rest => some <| match query.controllingExtreme with
      | none => first
      | some (minimum, column) => extremeRepresentative minimum column first rest

theorem GroupQuery.representative_mem (query : GroupQuery) (rows : List Row) (key : List Value)
    (chosen : Row) (success : query.representative rows key = some chosen) :
    chosen ∈ query.keyRows rows key := by
  unfold GroupQuery.representative at success
  cases found : query.keyRows rows key with
  | nil => simp [found] at success
  | cons first rest =>
      cases controls : query.controllingExtreme with
      | none => simp [found, controls] at success; subst chosen; simp
      | some control =>
          rcases control with ⟨minimum, column⟩
          simp [found, controls] at success
          subst chosen
          exact extremeRepresentative_mem minimum column first rest

theorem GroupQuery.representative_key (query : GroupQuery) (rows : List Row) (key : List Value)
    (chosen : Row) (success : query.representative rows key = some chosen) :
    query.rowKey chosen = key := by
  have member := query.representative_mem rows key chosen success
  simpa only [beq_iff_eq] using (List.mem_filter.mp member).2

def GroupQuery.outputKey (query : GroupQuery) (rows : List Row) (key : List Value) : List Value :=
  ((query.representative rows key).map query.originalKey).getD key

def GroupQuery.outputValue (query : GroupQuery) (rows : List Row)
    (key : List Value) : GroupOutput → Except String Value
  | .key position => .ok ((query.outputKey rows key)[position]?.getD .null)
  | .countStar =>
      .integer <$> countInteger (query.keyRows rows key).length
  | .countColumn column =>
      .integer <$> countInteger ((query.keyRows rows key).countP
        fun row => row.value column != .null)
  | .sumColumn column => sumColumn column (query.keyRows rows key)
  | .averageColumn column => .ok (averageColumn column (query.keyRows rows key))
  | .totalColumn column => .ok (totalColumn column (query.keyRows rows key))
  | .minColumn column => .ok (extremeColumn true column (query.keyRows rows key))
  | .maxColumn column => .ok (extremeColumn false column (query.keyRows rows key))

def GroupQuery.evalOutputs (query : GroupQuery) (rows : List Row)
    (key : List Value) : List GroupOutput → Except String (List Value)
  | [] => .ok []
  | output :: outputs =>
      match query.outputValue rows key output with
      | .error message => .error message
      | .ok value =>
          match query.evalOutputs rows key outputs with
          | .error message => .error message
          | .ok values => .ok (value :: values)

theorem GroupQuery.evalOutputs_length (query : GroupQuery) (rows : List Row)
    (key : List Value) (outputs : List GroupOutput) (result : List Value)
    (success : query.evalOutputs rows key outputs = .ok result) :
    result.length = outputs.length := by
  induction outputs generalizing result with
  | nil =>
      simp [GroupQuery.evalOutputs] at success
      subst result
      rfl
  | cons output outputs induction =>
      simp only [GroupQuery.evalOutputs] at success
      cases head : query.outputValue rows key output with
      | error message => simp [head] at success
      | ok value =>
          simp only [head] at success
          cases tail : query.evalOutputs rows key outputs with
          | error message => simp [tail] at success
          | ok values =>
              simp [tail] at success
              subst result
              simp [induction values tail]

def GroupQuery.evalKeys (query : GroupQuery) (rows : List Row) :
    List (List Value) → Except String (List (List Value))
  | [] => .ok []
  | key :: keys =>
      match query.evalOutputs rows key query.outputs with
      | .error message => .error message
      | .ok result =>
          match query.evalKeys rows keys with
          | .error message => .error message
          | .ok results =>
              .ok (result :: results)

def GroupQuery.eval (query : GroupQuery) (rows : List Row) :
    Except String (List (List Value)) :=
  query.evalKeys rows (query.groupKeys rows)

theorem GroupQuery.evalKeys_width (query : GroupQuery) (rows : List Row)
    (keys : List (List Value)) (output : List (List Value))
    (success : query.evalKeys rows keys = .ok output) :
    ∀ result ∈ output, result.length = query.outputs.length := by
  induction keys generalizing output with
  | nil =>
      simp [GroupQuery.evalKeys] at success
      subst output
      simp
  | cons key keys induction =>
      simp only [GroupQuery.evalKeys] at success
      cases evaluated : query.evalOutputs rows key query.outputs with
      | error message => simp [evaluated] at success
      | ok head =>
          simp only [evaluated] at success
          cases tailResult : query.evalKeys rows keys with
          | error message => simp [tailResult] at success
          | ok tail =>
              simp [tailResult] at success
              subst output
              have headWidth :=
                query.evalOutputs_length rows key query.outputs head evaluated
              intro result member
              simp only [List.mem_cons] at member
              rcases member with equal | member
              · subst result
                exact headWidth
              · exact induction _ tailResult result member

theorem GroupQuery.eval_width (query : GroupQuery) (rows : List Row)
    (output : List (List Value))
    (success : query.eval rows = .ok output) :
    ∀ result ∈ output, result.length = query.outputs.length := by
  exact query.evalKeys_width rows (query.groupKeys rows) output success

inductive Command where
  | createTable (schema : Schema)
  | createIndex (table : String) (index : Index)
  | insert (table : String) (values : List Value)
  | replace (table : String) (values : List Value)
  | deleteWhere (table : String) (predicate : Option Predicate)
  | updateWhere (table : String) (assignments : List (Nat × Value))
      (predicate : Option Predicate)
  | query (table : String) (query : Query)
  | count (table : String) (target : CountTarget) (predicate : Option Predicate)
  | sum (table : String) (column : Nat) (predicate : Option Predicate)
  | extreme (table : String) (minimum : Bool) (column : Nat)
      (predicate : Option Predicate)
  | group (table : String) (query : GroupQuery)
  | join (left right : String) (query : CoreJoin.Query)
  | begin
  | commit
  | rollback

def Command.writes : Command → Bool
  | .createTable _ | .createIndex .. | .insert .. | .replace .. | .deleteWhere .. |
      .updateWhere .. => true
  | _ => false

/-- A named transaction mark. The oldest mark owns the transaction only when
SAVEPOINT opened it outside an existing BEGIN. Snapshots are immutable values. -/
structure Savepoint where
  name : String
  snapshot : Database
  startsTransaction : Bool
  headers : SQLite.ApplicationHeader.Schemas := {}
  previousHeaderSnapshot : Option SQLite.ApplicationHeader.Schemas := none

/-- Accepted SQL row writes used by connection-level constraints. An absent
column set denotes INSERT; UPDATE retains its actual SET positions. -/
structure ForeignWrite where
  table : String
  rowid : Integer
  columns : Option (List Nat)

structure State where
  database : Database
  transactionSnapshot : Option Database := none
  savepoints : List Savepoint := []
  headers : SQLite.ApplicationHeader.Schemas := {}
  transactionHeaderSnapshot : Option SQLite.ApplicationHeader.Schemas := none
  lastChanges : Nat := 0
  totalChanges : Nat := 0
  lastInsertRowid : Int := 0
  foreignKeys : Bool := false
  /-- Read compiler context for persistent VIEW/trigger programs. -/
  schemaProgram : Bool := false
  foreignWrites : List ForeignWrite := []
  schemaHash : Option SQLite.SchemaHash.State := none
  transactionSchemaHash : Option SQLite.SchemaHash.State := none
  schemaHashSavepoints : List (String × SQLite.SchemaHash.State) := []
  catalog : CoreCatalogData.State := {}

def State.schemaHashValue (state : State) : SQLite.SchemaHash.State :=
  match state.schemaHash with
  | some cached => cached
  | none => SQLite.SchemaHash.build (state.database.tables.map (·.schema.name) ++
      state.catalog.current.views.map (·.definition.name))

def State.recordForeignWrite (state : State) (table : String) (rowid : Integer)
    (columns : Option (List Nat)) : State :=
  if state.foreignKeys then { state with foreignWrites := { table, rowid, columns } :: state.foreignWrites }
  else state

theorem State.recordForeignWrite_database (state : State) (table : String) (rowid : Integer)
    (columns : Option (List Nat)) :
    (state.recordForeignWrite table rowid columns).database = state.database := by
  unfold recordForeignWrite
  split <;> rfl

def State.empty : State := { database := Database.empty }

def execute (state : State) : Command → Except String (State × Result)
  | .createTable schema => do
      let database ← state.database.createTable schema
      return ({ state with database }, {})
  | .createIndex tableName index => do
      let database ← state.database.modifyTable tableName fun table =>
        table.addIndex index
      return ({ state with database }, {})
  | .insert tableName values => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let replacement ← table.insertValues values
      let database ← state.database.updateTable replacement
      return ({ state with
        database := database
        lastInsertRowid := ((table.createRow values).toOption.map (·.rowid.value)).getD state.lastInsertRowid }, { changes := 1 })
  | .replace tableName values => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let replacement ← table.replaceValues values
      let database ← state.database.updateTable replacement
      return ({ state with
        database := database
        lastInsertRowid := ((table.createReplacementRow values).toOption.map (·.rowid.value)).getD state.lastInsertRowid }, { changes := 1 })
  | .deleteWhere tableName predicate => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let replacement ← table.retainRows fun row => !selects predicate row
      let database ← state.database.updateTable replacement
      return ({ state with database }, {
        changes := table.rows.length - replacement.rows.length })
  | .updateWhere tableName assignments predicate => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let (replacement, changes) ← table.updateWhere assignments predicate
      let database ← state.database.updateTable replacement
      return ({ state with database }, { changes })
  | .query tableName query => do
      let table ← match state.database.findTable? tableName with
        | some table => .ok table
        | none => .error s!"no such table: {tableName}"
      let optimized := query.optimize
      return (state, { rows := optimized.eval (table.plannedRows optimized) })
  | .count tableName target predicate =>
      match state.database.findTable? tableName with
      | none => .error s!"no such table: {tableName}"
      | some table =>
          match countInteger (countRows target predicate table.rows) with
          | .error message => .error message
          | .ok count => .ok (state, { rows := [[.integer count]] })
  | .sum tableName column predicate =>
      match state.database.findTable? tableName with
      | none => .error s!"no such table: {tableName}"
      | some table =>
          match sumColumn column (table.rows.filter (selects predicate)) with
          | .error message => .error message
          | .ok value => .ok (state, { rows := [[value]] })
  | .extreme tableName minimum column predicate =>
      match state.database.findTable? tableName with
      | none => .error s!"no such table: {tableName}"
      | some table =>
          let value := extremeColumn minimum column
            (table.rows.filter (selects predicate))
          .ok (state, { rows := [[value]] })
  | .group tableName query =>
      match state.database.findTable? tableName with
      | none => .error s!"no such table: {tableName}"
      | some table =>
          match query.eval table.rows with
          | .error message => .error message
          | .ok rows => .ok (state, { rows })
  | .join leftName rightName query => do
      let left ← match state.database.findTable? leftName with
        | some table => .ok table
        | none => .error s!"no such table: {leftName}"
      let right ← match state.database.findTable? rightName with
        | some table => .ok table
        | none => .error s!"no such table: {rightName}"
      return (state, { rows := query.evalPlanned left right })
  | .begin =>
      if state.transactionSnapshot.isSome then .error "cannot start a transaction within a transaction"
      else .ok ({ state with
        transactionSnapshot := some state.database
        transactionHeaderSnapshot := some state.headers }, {})
  | .commit =>
      if state.transactionSnapshot.isSome then
        .ok ({ state with
          transactionSnapshot := none
          savepoints := []
          transactionHeaderSnapshot := none }, {})
      else .error "cannot commit - no transaction is active"
  | .rollback =>
      match state.transactionSnapshot with
      | some snapshot => .ok ({
          database := snapshot
          headers := state.transactionHeaderSnapshot.getD state.headers
          foreignKeys := state.foreignKeys }, {})
      | none => .error "cannot rollback - no transaction is active"

/-- Explicit containment boundary for an *uncertified* effectful traversal.
Certified candidates never call this function.  General or externally-mutated
files may still offer physical candidates without a kernel witness; those are
compared with the verified executor and rejected to the ordinary path on any
disagreement. -/
def executeUncertifiedQueryWithCandidates (state : State) (tableName : String)
    (query : Query) (candidates : List Row) : Except String (State × Result) :=
  match state.database.findTable? tableName with
  | none => .error s!"no such table: {tableName}"
  | some table =>
      let optimized := query.optimize
      let physicalResult := optimized.eval candidates
      let verifiedResult := optimized.eval (table.plannedRows optimized)
      if _same : physicalResult = verifiedResult then
        .ok (state, { rows := physicalResult })
      else execute state (.query tableName query)

end Core

end SQLeanite
