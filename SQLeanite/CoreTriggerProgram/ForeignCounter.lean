import SQLeanite.CoreForeignKey
import SQLeanite.CoreTriggerProgram.Binding

namespace SQLeanite.CoreTriggerProgram.ForeignCounter

/-- VDBE's immediate counter is signed. FkIfZero guards an entire child scan,
not each decrement, and therefore cannot be modelled by saturating arithmetic. -/
def decrement (counter : Int) (count : Nat) : Int :=
  if counter == 0 then counter else counter - Int.ofNat count

def require (counter : Int) : Except String Unit :=
  if counter == 0 then .ok () else .error "FOREIGN KEY constraint failed"

def key (schema : Core.Schema) (values : List Core.Value) : Option Core.Integer := do
  let .integer value ← values[schema.primaryKey]? | none
  return value

def equal (edge : CoreForeignKey.Edge) (child parent : Core.Value) : Bool :=
  PhysicalQuery.sqlEquals (SQLite.PhysicalAffinity.comparison edge.affinity child) parent == .true

def missing (database : Core.Database) (edge : CoreForeignKey.Edge) (value : Core.Value) : Bool :=
  value != .null && !(CoreForeignKeyData.referenceSatisfied
    (CoreNames.table? database edge.parent) edge.parentColumn value)

def modified (table : Core.Table) (statement : Statement) (position : Nat) : Bool :=
  match statement with
  | .update _ _ assignments .. => CoreForeignKey.affectedAssignment table assignments position
  | _ => true

def parentChildren (database : Core.Database) (edge : CoreForeignKey.Edge)
    (parent : Core.Value) (exclude : Option Core.Integer) : Nat :=
  let rows := (CoreNames.table? database edge.child).map (·.rows) |>.getD []
  (rows.filter fun row => !exclude.any (fun own => own == row.rowid) && equal edge (row.value edge.column) parent).length

def remove (state : Core.State) (table : Core.Table) (values : List Core.Value) : Except String Core.State := do
  let some rowid := key table.schema values | throw "FK old register rowid is missing"
  return (← Core.execute state (.deleteWhere table.schema.name
    (some (.equal table.schema.primaryKey (.integer rowid))))).1

/-- Model the real old-child, old-parent, new-child, new-parent opcode order.
OLD registers can differ from the physical row after a BEFORE DELETE body. -/
def mutation (state : Core.State) (table : Core.Table) (statement : Statement)
    (old new : Option (List Core.Value)) : Except String Core.State := do
  let edges ← CoreForeignKey.counterEdges state statement
  let childEdges := edges.filter fun edge => edge.child.toLower == table.schema.name.toLower &&
    (edge.parent.toLower == table.schema.name.toLower || modified table statement edge.column)
  let schemaOrder := fun name => ((state.catalog.current.identities.find? fun identity =>
    identity.kind == "table" && identity.name.toLower == name.toLower).map (·.rowid)).getD 0
  let parentEdges := (edges.filter fun edge => edge.parent.toLower == table.schema.name.toLower && modified table statement edge.parentColumn).mergeSort
    (fun a b => schemaOrder a.child ≥ schemaOrder b.child)
  let mut counter := state.foreignCounter
  if let some old := old then
    for edge in childEdges do
      if missing state.database edge (old[edge.column]?.getD .null) then counter := decrement counter 1
    for edge in parentEdges do
      let exclude := if edge.child.toLower == table.schema.name.toLower then key table.schema old else none
      counter := counter + parentChildren state.database edge (old[edge.parentColumn]?.getD .null) exclude
  let middle ← match old with
    | none => pure state
    | some old => remove state table old
  if let some new := new then
    for edge in childEdges do
      let value := new[edge.column]?.getD .null
      let self := edge.parent.toLower == table.schema.name.toLower && equal edge value (new[edge.parentColumn]?.getD .null)
      if !self && missing middle.database edge value then counter := counter + 1
    for edge in parentEdges do
      counter := decrement counter (parentChildren middle.database edge (new[edge.parentColumn]?.getD .null) none)
    let (inserted,_) ← Core.execute middle (.insert table.schema.name new)
    return { inserted with foreignCounter := counter }
  return { middle with foreignCounter := counter }

/-- A successful point write supplies its actual accepted row. Replay the
ordinary Core row removals, including REPLACE victims, solely to account FK
opcodes; validate the replayed target rows against the actual base result. -/
def account (before after : Core.State) (statement : Statement)
    (old new : Option (List Core.Value)) : Except String Core.State := do
  if !before.foreignKeys then return after
  let some target := CoreViewSQL.target? statement | throw "FK counter write has no target"
  let some table := CoreNames.table? before.database target | throw s!"no such table: {target}"
  let some actual := CoreNames.table? after.database target | throw "FK counter target disappeared"
  let oldKey := old.bind (key table.schema)
  let newKey := new.bind (key table.schema)
  let victims := table.rows.filter fun row =>
    !oldKey.any (· == row.rowid) &&
      (newKey.any (· == row.rowid) || (actual.findRowid? row.rowid).isNone)
  let mut current := before
  for victim in victims do
    current ← mutation current table (.delete target none none #[]) (some victim.values) none
  current ← mutation current table statement old new
  let some replayed := CoreNames.table? current.database target | throw "FK counter replay lost its target"
  unless decide (replayed.rows = actual.rows) do throw "FK counter replay disagrees with accepted target rows"
  return { after with foreignCounter := current.foreignCounter }

theorem decrement_zero (count : Nat) : decrement 0 count = 0 := rfl

theorem decrement_nonzero (counter : Int) (count : Nat) (nonzero : counter ≠ 0) :
    decrement counter count = counter - Int.ofNat count := by
  simp [decrement, nonzero]

theorem require_ok (counter : Int) (success : require counter = .ok ()) : counter = 0 := by
  unfold require at success
  split at success
  · simpa using ‹(counter == 0) = true›
  · contradiction

end SQLeanite.CoreTriggerProgram.ForeignCounter
