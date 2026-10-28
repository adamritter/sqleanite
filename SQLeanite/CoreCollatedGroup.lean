import SQLeanite.CoreEngine.ChooseExtremeEqLeftOrRight

/-! Column grouping with explicit collations. Original source rows remain
available for aggregate steps and the existing min/max representative rule. -/
namespace SQLeanite.CoreCollatedGroup

def compareKeys : List SQLite.Collation.Kind → List Core.Value → List Core.Value → Ordering
  | [], left, right => PhysicalQuery.compareValues left right
  | kind :: kinds, left :: lefts, right :: rights =>
      let order := SQLite.Collation.compareValue kind left right
      if order == .eq then compareKeys kinds lefts rights else order
  | _, left, right => PhysicalQuery.compareValues left right

def compareRows (query : Core.GroupQuery) (kinds : List SQLite.Collation.Kind)
    (left right : Core.Row) : Ordering :=
  compareKeys kinds (query.originalKey left) (query.originalKey right)

/-- Select first source representatives solely for enumerating group keys.
The final bare-column representative is chosen separately for each group. -/
def keys (query : Core.GroupQuery) (kinds : List SQLite.Collation.Kind) :
    List Core.Row → List Core.Row
  | [] => []
  | row :: rows => row :: (keys query kinds rows).filter
      (fun next => compareRows query kinds row next != .eq)

theorem keys_subset (query : Core.GroupQuery) (kinds : List SQLite.Collation.Kind)
    (rows : List Core.Row) : keys query kinds rows ⊆ rows := by
  induction rows with
  | nil => simp [keys]
  | cons row rows ih =>
      intro value member
      simp only [keys, List.mem_cons, List.mem_filter] at member
      rcases member with rfl | ⟨kept, _⟩
      · simp
      · exact List.mem_cons_of_mem row (ih kept)

def members (query : Core.GroupQuery) (kinds : List SQLite.Collation.Kind)
    (rows : List Core.Row) (key : Core.Row) : List Core.Row :=
  rows.filter (fun row => compareRows query kinds key row == .eq)

theorem members_subset (query : Core.GroupQuery) (kinds : List SQLite.Collation.Kind)
    (rows : List Core.Row) (key : Core.Row) : members query kinds rows key ⊆ rows := by
  intro row member
  exact (List.mem_filter.mp member).1

def representative (query : Core.GroupQuery) : List Core.Row → Option Core.Row
  | [] => none
  | first :: rest => some <| match query.controllingExtreme with
      | none => first
      | some (minimum, column) => Core.extremeRepresentative minimum column first rest

theorem representative_mem (query : Core.GroupQuery) (rows : List Core.Row)
    (chosen : Core.Row) (success : representative query rows = some chosen) : chosen ∈ rows := by
  cases rows with
  | nil => simp [representative] at success
  | cons first rest =>
      cases controls : query.controllingExtreme with
      | none => simp [representative, controls] at success; subst chosen; simp
      | some control =>
          rcases control with ⟨minimum, column⟩
          simp [representative, controls] at success
          subst chosen
          exact Core.extremeRepresentative_mem minimum column first rest

def outputValue (query : Core.GroupQuery) (rows : List Core.Row)
    (key : List Core.Value) : Core.GroupOutput → Except String Core.Value
  | .key position => .ok (key[position]?.getD .null)
  | .countStar => .integer <$> Core.countInteger rows.length
  | .countColumn column => .integer <$> Core.countInteger (rows.countP (fun row => row.value column != .null))
  | .sumColumn column => Core.sumColumn column rows
  | .averageColumn column => .ok (Core.averageColumn column rows)
  | .totalColumn column => .ok (Core.totalColumn column rows)
  | .minColumn column => .ok (Core.extremeColumn true column rows)
  | .maxColumn column => .ok (Core.extremeColumn false column rows)

def emit (query : Core.GroupQuery) (rows : List Core.Row) (key : List Core.Value) :
    List Core.GroupOutput → Except String (List Core.Value)
  | [] => .ok []
  | output :: outputs => do
      let value ← outputValue query rows key output
      return value :: (← emit query rows key outputs)

theorem emit_width (query : Core.GroupQuery) (rows : List Core.Row) (key : List Core.Value)
    (outputs : List Core.GroupOutput) (values : List Core.Value)
    (success : emit query rows key outputs = .ok values) : values.length = outputs.length := by
  induction outputs generalizing values with
  | nil => simp [emit] at success; subst values; rfl
  | cons output outputs ih =>
      simp only [emit] at success
      cases head : outputValue query rows key output with
      | error message => simp [head, bind, Except.bind] at success
      | ok value =>
          cases tail : emit query rows key outputs with
          | error message => simp [head, tail, bind, Except.bind] at success
          | ok rest =>
              simp [head, tail, bind, Except.bind, pure, Except.pure] at success
              subst values
              simp [ih rest tail]

def evalWindow (query : Core.GroupQuery) (kinds : List SQLite.Collation.Kind) (rows : List Core.Row)
    (offset : Nat) (limit : Option Nat) : Except String (List (List Core.Value)) := do
  if limit == some 0 then return []
  let selected := query.selectedRows rows
  let groups := (keys query kinds selected).mergeSort (fun left right => compareRows query kinds left right != .gt)
  let groups := match limit with | none => groups | some count => groups.take (offset + count)
  let output ← groups.mapM fun key => do
    let bucket := members query kinds selected key
    let chosen := (representative query bucket).getD key
    emit query bucket (query.originalKey chosen) query.outputs
  return output.drop offset

/-- OFFSET is applied after aggregate finalization; LIMIT bounds the groups
that are finalized, matching SQLite's sorter-fed aggregate loop. -/
def eval (query : Core.GroupQuery) (kinds : List SQLite.Collation.Kind) (rows : List Core.Row) :
    Except String (List (List Core.Value)) := evalWindow query kinds rows 0 none

theorem evalWindow_limit_zero (query : Core.GroupQuery) (kinds : List SQLite.Collation.Kind)
    (rows : List Core.Row) (offset : Nat) : evalWindow query kinds rows offset (some 0) = .ok [] := by
  simp [evalWindow, pure, Except.pure]

end SQLeanite.CoreCollatedGroup
