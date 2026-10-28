import SQLeanite.CoreTokenGrammar.MatchInsertPrefix
import SQLeanite.SQLite.CreateCatalog
import SQLeanite.SQLite.StoredText

/-! Source-aware schema objects and their catalog identities. Ordinary Core
row tables remain the independently proved database model; these declarations
carry their own concrete-grammar certificate and transaction snapshots. -/
namespace SQLeanite.CoreCatalogData

structure ViewDefinition where
  name : String
  columns : Option (Array String)
  query : Select

/-- Persistent view source is ordinary CREATE VIEW text. Name binding and
result-width checks are deferred until the view is prepared for use. -/
def parseView (text : String) : Option ViewDefinition := do
  let parsed ← (CoreTokenGrammar.parseCertified text).toOption
  match parsed.statements.toList with
  | [.createView name columns query _ false _] => some { name, columns, query }
  | _ => none

structure View where
  text : String
  definition : ViewDefinition
  decoded : parseView text = some definition

def view (text : String) : Except String View :=
  match decoded : parseView text with
  | none => .error "invalid persistent view declaration"
  | some definition => .ok { text, definition, decoded }

theorem view_decoded (text : String) (source : View) (success : view text = .ok source) :
    parseView text = some source.definition := by
  unfold view at success
  split at success <;> try contradiction
  cases success
  assumption

theorem View.definition_of_text_eq (left right : View) (same : left.text = right.text) :
    left.definition = right.definition := by
  apply Option.some.inj
  rw [← left.decoded, ← right.decoded, same]

structure TriggerDefinition where
  name : String
  table : String
  event : TriggerEvent
  timing : TriggerTiming
  when_ : Option Expr
  body : Array Statement

def parseTrigger (text : String) : Option TriggerDefinition := do
  let parsed ← (CoreTokenGrammar.parseCertified text).toOption
  match parsed.statements.toList with
  | [.createTrigger name table event timing when_ body _ false _ _] =>
      some { name, table, event, timing, when_, body }
  | _ => none

structure Trigger where
  text : String
  definition : TriggerDefinition
  decoded : parseTrigger text = some definition
  owner : String
  ownerMatches : owner.toLower = definition.table.toLower

def trigger (text : String) : Except String Trigger :=
  match decoded : parseTrigger text with
  | none => .error "invalid persistent trigger declaration"
  | some definition => .ok { text, definition, decoded, owner := definition.table, ownerMatches := rfl }

def triggerAtOwner (text owner : String) : Except String Trigger := do
  let source ← trigger text
  if same : owner.toLower = source.definition.table.toLower then
    return { source with owner, ownerMatches := same }
  else throw "trigger source owner mismatch"

theorem triggerAtOwner_owner (text owner : String) (source : Trigger)
    (success : triggerAtOwner text owner = .ok source) : source.owner = owner := by
  unfold triggerAtOwner at success
  cases compiled : trigger text with
  | error message => simp [compiled, bind, Except.bind] at success
  | ok initialized =>
      simp only [compiled, bind, Except.bind] at success
      split at success
      · simp only [pure, Except.pure] at success
        cases success
        rfl
      · contradiction

theorem trigger_decoded (text : String) (source : Trigger) (success : trigger text = .ok source) :
    parseTrigger text = some source.definition := by
  unfold trigger at success
  split at success <;> try contradiction
  cases success
  assumption

theorem Trigger.definition_of_text_eq (left right : Trigger) (same : left.text = right.text) :
    left.definition = right.definition := by
  apply Option.some.inj
  rw [← left.decoded, ← right.decoded, same]

structure FilteredIndexDefinition where
  name : String
  table : String
  key : Expr
  column : Option String
  predicate : Expr
  partialIndex : Bool
  unique : Bool

def indexColumnName? : Expr → Option String
  | .column none name => some name
  | .call "lean_dqs" #[.literal (.text name) _] false => some name
  | _ => none

def auxiliaryIndex (expressions : Array Expr) (predicate : Option Expr) : Bool :=
  predicate.isSome || match expressions.toList with
    | [key] => (indexColumnName? key).isNone
    | _ => true

def parseFilteredIndex (text : String) : Option FilteredIndexDefinition := do
  let parsed ← (CoreTokenGrammar.parseCertified text).toOption
  match parsed.statements.toList with
  | [.createIndex name table expressions unique predicate _] =>
      unless auxiliaryIndex expressions predicate do none
      let [key] := expressions.toList | none
      let column := indexColumnName? key
      some {
        name, table, key, column
        predicate := predicate.getD (.literal (.integer 1) none)
        partialIndex := predicate.isSome
        unique }
  | _ => none

/-- A filtered physical index has its own source certificate. It is not an
ordinary full-column index in the independently checked Core table model. -/
structure FilteredIndex where
  text : String
  definition : FilteredIndexDefinition
  decoded : parseFilteredIndex text = some definition
  owner : String
  ownerMatches : owner.toLower = definition.table.toLower

def filteredIndexAtOwner (text owner : String) : Except String FilteredIndex := do
  match decoded : parseFilteredIndex text with
  | none => throw "unsupported partial index declaration"
  | some definition =>
      if same : owner.toLower = definition.table.toLower then
        return { text, definition, decoded, owner, ownerMatches := same }
      else throw "partial index source owner mismatch"

theorem FilteredIndex.definition_of_text_eq (left right : FilteredIndex)
    (same : left.text = right.text) : left.definition = right.definition := by
  apply Option.some.inj
  rw [← left.decoded, ← right.decoded, same]

structure Identity where
  kind : String
  name : String
  rowid : Nat
  deriving DecidableEq, Repr

structure Objects where
  views : List View := []
  triggers : List Trigger := []
  filteredIndexes : List FilteredIndex := []
  identities : List Identity := []
  schemaVersion : Nat := 0
  textEncoding : Nat := 1

def Objects.contents (objects : Objects) :
    ((List String × List (String × String)) × List Identity × Nat) × List (String × String) :=
  (((objects.views.map (·.text), objects.triggers.map (fun trigger => (trigger.text,trigger.owner))),
    objects.identities, objects.schemaVersion), objects.filteredIndexes.map (fun index => (index.text,index.owner)))

structure State where
  storedTexts : List SQLite.StoredText := []
  current : Objects := {}
  durable : Objects := {}
  loaded : Bool := false
  transactionSnapshot : Option Objects := none
  savepoints : List (String × Objects) := []

def State.changed (state : State) : Bool := state.current.contents != state.durable.contents

def State.acknowledge (state : State) : State := { state with durable := state.current }

theorem State.acknowledge_unchanged (state : State) : state.acknowledge.changed = false := by
  simp [acknowledge, changed]

/-- SQLite keeps the original view name token and body after removing the
CREATE modifiers. Token spans preserve quoted identifiers and source trivia. -/
def normalizeView (sql : String) : Option String := do
  let chars := sql.toList
  let tokens ← (SQLite.CreateCatalog.spans (chars.length + 1) 0 chars []).toOption
  let rest ← SQLite.CreateCatalog.afterKeyword "CREATE" tokens
  let rest := match rest with
    | first :: tail => if SQLite.CreateCatalog.keyword "TEMP" first ||
        SQLite.CreateCatalog.keyword "TEMPORARY" first then tail else rest
    | [] => []
  let rest ← SQLite.CreateCatalog.afterKeyword "VIEW" rest
  let rest ← match SQLite.CreateCatalog.afterKeyword "IF" rest with
    | none => some rest
    | some rest => SQLite.CreateCatalog.afterKeyword "NOT" rest >>= SQLite.CreateCatalog.afterKeyword "EXISTS"
  let name ← rest.head?
  let terminator := tokens.find? (fun span => span.token == .symbol ";")
  let finish := terminator.map (·.start) |>.getD chars.length
  return "CREATE VIEW " ++ String.ofList (chars.drop name.start |>.take (finish - name.start))

/-- Keep the actual declared-name token through the final END token, removing
only CREATE modifiers and an optional main namespace from the header. -/
def normalizeTrigger (sql : String) : Option String := do
  let chars := sql.toList
  let tokens ← (SQLite.CreateCatalog.spans (chars.length+1) 0 chars []).toOption
  let rest ← SQLite.CreateCatalog.afterKeyword "CREATE" tokens
  let rest := match rest with
    | first :: tail => if SQLite.CreateCatalog.keyword "TEMP" first || SQLite.CreateCatalog.keyword "TEMPORARY" first then tail else rest
    | [] => []
  let rest ← SQLite.CreateCatalog.afterKeyword "TRIGGER" rest
  let rest ← match SQLite.CreateCatalog.afterKeyword "IF" rest with
    | none => some rest
    | some rest => SQLite.CreateCatalog.afterKeyword "NOT" rest >>= SQLite.CreateCatalog.afterKeyword "EXISTS"
  let name ← match rest with
    | _ :: dot :: name :: _ => if dot.token == .symbol "." then some name else rest.head?
    | _ => rest.head?
  let ending ← tokens.reverse.find? (SQLite.CreateCatalog.keyword "END")
  return "CREATE TRIGGER " ++ String.ofList (chars.drop name.start |>.take (ending.finish-name.start))

end SQLeanite.CoreCatalogData
