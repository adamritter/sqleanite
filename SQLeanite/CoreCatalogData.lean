import SQLeanite.CoreTokenGrammar
import SQLeanite.SQLite.StoredText
import SQLeanite.SQLite.CreateCatalog

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

structure Identity where
  kind : String
  name : String
  rowid : Nat
  deriving DecidableEq, Repr

structure Objects where
  views : List View := []
  identities : List Identity := []
  schemaVersion : Nat := 0
  textEncoding : Nat := 1

def Objects.contents (objects : Objects) : List String × List Identity × Nat :=
  (objects.views.map (·.text), objects.identities, objects.schemaVersion)

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

end SQLeanite.CoreCatalogData
