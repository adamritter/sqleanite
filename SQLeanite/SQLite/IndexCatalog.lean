import SQLeanite.CoreSQL
import SQLeanite.SQLite.CreateCatalog

/-! Source metadata for WAL index creation. This ledger follows successful
transaction statements; it never changes logical rows or index definitions.
The adapter reparses retained text against current metadata before encoding. -/
namespace SQLeanite.SQLite.IndexCatalog

open CreateCatalog

def normalize (sql : String) : Option String := do
  let chars := sql.toList
  let tokens ← (spans (chars.length + 1) 0 chars []).toOption
  let terminator := tokens.find? (fun span => span.token == .symbol ";")
  let tokens := tokens.takeWhile (fun span => span.token != .symbol ";")
  let rest ← afterKeyword "CREATE" tokens
  let unique := rest.head?.any (keyword "UNIQUE")
  let rest := if unique then rest.drop 1 else rest
  let rest ← afterKeyword "INDEX" rest
  let rest ← match afterKeyword "IF" rest with
    | none => some rest
    | some rest => afterKeyword "NOT" rest >>= afterKeyword "EXISTS"
  let name ← match rest with
    | first :: dot :: name :: _ =>
        if dot.token == .symbol "." then some name else some first
    | _ => rest.head?
  let finish := (terminator.map (·.start)).getD chars.length
  return (if unique then "CREATE UNIQUE INDEX " else "CREATE INDEX ") ++
    String.ofList (chars.drop name.start |>.take (finish - name.start))

structure Source where
  name : String
  table : String
  sql : String
  deriving DecidableEq, Repr

structure Mark where
  name : String
  sources : List Source
  deriving DecidableEq, Repr

structure State where
  sources : List Source := []
  transaction : Option (List Source) := none
  marks : List Mark := []
  deriving DecidableEq, Repr

def State.begin (state : State) : State :=
  { state with transaction := some state.sources }

def State.commit (state : State) : State :=
  { state with transaction := none, marks := [] }

def State.rollback (state : State) : State :=
  { sources := state.transaction.getD state.sources }

def State.savepoint (state : State) (name : String) : State :=
  { state with
    transaction := some (state.transaction.getD state.sources)
    marks := ⟨name, state.sources⟩ :: state.marks }

def remaining (name : String) (marks : List Mark) : List Mark :=
  marks.dropWhile (fun mark => mark.name.toLower != name.toLower)

def State.rollbackTo (state : State) (name : String) : State :=
  match remaining name state.marks with
  | [] => state
  | mark :: older => { state with sources := mark.sources, marks := mark :: older }

def State.release (state : State) (name : String) (stillInTransaction : Bool) : State :=
  { state with
    transaction := if stillInTransaction then state.transaction else none
    marks := (remaining name state.marks).drop 1 }

theorem rollback_restores (state : State) (saved : List Source)
    (snapshot : state.transaction = some saved) : state.rollback.sources = saved := by
  simp [State.rollback, snapshot]

theorem rollbackTo_savepoint (state : State) (name : String) :
    (state.savepoint name).rollbackTo name = state.savepoint name := by
  simp [State.rollbackTo, State.savepoint, remaining]

theorem commit_preserves_sources (state : State) : state.commit.sources = state.sources := rfl

/-- Called only after the corresponding Core statement succeeds. Failed and
IF NOT EXISTS no-op creation cannot replace the prior definition. -/
def track (ledger : State) (before after : Core.State) (statement : Statement)
    (source : String) : Except String State := do
  match statement with
  | .createIndex name table _ _ _ _ =>
      if CoreSQL.schemaNoop before statement then return ledger
      let some sql := normalize source | throw "cannot retain CREATE INDEX source"
      return { ledger with sources := {
        name, table := CoreSQL.resolveTableName before table, sql } :: ledger.sources }
  | .begin => return ledger.begin
  | .commit => return ledger.commit
  | .rollback => return ledger.rollback
  | .savepoint name => return ledger.savepoint name
  | .rollbackTo name => return ledger.rollbackTo name
  | .release name => return ledger.release name after.transactionSnapshot.isSome
  | _ => return ledger

end SQLeanite.SQLite.IndexCatalog
