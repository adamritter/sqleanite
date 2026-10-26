import SQLeanite.CoreSchemaTranslate
import SQLeanite.CanonicalIndexSQL

/-! Metadata-only admission of foreign sqlite_schema SQL. SQLite's schema
initializer prepares the first CREATE statement and ignores its tail. No SQL
statement is executed here; the independent Core token replay must admit the
first statement before a typed table schema or index description is returned. -/
namespace SQLeanite.CoreSchemaSQL

/-- Stop at a lexical semicolon, never one inside a string, identifier or
comment. Keep original source characters so quoted text is not re-rendered. -/
def firstTail : Nat → List Char → Except String (List Char)
  | 0, _ => .error "schema tokenizer progress limit exceeded"
  | fuel + 1, input => do
      match ← lexicalStep input with
      | none => pure []
      | some step =>
          if step.emitted.contains (.symbol ";") then pure step.rest
          else firstTail fuel step.rest

theorem firstTail_semicolon (fuel : Nat) (input : List Char) (step : LexStep)
    (scanned : lexicalStep input = .ok (some step))
    (terminal : step.emitted.contains (.symbol ";") = true) :
    firstTail (fuel + 1) input = .ok step.rest := by
  simp [firstTail, scanned, terminal, bind, Except.bind, pure, Except.pure]

/-- prepare.c requires the untrimmed catalog SQL to begin with CR. -/
def firstStatement (sql : String) : Option String := do
  if !(sql.toLower.startsWith "cr") then none else do
    let input := sql.toList
    let rest ← (firstTail (input.length + 1) input).toOption
    some (String.ofList (input.take (input.length - rest.length)))

def statements (sql : String) : Option (Array Statement) := do
  let first ← firstStatement sql
  let parsed ← (CoreTokenGrammar.parseCertified first).toOption
  some parsed.statements

def tableSchema (sql : String) : Option Core.Schema := do
  let parsed ← statements sql
  match parsed.toList with
  | [.createTable name columns constraints _] =>
      (CoreSQL.schema name columns constraints).toOption
  | _ => none

def indexSpec (sql : String) : Option CanonicalIndexSQL.Spec := do
  let parsed ← statements sql
  match parsed.toList with
  | [.createIndex name table expressions unique where_ _] => do
      if where_.isSome then none else do
        match expressions.toList with
        | [expression] => do
            let column ← CoreSQL.indexColumnName? expression
            some ⟨name, table, column, unique⟩
        | _ => none
  | _ => none

end SQLeanite.CoreSchemaSQL
