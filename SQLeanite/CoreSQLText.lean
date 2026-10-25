import SQLeanite.CoreSQLGrammar

namespace SQLeanite
namespace CoreSQL

/-!
# Text-to-Core boundary

`CoreStatementForm` is the top-level grammar admitted by the verified Core.
The expression-level subgrammars live in `CoreSQLGrammar`.  `ParsedSupportedText`
keeps the parser equation explicit instead of defining support to mean that
execution happened to succeed; this distinction is needed by the later parser
correctness theorem.
-/

inductive CoreStatementForm : Statement → Prop where
  | insertSelect (table columns query conflict) : CoreStatementForm (.insertSelect table columns query conflict)
  | dropTable (name ifExists) : CoreStatementForm (.dropTable name ifExists)
  | dropIndex (name ifExists) : CoreStatementForm (.dropIndex name ifExists)
  | createTable (name columns constraints ifNotExists) :
      CoreStatementForm (.createTable name columns constraints ifNotExists)
  | createIndex (name table expressions unique where_ ifNotExists) :
      CoreStatementForm
        (.createIndex name table expressions unique where_ ifNotExists)
  | insert (table columns rows conflict) :
      CoreStatementForm (.insert table columns rows conflict)
  | delete (table alias where_ returning) :
      CoreStatementForm (.delete table alias where_ returning)
  | update (table alias assignments where_ conflict) :
      CoreStatementForm (.update table alias assignments where_ conflict)
  | select (query) : CoreStatementForm (.select query)
  | begin : CoreStatementForm .begin
  | commit : CoreStatementForm .commit
  | rollback : CoreStatementForm .rollback

def CoreStatementListForm (statements : List Statement) : Prop :=
  ∀ statement ∈ statements, CoreStatementForm statement

theorem statementForm_of_execute_success {state next : Core.State}
    {statement : Statement} {results : List Core.Result}
    (success : executeStatement state statement = .ok (next, results)) :
    CoreStatementForm statement := by
  cases statement with
  | insertSelect table columns query conflict => exact .insertSelect ..
  | dropTable name ifExists => exact .dropTable ..
  | dropIndex name ifExists => exact .dropIndex ..
  | createTable name columns constraints ifNotExists => exact .createTable ..
  | createIndex name table expressions unique where_ ifNotExists =>
      exact .createIndex ..
  | insert table columns rows conflict => exact .insert ..
  | delete table alias where_ returning => exact .delete ..
  | update table alias assignments where_ conflict => exact .update ..
  | select query => exact .select query
  | begin => exact .begin
  | commit => exact .commit
  | rollback => exact .rollback
  | createTableAs | createView | dropView |
      createTrigger | dropTrigger | alterAddColumn | alterRenameColumn |
      withRecursive | withCte | values | reindex | pragma =>
      simp [executeStatement, unsupported] at success

theorem statementListForm_of_run_success (state : Core.State) :
    ∀ {statements : List Statement} {next : Core.State}
      {results : List Core.Result},
      runStatements state statements = .ok (next, results) →
      CoreStatementListForm statements
  | [], _, _, _ => by simp [CoreStatementListForm]
  | statement :: statements, next, results, success => by
      unfold runStatements at success
      cases head : executeStatement state statement with
      | error message => simp [head] at success
      | ok outcome =>
          rcases outcome with ⟨middle, headResults⟩
          cases tail : runStatements middle statements with
          | error message => simp [head, tail] at success
          | ok outcome =>
              intro candidate member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact statementForm_of_execute_success head
              · exact statementListForm_of_run_success middle tail candidate member

/-- A proof-producing parse whose AST lies in the Core top-level grammar.  The
certificate contains both the character-to-token trace and the independent
token-to-AST replay used by the live executor. -/
def ParsedSupportedText (text : String) (statements : Array Statement) : Prop :=
  ∃ certificate : CoreTokenGrammar.CertifiedParse text,
    CoreTokenGrammar.parseCertified text = .ok certificate ∧
    certificate.statements = statements ∧
    CoreStatementListForm statements.toList

/-- Supported Core text carries an independently checkable character-to-token
trace, not merely the final parser equation. -/
theorem ParsedSupportedText.tokenizes {text : String}
    {statements : Array Statement}
    (supported : ParsedSupportedText text statements) :
    ∃ tokens : Array Token,
      lex text = .ok tokens ∧ Tokenizes text.toList tokens.toList :=
  by
    rcases supported with ⟨certificate, _, rfl, _⟩
    exact ⟨certificate.tokens, certificate.lexes, certificate.tokenizes⟩

theorem ParsedSupportedText.grammar {text : String}
    {statements : Array Statement}
    (supported : ParsedSupportedText text statements) :
    ∃ tokens : Array Token,
      Tokenizes text.toList tokens.toList ∧
      CoreTokenGrammar.Matches tokens statements := by
  rcases supported with ⟨certificate, _, rfl, _⟩
  exact ⟨certificate.tokens, certificate.tokenizes, certificate.grammar⟩

theorem execute_eq_runStatements_of_parsed {state : Core.State} {text : String}
    {statements : Array Statement}
    (supported : ParsedSupportedText text statements) :
    execute state text = runStatements state statements.toList := by
  rcases supported with ⟨certificate, parsed, rfl, _⟩
  simp [execute, parsed, bind, Functor.map, Except.bind]

/-- Every text accepted all the way through the live Core has a parser witness
and contains no legacy-only top-level statement. -/
theorem parsedSupportedText_of_execute_success {state next : Core.State}
    {text : String} {results : List Core.Result}
    (success : execute state text = .ok (next, results)) :
    ∃ statements, ParsedSupportedText text statements := by
  cases parsed : CoreTokenGrammar.parseCertified text with
  | error message =>
      simp [execute, parsed, bind, Functor.map, Except.bind] at success
  | ok certificate =>
      refine ⟨certificate.statements, certificate, parsed, rfl, ?_⟩
      exact statementListForm_of_run_success state
        (by simpa [execute, parsed, bind, Functor.map, Except.bind] using success)

theorem parsedSupportedText_execute_exact {state next : Core.State}
    {text : String} {statements : Array Statement}
    {results : List Core.Result}
    (supported : ParsedSupportedText text statements)
    (success : runStatements state statements.toList =
      .ok (next, results)) :
    execute state text = .ok (next, results) := by
  rw [execute_eq_runStatements_of_parsed supported]
  exact success

end CoreSQL
end SQLeanite
