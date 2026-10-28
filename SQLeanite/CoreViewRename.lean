import SQLeanite.CoreForeignKeyRename
import SQLeanite.CoreViewSQL

/-! Schema renames edit independently replayed identifier roles. Offsets come
from actual lexical steps, retaining all untouched SQL, comments and literals.
Each resulting view source is independently certified again before use. -/
namespace SQLeanite.CoreViewRename

abbrev Request := CoreForeignKeyRename.Request

structure Edit where
  start : Nat
  finish : Nat
  replacement : String

def targetSource (change : Request) (source : TableRef) : Bool :=
  source.subquerySql.isNone && source.functionArgs.isNone &&
    (CoreViewSQL.sourceName? source).any (fun name => name.toLower == change.parent.toLower)

def sourceContexts (state : Core.State) (query : Select) : List (TableRef × CoreExpr.Context) :=
  query.sources.toList.filterMap fun source => do
    unless source.subquerySql.isNone && source.functionArgs.isNone do none
    let name ← CoreViewSQL.sourceName? source
    let table ← CoreNames.table? state.database name
    return (source, { schema := table.schema, sourceName := source.alias.getD name })

/-- A local declaration shadows an outer field. Only a uniquely resolved
reference to the renamed physical table can change a column token. -/
def columnTarget : List Select → Core.State → Request → Option String → String → Bool
  | [], _, _, _, _ => false
  | query :: parents, state, change, qualifier, name =>
      let contexts := sourceContexts state query
      let candidates := CoreJoinUsing.nameCandidates (contexts.map Prod.snd) qualifier name
      match candidates with
      | [] => columnTarget parents state change qualifier name
      | [(sourceIndex,_)] => (contexts[sourceIndex]?).any (fun (source,_) => targetSource change source)
      | _ => false

def qualifierTarget : List Select → Request → String → Bool
  | [], _, _ => false
  | query :: parents, change, qualifier =>
      let sources := query.sources.toList.filter fun source =>
        (source.alias.getD ((CoreViewSQL.sourceName? source).getD source.name)).toLower == qualifier.toLower
      match sources with
      | [] => qualifierTarget parents change qualifier
      | [source] => source.alias.isNone && targetSource change source
      | _ => false

def referenceTarget (state : Core.State) (change : Request) (parents : List Select)
    (reference : CoreTokenGrammar.Reference) : Bool :=
  let scopes := reference.query.toList ++ parents
  match reference.kind, change.column with
  | .table source, none => targetSource change source
  | .qualifier name, none => qualifierTarget scopes change name
  | .column qualifier name, some oldName =>
      name.toLower == oldName.toLower &&
        !(reference.outputAliases && qualifier.isNone && reference.query.any (fun query =>
          query.columns.any (fun col => col.alias.any (fun alias => alias.toLower == name.toLower)))) &&
        columnTarget scopes state change qualifier name
  | _, _ => false

def applyEdits (chars : List Char) : Nat → List Edit → String
  | offset, [] => String.ofList (chars.drop offset)
  | offset, edit :: edits =>
      String.ofList (chars.drop offset |>.take (edit.start - offset)) ++ edit.replacement ++
        applyEdits chars edit.finish edits

def rewrite : Nat → Core.State → Request → List Select → String → Except String String
  | 0, _, _, _, _ => .error "view rename nesting limit exceeded"
  | fuel + 1, state, change, parents, text => do
      let parsed ← CoreTokenGrammar.parseCertified text
      let references ← CoreTokenGrammar.references parsed.tokens parsed.statements
      let chars := text.toList
      let spans ← SQLite.CreateCatalog.spans (chars.length + 1) 0 chars []
      let mut edits : List Edit := []
      for reference in references do
        let position := parsed.tokens.size - reference.tailLength - 1
        let ordinal := (CoreTokenGrammar.significant (parsed.tokens.toList.take position)).length
        let some span := spans[ordinal]? | throw "invalid traced view token offset"
        match reference.kind with
        | .captured sql correlated =>
            let tokens ← lex sql
            let count := (CoreTokenGrammar.significant tokens.toList).filter (· != .eof) |>.length
            let some last := spans[ordinal + count - 1]? | throw "invalid traced captured query extent"
            let original := String.ofList (chars.drop span.start |>.take (last.finish - span.start))
            let scopes := if correlated then reference.query.toList ++ parents else []
            let replacement ← rewrite fuel state change scopes original
            if replacement != original then edits := edits ++ [{ start := span.start, finish := last.finish, replacement }]
        | _ =>
            if referenceTarget state change parents reference then
              let quoted := change.forceQuote || (match span.token with | .ident _ => false | _ => true)
              let replacement := if quoted then SQLite.RenameTableCatalog.quoted change.newName else change.newName
              edits := edits ++ [{ start := span.start, finish := span.finish, replacement }]
      let orderedEdits := edits.mergeSort (fun left right => left.start ≤ right.start)
      unless orderedEdits.Pairwise (fun left right => left.finish ≤ right.start) do
        throw "overlapping view rename token offsets"
      return applyEdits chars 0 orderedEdits

def execute (before after : Core.State) (statement : Statement) (source : String) : Except String Core.State := do
  let some change := CoreForeignKeyRename.request before statement source | return after
  let views ← after.catalog.current.views.mapM fun view => do
    let text ← rewrite 256 before change [] view.text
    let compiled ← CoreCatalogData.view text
    unless compiled.definition.name == view.definition.name && compiled.definition.columns == view.definition.columns do
      throw "view rename changed its declared identity"
    return compiled
  return { after with catalog := { after.catalog with current := { after.catalog.current with views } } }

theorem execute_unrelated (before after : Core.State) (statement : Statement) (source : String)
    (unchanged : CoreForeignKeyRename.request before statement source = none) :
    execute before after statement source = .ok after := by
  simp [execute, unchanged, pure, Except.pure]

end SQLeanite.CoreViewRename
