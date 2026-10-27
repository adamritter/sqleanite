import SQLeanite.SQLite.ColumnCatalog

/-! Lexical REFERENCES targets in admitted CREATE TABLE source. Parent names
and explicit parent-column names bind outside CHECK/default expressions. -/
namespace SQLeanite.SQLite.ForeignKeyCatalog
open CreateCatalog

def targets (parent : String) (column : Option String) : Nat → List Span → List Nat
  | _, [] => []
  | depth, first :: rest =>
      if first.token == .symbol "(" then targets parent column (depth + 1) rest
      else if first.token == .symbol ")" then targets parent column (depth - 1) rest
      else
        let positions := if depth == 1 && keyword "REFERENCES" first then
          match rest with
          | referenced :: tail =>
              if (ColumnCatalog.identifier referenced.token).any (fun name => name.toLower == parent.toLower) then
                match column with
                | none => [referenced.start]
                | some oldName => match tail with
                    | opening :: target :: _ =>
                        if opening.token == .symbol "(" &&
                            (ColumnCatalog.identifier target.token).any (fun name => name.toLower == oldName.toLower) then
                          [target.start] else []
                    | _ => []
              else []
          | _ => []
        else []
        positions ++ targets parent column depth rest

def rewrite (catalog parent : String) (column : Option String) (newName : String)
    (forceQuote : Bool) : Option String := do
  let chars := catalog.toList
  let tokens ← (spans (chars.length + 1) 0 chars []).toOption
  let positions := targets parent column 0 tokens
  if positions.isEmpty then return catalog
  return ColumnCatalog.edit chars newName forceQuote 0 (tokens.filter (fun span => positions.contains span.start))

theorem rewrite_no_targets (catalog parent : String) (column : Option String)
    (newName : String) (forceQuote : Bool) (tokens : List Span)
    (tokenized : (spans (catalog.toList.length + 1) 0 catalog.toList []).toOption = some tokens)
    (absent : targets parent column 0 tokens = []) :
    rewrite catalog parent column newName forceQuote = some catalog := by
  simp [rewrite, tokenized, absent]

end SQLeanite.SQLite.ForeignKeyCatalog
