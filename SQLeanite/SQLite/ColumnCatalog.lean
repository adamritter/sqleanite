import SQLeanite.SQLite.AlterCatalog
import SQLeanite.SQLite.RenameTableCatalog

namespace SQLeanite.SQLite.ColumnCatalog
open CreateCatalog

/-- Column-name token and the preceding comma (or opening parenthesis).
Nested type/default expressions never become column boundaries. -/
def columns : Nat → Bool → Nat → List Span → List (Span × Nat)
  | _, _, _, [] => []
  | depth, beginning, separator, first :: rest =>
      if first.token == .symbol "(" then
        columns (depth+1) (depth == 0) (if depth == 0 then first.finish else separator) rest
      else if first.token == .symbol ")" then
        if depth == 1 then [] else columns (depth-1) false separator rest
      else if depth == 1 && first.token == .symbol "," then
        columns depth true first.start rest
      else if depth == 1 && beginning then
        if AlterCatalog.tableConstraint first then []
        else (first, separator) :: columns depth false separator rest
      else columns depth beginning separator rest

def dropColumn (catalog : String) (position : Nat) : Option String := do
  let chars := catalog.toList
  let tokens ← (spans (chars.length+1) 0 chars []).toOption
  let starts := columns 0 false 0 tokens
  let (target, separator) ← starts[position]?
  let (start, finish) ← match starts[position+1]? with
    | some (next, _) => pure (target.start, next.start)
    | none => do
        if position == 0 then none else pure ()
        let finish ← AlterCatalog.addOffset 0 tokens
        pure (separator, finish)
  return String.ofList (chars.take start ++ chars.drop finish)

def identifier : Token → Option String
  | .ident name | .quotedIdent name _ | .string name => some name
  | _ => none

/-- Only a single-column table-level PRIMARY KEY can refer to a column in
currently admitted table definitions. Constraint names, type names, defaults
and comments must retain their spelling even if equal to the old name. -/
def primaryReferences (oldName : String) : List Span → List Nat
  | [] => []
  | first :: rest =>
      let here := match rest with
        | key :: opening :: target :: _ =>
            if keyword "PRIMARY" first && keyword "KEY" key && opening.token == .symbol "(" &&
                (identifier target.token).any (fun name => name.toLower == oldName.toLower) then
              [target.start] else []
        | _ => []
      here ++ primaryReferences oldName rest

/-- CHECK expression identifiers refer to this table. Strings, function names,
qualifiers, COLLATE names and CAST type spans are not column references. -/
def checkReferences (oldName : String) : Nat → Option Nat → Bool → List Span → List Nat
  | _, _, _, [] => []
  | depth, castType, collation, first :: rest =>
      if depth == 0 then
        if keyword "CHECK" first && (rest.head?.map (·.token)) == some (.symbol "(") then
          checkReferences oldName 1 none false (rest.drop 1)
        else checkReferences oldName 0 none false rest
      else if first.token == .symbol "(" then
        checkReferences oldName (depth+1) castType false rest
      else if first.token == .symbol ")" then
        checkReferences oldName (depth-1) (if castType == some depth then none else castType) false rest
      else if castType.isSome then checkReferences oldName depth castType false rest
      else if keyword "AS" first then checkReferences oldName depth (some depth) false rest
      else
        let candidate := match first.token with
          | .quotedIdent name _ => name.toLower == oldName.toLower
          | .ident name => name.toLower == oldName.toLower &&
              !["case","when","then","else","end","and","or","not","is","null","in",
                "between","like","glob","match","escape","collate","as"].contains name.toLower
          | _ => false
        let following := rest.head?.map (·.token)
        let positions := if candidate && !collation && following != some (.symbol "(") &&
            following != some (.symbol ".") then [first.start] else []
        positions ++ checkReferences oldName depth none (keyword "COLLATE" first) rest
termination_by _ _ _ tokens => tokens.length

def uniqueReferences (oldName : String) : List Span → List Nat
  | [] => []
  | first :: rest =>
      let positions := match rest with
        | opening :: target :: _ =>
            if keyword "UNIQUE" first && opening.token == .symbol "(" &&
                (identifier target.token).any (fun name => name.toLower == oldName.toLower) then
              [target.start] else []
        | _ => []
      positions ++ uniqueReferences oldName rest

/-- Table FOREIGN KEY child lists bind local column names. Parent targets
are rewritten separately by the connection's foreign-key rename operation. -/
def foreignChildReferences (oldName : String) : Nat → List Span → List Nat
  | _, [] => []
  | depth, first :: rest =>
      if first.token == .symbol "(" then foreignChildReferences oldName (depth + 1) rest
      else if first.token == .symbol ")" then foreignChildReferences oldName (depth - 1) rest
      else
        let positions := match rest with
          | key :: opening :: target :: _ =>
              if depth == 1 && keyword "FOREIGN" first && keyword "KEY" key &&
                  opening.token == .symbol "(" &&
                  (identifier target.token).any (fun name => name.toLower == oldName.toLower) then
                [target.start] else []
          | _ => []
        positions ++ foreignChildReferences oldName depth rest

def edit (chars : List Char) (newName : String) (forceQuote : Bool) : Nat → List Span → String
  | offset, [] => String.ofList (chars.drop offset)
  | offset, target :: rest =>
      let useQuote := forceQuote || (match target.token with | .ident _ => false | _ => true)
      let replacement := if useQuote then RenameTableCatalog.quoted newName else newName
      let separation := if useQuote && chars[target.finish]? == some '"' then " " else ""
      String.ofList (chars.drop offset |>.take (target.start-offset)) ++ replacement ++ separation ++
        edit chars newName forceQuote target.finish rest

def renameColumn (catalog source oldName newName : String) (position : Nat) : Option String := do
  let chars := catalog.toList
  let tokens ← (spans (chars.length+1) 0 chars []).toOption
  let (target, _) ← (columns 0 false 0 tokens)[position]?
  let input := source.toList
  let inputTokens ← (spans (input.length+1) 0 input []).toOption
  let newToken ← (inputTokens.takeWhile (fun span => span.token != .symbol ";")).getLast?
  let forceQuote := match newToken.token with | .ident _ => false | _ => true
  let positions := target.start :: (primaryReferences oldName tokens ++ uniqueReferences oldName tokens ++
    checkReferences oldName 0 none false tokens ++ foreignChildReferences oldName 0 tokens)
  return edit chars newName forceQuote 0 (tokens.filter (fun span => positions.contains span.start))

end SQLeanite.SQLite.ColumnCatalog
