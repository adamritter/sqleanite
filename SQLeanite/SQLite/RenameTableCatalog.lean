import SQLeanite.SQLite.CreateCatalog

namespace SQLeanite.SQLite.RenameTableCatalog

def quoted (name : String) : String :=
  "\"" ++ name.replace "\"" "\"\"" ++ "\""

private def identifier : Token → Option String
  | .ident name | .quotedIdent name _ | .string name => some name
  | _ => none

/-- A qualified column inside CHECK binds its qualifier to this table. -/
def checkQualifiers (oldName : String) : Nat → List CreateCatalog.Span → List Nat
  | _, [] => []
  | depth, first :: rest =>
      if depth == 0 then
        if CreateCatalog.keyword "CHECK" first && (rest.head?.map (·.token)) == some (.symbol "(") then
          checkQualifiers oldName 1 (rest.drop 1)
        else checkQualifiers oldName 0 rest
      else if first.token == .symbol "(" then checkQualifiers oldName (depth+1) rest
      else if first.token == .symbol ")" then checkQualifiers oldName (depth-1) rest
      else
        let positions := if (identifier first.token).any (fun name => name.toLower == oldName.toLower) &&
            (rest.head?.map (·.token)) == some (.symbol ".") then [first.start] else []
        positions ++ checkQualifiers oldName depth rest
termination_by _ tokens => tokens.length

private def edit (chars : List Char) (newName : String) : Nat → List CreateCatalog.Span → String
  | offset, [] => String.ofList (chars.drop offset)
  | offset, target :: rest =>
      let separation := if chars[target.finish]? == some '"' then " " else ""
      String.ofList (chars.drop offset |>.take (target.start-offset)) ++ quoted newName ++ separation ++
        edit chars newName target.finish rest

/-- Rename the table declaration and CHECK qualifiers; other spelling survives. -/
def rename (catalog newName : String) : Option String := do
  let chars := catalog.toList
  let tokens ← (CreateCatalog.spans (chars.length+1) 0 chars []).toOption
  let name ← CreateCatalog.nameSpan tokens
  let oldName ← identifier name.token
  let positions := name.start :: checkQualifiers oldName 0 tokens
  return edit chars newName 0 (tokens.filter (fun token => positions.contains token.start))

end SQLeanite.SQLite.RenameTableCatalog
