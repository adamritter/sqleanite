import SQLeanite.SQLite.CreateCatalog

namespace SQLeanite.SQLite.RenameTableCatalog

def quoted (name : String) : String :=
  "\"" ++ name.replace "\"" "\"\"" ++ "\""

/-- The admitted table definitions have no foreign-key references to rename.
Keep all original source except the table-name token, which SQLite quotes. -/
def rename (catalog newName : String) : Option String := do
  let chars := catalog.toList
  let tokens ← (CreateCatalog.spans (chars.length+1) 0 chars []).toOption
  let name ← CreateCatalog.nameSpan tokens
  let separation := if chars[name.finish]? == some '"' then " " else ""
  return String.ofList (chars.take name.start) ++ quoted newName ++ separation ++
    String.ofList (chars.drop name.finish)

end SQLeanite.SQLite.RenameTableCatalog
