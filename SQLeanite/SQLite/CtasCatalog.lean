import SQLeanite.CoreData

namespace SQLeanite.SQLite.CtasCatalog

def keywords : List String := ["ABORT", "ACTION", "ADD", "AFTER", "ALL", "ALTER", "ALWAYS", "ANALYZE", "AND", "AS", "ASC", "ATTACH", "AUTOINCREMENT", "BEFORE", "BEGIN", "BETWEEN", "BY", "CASCADE", "CASE", "CAST", "CHECK", "COLLATE", "COLUMN", "COMMIT", "CONFLICT", "CONSTRAINT", "CREATE", "CROSS", "CURRENT", "CURRENT_DATE", "CURRENT_TIME", "CURRENT_TIMESTAMP", "DATABASE", "DEFAULT", "DEFERRED", "DEFERRABLE", "DELETE", "DESC", "DETACH", "DISTINCT", "DO", "DROP", "END", "EACH", "ELSE", "ESCAPE", "EXCEPT", "EXCLUSIVE", "EXCLUDE", "EXISTS", "EXPLAIN", "FAIL", "FILTER", "FIRST", "FOLLOWING", "FOR", "FOREIGN", "FROM", "FULL", "GENERATED", "GLOB", "GROUP", "GROUPS", "HAVING", "IF", "IGNORE", "IMMEDIATE", "IN", "INDEX", "INDEXED", "INITIALLY", "INNER", "INSERT", "INSTEAD", "INTERSECT", "INTO", "IS", "ISNULL", "JOIN", "KEY", "LAST", "LEFT", "LIKE", "LIMIT", "MATCH", "MATERIALIZED", "NATURAL", "NO", "NOT", "NOTHING", "NOTNULL", "NULL", "NULLS", "OF", "OFFSET", "ON", "OR", "ORDER", "OTHERS", "OUTER", "OVER", "PARTITION", "PLAN", "PRAGMA", "PRECEDING", "PRIMARY", "QUERY", "RAISE", "RANGE", "RECURSIVE", "REFERENCES", "REGEXP", "REINDEX", "RELEASE", "RENAME", "REPLACE", "RESTRICT", "RETURNING", "RIGHT", "ROLLBACK", "ROW", "ROWS", "SAVEPOINT", "SELECT", "SET", "TABLE", "TEMP", "TEMPORARY", "THEN", "TIES", "TO", "TRANSACTION", "TRIGGER", "UNBOUNDED", "UNION", "UNIQUE", "UPDATE", "USING", "VACUUM", "VALUES", "VIEW", "VIRTUAL", "WHEN", "WHERE", "WINDOW", "WITH", "WITHOUT"]

def identLength (name : String) : Nat :=
  name.utf8ByteSize + (name.toList.filter (· == '"')).length + 2

def ident (name : String) : String :=
  let plain := !name.isEmpty &&
    name.toList.all (fun c => ('a' ≤ c && c ≤ 'z') ||
      ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_') &&
    !(name.toList.head?.any Char.isDigit) && !keywords.contains name.toUpper
  if plain then name else "\"" ++ name.replace "\"" "\"\"" ++ "\""

def print (name : String) (columns : List (String × Affinity)) : String :=
  let estimate := identLength name + columns.foldl (fun n col => n + identLength col.1 + 5) 0
  let short := estimate < 50
  let column (value : String × Affinity) := ident value.1 ++ match value.2 with
    | .blob => "" | .text => " TEXT" | .numeric => " NUM"
    | .integer => " INT" | .real => " REAL"
  "CREATE TABLE " ++ ident name ++ "(" ++ (if short then "" else "\n  ") ++
    String.intercalate (if short then "," else ",\n  ") (columns.map column) ++
    (if short then ")" else "\n)")

end SQLeanite.SQLite.CtasCatalog
