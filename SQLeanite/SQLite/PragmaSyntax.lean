import SQLeanite.Lexer

/-! SQLite 3.53.4 PRAGMA atom syntax, from parse.y nm/nmnum/number and
pragma.c token dequoting. Numeric source spelling is semantic here: 01 and
0x1 name different objects even though their numeric values are equal. -/
namespace SQLeanite.SQLite.PragmaSyntax

/-- Non-fallback keywords excluded from nmnum; ON/DELETE/DEFAULT are explicit
exceptions. WINDOW/FILTER/OVER are contextual identifiers in this position. -/
def bareArgumentName (name : String) : Bool :=
  !["add", "all", "alter", "and", "as", "autoincrement", "between", "case",
    "check", "collate", "commit", "constraint", "create", "deferrable", "distinct",
    "drop", "else", "escape", "except", "exists", "foreign", "from", "group",
    "having", "in", "index", "insert", "intersect", "into", "is", "isnull", "join", "limit",
    "not", "nothing", "notnull", "null", "or", "order", "primary", "references", "returning",
    "select", "set", "table", "then", "to", "transaction", "union", "unique",
    "update", "using", "values", "when", "where"].contains name.toLower

def bareName (name : String) : Bool :=
  bareArgumentName name && !["on", "delete", "default"].contains name.toLower

def nameToken (argument : Bool) : Token → Option String
  | .ident name => if (if argument then bareArgumentName name else bareName name) then some name else none
  | .quotedIdent name _ | .string name => some name
  | _ => none

def signedSource (negative : Bool) (source : String) : String :=
  (if negative then "-" else "") ++ source

def numeric (negative : Bool) : Token → Option (Value × String)
  | .integer integer source =>
      let source := source.getD (toString integer)
      if source.contains '_' then none else
        let signed := if negative then -integer else integer
        let value := if (-9223372036854775808 : Int) ≤ signed && signed ≤ 9223372036854775807 then
          Value.integer signed else Value.real (Float.ofInt signed)
        some (value, signedSource negative source)
  | .real source => do
      if source.contains '_' then none else do
        let value ← parseDecimal? source
        some (.real (if negative then -value else value), signedSource negative source)
  | _ => none

theorem numeric_integer_spelling (negative : Bool) (integer : Int) (source : String)
    (noSeparators : source.contains '_' = false) :
    (numeric negative (.integer integer (some source))).map Prod.snd =
      some (signedSource negative source) := by
  simp [numeric, noSeparators]

/-- Recognized names in the pinned SQLite 3.53.4 build, from pragma.h and its
PRAGMA pragma_list. Recognition does not mean implementation: known but
unimplemented operations still fail explicitly; unknown names are no-ops. -/
def knownNames : List String :=
  ["analysis_limit", "application_id", "auto_vacuum", "automatic_index", "busy_timeout", "cache_size",
    "cache_spill", "case_sensitive_like", "cell_size_check", "checkpoint_fullfsync", "collation_list", "compile_options",
    "count_changes", "data_version", "database_list", "default_cache_size", "defer_foreign_keys", "empty_result_callbacks",
    "encoding", "foreign_key_check", "foreign_key_list", "foreign_keys", "freelist_count", "full_column_names",
    "fullfsync", "function_list", "hard_heap_limit", "ignore_check_constraints", "incremental_vacuum", "index_info",
    "index_list", "index_xinfo", "integrity_check", "journal_mode", "journal_size_limit", "legacy_alter_table",
    "locking_mode", "max_page_count", "mmap_size", "module_list", "optimize", "page_count",
    "page_size", "pragma_list", "query_only", "quick_check", "read_uncommitted", "recursive_triggers",
    "reverse_unordered_selects", "schema_version", "secure_delete", "short_column_names", "shrink_memory", "soft_heap_limit",
    "synchronous", "table_info", "table_list", "table_xinfo", "temp_store", "temp_store_directory",
    "threads", "trusted_schema", "user_version", "wal_autocheckpoint", "wal_checkpoint", "writable_schema"]

end SQLeanite.SQLite.PragmaSyntax
