import SQLeanite.CanonicalSchemaSQL

/-!
# Canonical `CREATE INDEX` printer and inverse

The physical catalog must recover index metadata without trusting the full SQL
parser for text emitted by this implementation. This small grammar is the
index counterpart of `CanonicalSchemaSQL`.
-/

namespace SQLeanite.CanonicalIndexSQL

structure Spec where
  name : String
  table : String
  column : String
  unique : Bool := false
  deriving DecidableEq, Repr

def Spec.chars (spec : Spec) : List Char :=
  (if spec.unique then "CREATE UNIQUE INDEX " else "CREATE INDEX ").toList ++ CanonicalSchemaSQL.quoteChars spec.name ++
    " ON ".toList ++ CanonicalSchemaSQL.quoteChars spec.table ++
    '(' :: CanonicalSchemaSQL.quoteChars spec.column ++ [')']

def print (spec : Spec) : String := String.ofList spec.chars

/-- Canonical catalog suffix used only when the encoder has established that
every current value in the index is INTEGER.  SQLite accepts the SQL comment;
the exact spelling makes it a checkable generated-image certificate rather
than a heuristic annotation. -/
def integerCertificateMarker : String := " /*LSQL:INTEGER*/"

/-- Generated-image certificate for indexes whose current values are all TEXT.
The marker is exact catalog provenance, not a type guess made while opening. -/
def textCertificateMarker : String := " /*LSQL:TEXT*/"

def printIntegerCertified (spec : Spec) : String :=
  print spec ++ integerCertificateMarker

def printTextCertified (spec : Spec) : String :=
  print spec ++ textCertificateMarker

def parseChars (input : List Char) : Option Spec := do
  let (unique, afterCreate) ← match CanonicalSchemaSQL.stripPrefix "CREATE UNIQUE INDEX ".toList input with
    | some after => some (true, after)
    | none => (CanonicalSchemaSQL.stripPrefix "CREATE INDEX ".toList input).map (false, ·)
  match afterCreate with
  | '"' :: afterOpenIndex => do
      let (indexName, afterIndex) ← CanonicalSchemaSQL.takeIdent afterOpenIndex
      let afterOn ← CanonicalSchemaSQL.stripPrefix " ON ".toList afterIndex
      match afterOn with
      | '"' :: afterOpenTable => do
          let (tableName, afterTable) ← CanonicalSchemaSQL.takeIdent afterOpenTable
          match afterTable with
          | '(' :: '"' :: afterOpenColumn => do
              let (columnName, tail) ← CanonicalSchemaSQL.takeIdent afterOpenColumn
              if tail = [')'] ∨
                  tail = ')' :: integerCertificateMarker.toList ∨
                  tail = ')' :: textCertificateMarker.toList then
                some ⟨String.ofList indexName, String.ofList tableName, String.ofList columnName, unique⟩
              else none
          | _ => none
      | _ => none
  | _ => none

def parse (sql : String) : Option Spec := parseChars sql.toList

private theorem strip_unique_nonunique (suffix : List Char) :
    CanonicalSchemaSQL.stripPrefix "CREATE UNIQUE INDEX ".toList
      ("CREATE INDEX ".toList ++ suffix) = none := by rfl

theorem parseChars_chars (spec : Spec) :
    parseChars spec.chars = some spec := by
  rcases spec with ⟨indexName, tableName, columnName, unique⟩
  change parseChars
    ((if unique then "CREATE UNIQUE INDEX " else "CREATE INDEX ").toList ++ CanonicalSchemaSQL.quoteChars indexName ++
      " ON ".toList ++ CanonicalSchemaSQL.quoteChars tableName ++
      '(' :: CanonicalSchemaSQL.quoteChars columnName ++ [')']) =
    some ⟨indexName, tableName, columnName, unique⟩
  unfold parseChars
  simp only [List.append_assoc]
  cases unique <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals simp only [strip_unique_nonunique, CanonicalSchemaSQL.stripPrefix_append, Option.map, Option.bind_eq_bind, Option.bind]
  all_goals simp only [CanonicalSchemaSQL.quoteChars, List.cons_append, List.nil_append,
    List.append_assoc,
    Option.bind_eq_bind, Option.bind]
  all_goals rw [CanonicalSchemaSQL.takeIdent_escape _ _ (by simp)]
  all_goals simp only [Option.bind_eq_bind, Option.bind]
  all_goals simp [CanonicalSchemaSQL.stripPrefix]
  all_goals rw [CanonicalSchemaSQL.takeIdent_escape _ _ (by simp)]
  all_goals simp only [Option.bind_eq_bind, Option.bind]
  all_goals rw [CanonicalSchemaSQL.takeIdent_escape _ _ (by simp)]
  all_goals simp

theorem parse_print (spec : Spec) :
    parse (print spec) = some spec := by
  unfold parse print
  rw [String.toList_ofList]
  exact parseChars_chars spec

theorem parse_printIntegerCertified (spec : Spec) :
    parse (printIntegerCertified spec) = some spec := by
  simp only [parse, printIntegerCertified, print, String.toList_append, String.toList_ofList]
  rcases spec with ⟨indexName, tableName, columnName, unique⟩
  change parseChars
    ((⟨indexName, tableName, columnName, unique⟩ : Spec).chars ++
      integerCertificateMarker.toList) =
        some ⟨indexName, tableName, columnName, unique⟩
  unfold Spec.chars parseChars
  simp only [List.append_assoc]
  cases unique <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals simp only [strip_unique_nonunique, CanonicalSchemaSQL.stripPrefix_append, Option.map, Option.bind_eq_bind, Option.bind]
  all_goals simp only [CanonicalSchemaSQL.quoteChars, List.cons_append, List.nil_append,
    List.append_assoc, Option.bind_eq_bind, Option.bind]
  all_goals rw [CanonicalSchemaSQL.takeIdent_escape _ _ (by simp)]
  all_goals simp only [Option.bind_eq_bind, Option.bind]
  all_goals simp [CanonicalSchemaSQL.stripPrefix]
  all_goals rw [CanonicalSchemaSQL.takeIdent_escape _ _ (by simp)]
  all_goals simp only [Option.bind_eq_bind, Option.bind]
  all_goals rw [CanonicalSchemaSQL.takeIdent_escape _ _ (by simp)]
  all_goals simp

theorem parse_printTextCertified (spec : Spec) :
    parse (printTextCertified spec) = some spec := by
  simp only [parse, printTextCertified, print, String.toList_append, String.toList_ofList]
  rcases spec with ⟨indexName, tableName, columnName, unique⟩
  change parseChars
    ((⟨indexName, tableName, columnName, unique⟩ : Spec).chars ++
      textCertificateMarker.toList) =
        some ⟨indexName, tableName, columnName, unique⟩
  unfold Spec.chars parseChars
  simp only [List.append_assoc]
  cases unique <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals simp only [strip_unique_nonunique, CanonicalSchemaSQL.stripPrefix_append, Option.map, Option.bind_eq_bind, Option.bind]
  all_goals simp only [CanonicalSchemaSQL.quoteChars, List.cons_append, List.nil_append,
    List.append_assoc, Option.bind_eq_bind, Option.bind]
  all_goals rw [CanonicalSchemaSQL.takeIdent_escape _ _ (by simp)]
  all_goals simp only [Option.bind_eq_bind, Option.bind]
  all_goals simp [CanonicalSchemaSQL.stripPrefix]
  all_goals rw [CanonicalSchemaSQL.takeIdent_escape _ _ (by simp)]
  all_goals simp only [Option.bind_eq_bind, Option.bind]
  all_goals rw [CanonicalSchemaSQL.takeIdent_escape _ _ (by simp)]
  all_goals simp

/-- Decode the marker only when the entire catalog SQL is exactly the
canonical certified printer. -/
def parseIntegerCertified (sql : String) : Option Spec := do
  let spec ← parse sql
  if sql = printIntegerCertified spec then some spec else none

theorem parseIntegerCertified_print (spec : Spec) :
    parseIntegerCertified (printIntegerCertified spec) = some spec := by
  unfold parseIntegerCertified
  rw [parse_printIntegerCertified]
  simp

def parseTextCertified (sql : String) : Option Spec := do
  let spec ← parse sql
  if sql = printTextCertified spec then some spec else none

theorem parseTextCertified_print (spec : Spec) :
    parseTextCertified (printTextCertified spec) = some spec := by
  unfold parseTextCertified
  rw [parse_printTextCertified]
  simp

def parseGeneratedCertified (sql : String) : Option Spec :=
  match parseIntegerCertified sql with
  | some spec => some spec
  | none => parseTextCertified sql

end SQLeanite.CanonicalIndexSQL
