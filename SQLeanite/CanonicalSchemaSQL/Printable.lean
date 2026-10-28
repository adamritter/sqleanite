import SQLeanite.CoreData.Value
import Std.Data.String.ToNat

namespace SQLeanite.CanonicalSchemaSQL

/-- The structural conditions needed to recover exactly the schema that was
printed. Identifier text itself is unrestricted: `quoteChars` escapes quotes. -/
structure Printable (schema : Core.Schema) : Prop where
  nonempty : schema.catalogColumns ≠ []
  primaryKeyNotNull : ∀ column ∈ schema.catalogColumns,
    column.integerPrimaryKey → column.notNull
  catalogShape : schema.CatalogShape

theorem Printable.ofWellFormed (schema : Core.Schema)
    (wellFormed : schema.WellFormed) : Printable schema := by
  have shape := wellFormed.2.2.2.2.2.2
  refine {
    nonempty := ?_
    primaryKeyNotNull := ?_
    catalogShape := shape }
  · intro empty
    unfold Core.Schema.CatalogShape at shape
    split at shape
    · exact shape.2.2.2.1 empty
    · have columns : schema.catalogColumns = schema.columns := shape.1
      have bound := wellFormed.1
      rw [← columns, empty] at bound
      simp at bound
  · intro column member primary
    exact wellFormed.2.2.2.2.2.1 column
      (by
        unfold Core.Schema.catalogColumns at member
        split at member
        · exact List.mem_of_mem_take member
        · exact member)
      primary

def escapeIdent : List Char → List Char
  | [] => []
  | '"' :: rest => '"' :: '"' :: escapeIdent rest
  | character :: rest => character :: escapeIdent rest

def quoteChars (name : String) : List Char := '"' :: escapeIdent name.toList ++ ['"']

def columnSuffix (column : Core.Column) : List Char :=
  if column.integerPrimaryKey then
    if column.integerPrimaryNotNull then " INTEGER PRIMARY KEY NOT NULL".toList
    else " INTEGER PRIMARY KEY".toList
  else if column.textPrimaryKey then
    if column.notNull then " TEXT PRIMARY KEY NOT NULL".toList
    else " TEXT PRIMARY KEY".toList
  else if column.notNull then " NOT NULL".toList
  else []

def typeCaseChars (name : String) : List Char :=
  if name.isEmpty then []
  else if SQLite.ColumnType.preserveCase name then "(0)".toList else []

def columnTypeChars (column : Core.Column) : List Char :=
  if column.explicitEmptyType || !column.declaredType.isEmpty then
    ' ' :: (quoteChars column.declaredType ++ typeCaseChars column.declaredType)
  else []

def baseColumnChars (column : Core.Column) : List Char :=
  quoteChars column.name ++ columnTypeChars column ++ columnSuffix column

def notNullConflictChars : Core.NotNullConflict → List Char
  | .abort => []
  | .ignore => " ON CONFLICT IGNORE".toList
  | .replace => " ON CONFLICT REPLACE".toList

def plainColumnChars (column : Core.Column) : List Char :=
  baseColumnChars column ++ notNullConflictChars column.notNullConflict

/-- A nondefault key uses a quoted type and a trailing PRIMARY KEY clause.
The ordinary base preserves explicit NOT NULL independently of rowid allocation. -/
def primaryBase (column : Core.Column) : Core.Column :=
  if key : column.integerPrimaryKey = true then {
    name := column.name, declaredType := "INTEGER", notNull := column.integerPrimaryNotNull,
    notNullConflict := column.notNullConflict,
    notNullConflictOnly := fun different => ⟨(column.notNullConflictOnly different).2 key, by simp⟩ }
  else {
    name := column.name, declaredType := "TEXT", notNull := column.notNull,
    notNullConflict := column.notNullConflict,
    notNullConflictOnly := fun different => ⟨(column.notNullConflictOnly different).1, by simp⟩ }

def primaryConflictChars : Core.NotNullConflict → List Char
  | .abort => []
  | .ignore => " PRIMARY KEY ON CONFLICT IGNORE".toList
  | .replace => " PRIMARY KEY ON CONFLICT REPLACE".toList

def legacyKeyColumnChars (column : Core.Column) : List Char :=
  if column.primaryConflict = .abort then plainColumnChars column
  else plainColumnChars (primaryBase column) ++ primaryConflictChars column.primaryConflict

/-- A precision suffix prevents an INTEGER display name from accidentally
becoming a rowid alias. All semantics remain in the ordinary SQL body. -/
def indexedTypeChars (typ : Core.IndexedType) : List Char :=
  if typ.explicitEmptyType || !typ.declaredType.isEmpty then
    ' ' :: (quoteChars typ.declaredType ++ "(0)".toList)
  else []

def explicitPrimaryChars : Core.NotNullConflict → List Char
  | .abort => " PRIMARY KEY ON CONFLICT ABORT".toList
  | .ignore => " PRIMARY KEY ON CONFLICT IGNORE".toList
  | .replace => " PRIMARY KEY ON CONFLICT REPLACE".toList

def indexedBodyChars (column : Core.Column) (typ : Core.IndexedType) : List Char :=
  quoteChars column.name ++ indexedTypeChars typ ++
    (if column.notNull then " NOT NULL".toList else " NULL".toList) ++
    notNullConflictChars column.notNullConflict ++ explicitPrimaryChars column.primaryConflict

def typedKeyColumnChars (column : Core.Column) : List Char :=
  match column.indexedType with
  | none => legacyKeyColumnChars column
  | some typ => "/*sqleanite-key*/".toList ++ indexedBodyChars column typ

def autoBodyChars (column : Core.Column) : List Char :=
  quoteChars column.name ++ " INTEGER".toList ++ explicitPrimaryChars column.primaryConflict ++
    " AUTOINCREMENT".toList ++
    (if column.integerPrimaryNotNull then " NOT NULL".toList ++ notNullConflictChars column.notNullConflict
     else " NULL".toList)

def keyColumnChars (column : Core.Column) : List Char :=
  if column.autoIncrement then "/*sqleanite-autoinc*/".toList ++ autoBodyChars column
  else typedKeyColumnChars column

/-- Lengths only frame ordinary SQL; the actual DEFAULT follows its column.
Both pieces are independently checked when the certificate is read. -/
def defaultHeader (base source : List Char) : List Char :=
  "/*sqleanite-default ".toList ++ quoteChars (toString base.length) ++ [' '] ++
    quoteChars (toString source.length) ++ "*/".toList

def columnChars (column : Core.Column) : List Char :=
  match column.defaultValue with
  | none => keyColumnChars column
  | some spec =>
      let base := keyColumnChars { column with defaultValue := none }
      defaultHeader base spec.source.toList ++ base ++ " DEFAULT ".toList ++ spec.source.toList ++ ['\n']

def columnsChars : List Core.Column → List Char
  | [] => []
  | [column] => columnChars column
  | column :: columns => columnChars column ++ ',' :: columnsChars columns

def tableChars (schema : Core.Schema) : List Char :=
  "CREATE TABLE ".toList ++ quoteChars schema.name ++
    '(' :: columnsChars schema.catalogColumns ++ [')']

def print (schema : Core.Schema) : String := String.ofList (tableChars schema)

def stripPrefix : List Char → List Char → Option (List Char)
  | [], input => some input
  | _ :: _, [] => none
  | expected :: expectedRest, actual :: actualRest =>
      if expected = actual then stripPrefix expectedRest actualRest else none

/-- Characters up to the closing quote. Fails if the quote is missing. -/
def takeIdent : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: '"' :: rest => do
      let (name, tail) ← takeIdent rest
      some ('"' :: name, tail)
  | '"' :: rest => some ([], rest)
  | character :: rest => do
      let (name, tail) ← takeIdent rest
      some (character :: name, tail)

/-- A complete column ends at a list separator. The ordinary base may also
end before the trailing primary-key constraint emitted above. -/
def endsColumn : List Char → Bool
  | [] => true
  | ',' :: _ => true
  | ')' :: _ => true
  | _ => false

def endsBaseColumn (input : List Char) : Bool :=
  endsColumn input || input.take 2 == [' ', 'P']

def parseTypedColumn (name : List Char) (input : List Char) :
    Option (Core.Column × List Char) := do
  let (typeName, afterType) ← takeIdent input
  let afterType ← stripPrefix (typeCaseChars (String.ofList typeName)) afterType
  if endsBaseColumn afterType then
    some (Core.Column.typed (String.ofList name) (String.ofList typeName) false, afterType)
  else
    let rest ← stripPrefix " NOT NULL".toList afterType
    some (Core.Column.typed (String.ofList name) (String.ofList typeName) true, rest)

def parseBaseColumn : List Char → Option (Core.Column × List Char)
  | '"' :: rest => do
      let (name, afterName) ← takeIdent rest
      if endsBaseColumn afterName then
        some ({ name := String.ofList name, notNull := false,
                integerPrimaryKey := false }, afterName)
      else
        match stripPrefix " INTEGER PRIMARY KEY".toList afterName with
        | some tail =>
            match stripPrefix " NOT NULL".toList tail with
            | some remaining =>
                some ({ name := String.ofList name, notNull := true,
                        integerPrimaryKey := true, integerPrimaryNotNull := true }, remaining)
            | none =>
                some ({ name := String.ofList name, notNull := true,
                        integerPrimaryKey := true }, tail)
        | none =>
          match stripPrefix " TEXT PRIMARY KEY".toList afterName with
          | some tail =>
              match stripPrefix " NOT NULL".toList tail with
              | some remaining =>
                  some ({ name := String.ofList name, notNull := true,
                          textPrimaryKey := true }, remaining)
              | none =>
                  some ({ name := String.ofList name, notNull := false,
                          textPrimaryKey := true }, tail)
          | none =>
            match stripPrefix " NOT NULL".toList afterName with
            | some tail =>
                some ({ name := String.ofList name, notNull := true }, tail)
            | none => match afterName with
                | ' ' :: '"' :: rest => parseTypedColumn name rest
                | _ => none
  | _ => none

def parsePlainColumn (input : List Char) : Option (Core.Column × List Char) := do
  let (column, tail) ← parseBaseColumn input
  match stripPrefix " ON CONFLICT IGNORE".toList tail with
  | some rest => return (← column.withNotNullConflict .ignore, rest)
  | none => match stripPrefix " ON CONFLICT REPLACE".toList tail with
      | some rest => return (← column.withNotNullConflict .replace, rest)
      | none => return (column, tail)

def primaryFromBase (column : Core.Column) (policy : Core.NotNullConflict) : Option Core.Column :=
  if column.integerPrimaryKey || column.textPrimaryKey then none
  else if column.declaredType = "INTEGER" then some {
    name := column.name, notNull := true, integerPrimaryKey := true,
    integerPrimaryNotNull := column.notNull, notNullConflict := column.notNullConflict,
    notNullConflictOnly := fun different => ⟨rfl, fun _ => (column.notNullConflictOnly different).1⟩,
    primaryConflict := policy, primaryConflictOnly := by simp }
  else if column.declaredType = "TEXT" then some {
    name := column.name, notNull := column.notNull, textPrimaryKey := true,
    notNullConflict := column.notNullConflict,
    notNullConflictOnly := fun different => ⟨(column.notNullConflictOnly different).1, by simp⟩,
    primaryConflict := policy, primaryConflictOnly := by simp }
  else none

def parseLegacyKeyColumn (input : List Char) : Option (Core.Column × List Char) := do
  let (column, tail) ← parsePlainColumn input
  match stripPrefix " PRIMARY KEY ON CONFLICT IGNORE".toList tail with
  | some rest => return (← primaryFromBase column .ignore, rest)
  | none => match stripPrefix " PRIMARY KEY ON CONFLICT REPLACE".toList tail with
      | some rest => return (← primaryFromBase column .replace, rest)
      | none => return (column, tail)

def typedIndexedType (name : String) : Core.IndexedType :=
  if name = "" then { declaredType := "", explicitEmptyType := true }
  else { declaredType := name }

def parseIndexedType : List Char → Option (Core.IndexedType × List Char)
  | ' ' :: '"' :: input => do
      let (name, rest) ← takeIdent input
      let rest ← stripPrefix "(0)".toList rest
      return (typedIndexedType (String.ofList name), rest)
  | input => some ({ declaredType := "" }, input)

def parseNullPolicy (input : List Char) : Core.NotNullConflict × List Char :=
  match stripPrefix " ON CONFLICT IGNORE".toList input with
  | some rest => (.ignore, rest)
  | none => match stripPrefix " ON CONFLICT REPLACE".toList input with
    | some rest => (.replace, rest)
    | none => (.abort, input)

def parseExplicitPrimary (input : List Char) : Option (Core.NotNullConflict × List Char) :=
  match stripPrefix " PRIMARY KEY ON CONFLICT ABORT".toList input with
  | some rest => some (.abort, rest)
  | none => match stripPrefix " PRIMARY KEY ON CONFLICT IGNORE".toList input with
    | some rest => some (.ignore, rest)
    | none => (stripPrefix " PRIMARY KEY ON CONFLICT REPLACE".toList input).map fun rest => (.replace, rest)

def fromIndexed (name : String) (typ : Core.IndexedType) (notNull : Bool)
    (nullPolicy primaryPolicy : Core.NotNullConflict) : Option Core.Column :=
  ({
    name := name
    notNull := notNull
    textPrimaryKey := true
    indexedType := some typ
    primaryConflict := primaryPolicy
    primaryConflictOnly := by simp
    indexedTypeOnly := by simp } : Core.Column).withNotNullConflict nullPolicy

def parseIndexedBody (input : List Char) : Option (Core.Column × List Char) := do
  let '"' :: input := input | none
  let (name, input) ← takeIdent input
  let (typ, input) ← parseIndexedType input
  let (notNull, input) ← match stripPrefix " NOT NULL".toList input with
    | some rest => some (true, rest)
    | none => (stripPrefix " NULL".toList input).map fun rest => (false, rest)
  let (nullPolicy, input) := parseNullPolicy input
  let (primaryPolicy, input) ← parseExplicitPrimary input
  let column ← fromIndexed (String.ofList name) typ notNull nullPolicy primaryPolicy
  return (column, input)

def parseTypedKeyColumn (input : List Char) : Option (Core.Column × List Char) :=
  match stripPrefix "/*sqleanite-key*/".toList input with
  | some rest => parseIndexedBody rest
  | none => parseLegacyKeyColumn input

def fromAuto (name : String) (explicitNotNull : Bool)
    (nullPolicy primaryPolicy : Core.NotNullConflict) : Option Core.Column :=
  ({
    name := name
    notNull := true
    integerPrimaryKey := true
    integerPrimaryNotNull := explicitNotNull
    primaryConflict := primaryPolicy
    primaryConflictOnly := by simp
    autoIncrement := true
    autoIncrementOnly := by simp } : Core.Column).withNotNullConflict nullPolicy

def parseAutoBody (input : List Char) : Option (Core.Column × List Char) := do
  let '"' :: input := input | none
  let (name, input) ← takeIdent input
  let input ← stripPrefix " INTEGER".toList input
  let (primaryPolicy, input) ← parseExplicitPrimary input
  let input ← stripPrefix " AUTOINCREMENT".toList input
  match stripPrefix " NOT NULL".toList input with
  | some rest =>
      let (nullPolicy, rest) := parseNullPolicy rest
      let column ← fromAuto (String.ofList name) true nullPolicy primaryPolicy
      return (column, rest)
  | none =>
      let rest ← stripPrefix " NULL".toList input
      let column ← fromAuto (String.ofList name) false .abort primaryPolicy
      return (column, rest)

def parseKeyColumn (input : List Char) : Option (Core.Column × List Char) :=
  match stripPrefix "/*sqleanite-autoinc*/".toList input with
  | some rest => parseAutoBody rest
  | none => parseTypedKeyColumn input

def takeQuotedNat (input : List Char) : Option (Nat × List Char) := do
  let '"' :: input := input | none
  let (digits, rest) ← takeIdent input
  let number ← (String.ofList digits).toNat?
  return (number, rest)

def parseColumn (input : List Char) : Option (Core.Column × List Char) :=
  match stripPrefix "/*sqleanite-default ".toList input with
  | none => parseKeyColumn input
  | some afterTag => do
      let (baseLength, rest) ← takeQuotedNat afterTag
      let rest ← stripPrefix [' '] rest
      let (sourceLength, rest) ← takeQuotedNat rest
      let rest ← stripPrefix "*/".toList rest
      let (column, []) ← parseKeyColumn (rest.take baseLength) | none
      let sourceStart ← stripPrefix " DEFAULT ".toList (rest.drop baseLength)
      let spec ← ColumnDefault.fromSource (String.ofList (sourceStart.take sourceLength))
      let tail ← stripPrefix ['\n'] (sourceStart.drop sourceLength)
      return ({ column with defaultValue := some spec }, tail)

def parseColumns : Nat → List Char → Option (List Core.Column × List Char)
  | 0, _ => none
  | fuel + 1, input => do
      let (column, afterColumn) ← parseColumn input
      match afterColumn with
      | ',' :: rest => do
          let (columns, tail) ← parseColumns fuel rest
          some (column :: columns, tail)
      | _ => some ([column], afterColumn)

def parseChars (input : List Char) : Option Core.Schema := do
  let afterKeyword ← stripPrefix "CREATE TABLE ".toList input
  match afterKeyword with
  | '"' :: rest => do
      let (name, afterName) ← takeIdent rest
      match afterName with
      | '(' :: afterParen => do
          let (columns, tail) ← parseColumns (afterParen.length + 1) afterParen
          match tail with
          | [')'] =>
              match columns.findIdx? (·.integerPrimaryKey) with
              | some primaryKey => some {
                  name := String.ofList name
                  columns := columns
                  primaryKey
                  declaredPrimaryKey := primaryKey }
              | none =>
                  let declaredPrimaryKey := (columns.findIdx? (·.textPrimaryKey)).getD (columns.length + 1)
                  some {
                    name := String.ofList name
                    columns := columns ++ [Core.hiddenRowidColumn]
                    primaryKey := columns.length
                    declaredPrimaryKey }
          | _ => none
      | _ => none
  | _ => none

def parse (sql : String) : Option Core.Schema := parseChars sql.toList

theorem stripPrefix_append (expected rest : List Char) :
    stripPrefix expected (expected ++ rest) = some rest := by
  induction expected with
  | nil => rfl
  | cons character expected induction => simp [stripPrefix, induction]

theorem takeIdent_escape (name rest : List Char)
    (boundary : rest.head? ≠ some '"') :
    takeIdent (escapeIdent name ++ '"' :: rest) = some (name, rest) := by
  induction name with
  | nil =>
      cases rest with
      | nil => rfl
      | cons character rest =>
          have notQuote : character ≠ '"' := by simpa using boundary
          simp [escapeIdent, takeIdent, notQuote]
  | cons character name induction =>
      cases quote : character == '"'
      · have notQuote : character ≠ '"' := by simpa using quote
        simp [escapeIdent, notQuote, takeIdent, induction]
      · have isQuote : character = '"' := by simpa using quote
        subst character
        simp [escapeIdent, takeIdent, induction]

/-- No suffix is a prefix of a separator, so a plain column stops correctly. -/
theorem stripPrefix_sep_none (suffix : List Char) (character : Char)
    (rest : List Char) (leading : suffix = ' ' :: suffix.tail)
    (notSpace : character ≠ ' ') :
    stripPrefix suffix (character :: rest) = none := by
  rw [leading]
  simp [stripPrefix, Ne.symm notSpace]

theorem stripPrefix_notNull_cons (rest : List Char) :
    stripPrefix " NOT NULL".toList
      (' ' :: 'N' :: 'O' :: 'T' :: ' ' :: 'N' :: 'U' :: 'L' :: 'L' :: rest)
      = some rest := rfl

theorem stripPrefix_ipk_miss (rest : List Char) :
    stripPrefix " INTEGER PRIMARY KEY".toList
      (' ' :: 'N' :: 'O' :: 'T' :: ' ' :: 'N' :: 'U' :: 'L' :: 'L' :: rest)
      = none := rfl

theorem stripPrefix_ipk_cons (rest : List Char) :
    stripPrefix " INTEGER PRIMARY KEY".toList
      (' ' :: 'I' :: 'N' :: 'T' :: 'E' :: 'G' :: 'E' :: 'R' :: ' ' :: 'P' :: 'R'
        :: 'I' :: 'M' :: 'A' :: 'R' :: 'Y' :: ' ' :: 'K' :: 'E' :: 'Y' :: rest)
      = some rest := rfl

theorem baseSeparator_cases (rest : List Char) (separator : endsBaseColumn rest = true) :
    endsColumn rest = true ∨ ∃ tail, rest = ' ' :: 'P' :: tail := by
  simp only [endsBaseColumn, Bool.or_eq_true, beq_iff_eq] at separator
  rcases separator with ordinary | primary
  · exact Or.inl ordinary
  · apply Or.inr
    cases rest with
    | nil => simp at primary
    | cons first rest =>
        cases rest with
        | nil => simp at primary
        | cons second tail =>
            simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at primary
            rcases primary with ⟨rfl, rfl⟩
            exact ⟨tail, rfl⟩

end SQLeanite.CanonicalSchemaSQL
