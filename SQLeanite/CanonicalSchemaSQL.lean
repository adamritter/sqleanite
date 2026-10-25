import Std.Data.String.ToNat
import SQLeanite.Core

/-!
# Canonical `CREATE TABLE` printer and its inverse

`decode` recovers a schema by running the full SQL parser over the text that
`encode` printed into `sqlite_schema`, so closing `decode (encode db) = db`
would need parser correctness over generated text -- a large, separate result.

This module removes that dependency for the text we generate ourselves. It
defines the printer over `List Char` and a recognizer that inverts it, and
proves `parse (print s) = some s`. `CoreDecode` tries this recognizer first and
falls back to the general parser, so files written by C SQLite still decode
while our own files round-trip by proof.

Working in `List Char` rather than `String` is deliberate: `String.ofList` and
`String.toList` are inverse by the standard library round-trip theorems.

`Printable` contains only structural schema facts. Identifier text is arbitrary:
the printer uses SQLite's doubled-quote convention and the inverse proof covers
embedded quotes and separators.
-/

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

/-! ## Printer -/

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

def keyColumnChars (column : Core.Column) : List Char :=
  match column.indexedType with
  | none => legacyKeyColumnChars column
  | some typ => "/*sqleanite-key*/".toList ++ indexedBodyChars column typ

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

/-! ## Recognizer -/

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

def parseKeyColumn (input : List Char) : Option (Core.Column × List Char) :=
  match stripPrefix "/*sqleanite-key*/".toList input with
  | some rest => parseIndexedBody rest
  | none => parseLegacyKeyColumn input

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

/-! ## The inverse proof -/

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

private theorem baseSeparator_cases (rest : List Char) (separator : endsBaseColumn rest = true) :
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

private theorem stripPrefix_notNull_end (rest : List Char)
    (separator : endsBaseColumn rest = true) : stripPrefix " NOT NULL".toList rest = none := by
  rcases baseSeparator_cases rest separator with ordinary | ⟨tail, rfl⟩
  · cases rest with
    | nil => rfl
    | cons c tail =>
        have notSpace : c ≠ ' ' := by
          intro equal
          subst c
          simp [endsColumn] at ordinary
        simp [stripPrefix, Ne.symm notSpace]
  · rfl

theorem parseBaseColumn_append (columnName : String)
    (columnNotNull columnPrimary columnTextPrimary : Bool)
    (rest : List Char)
    (consistent : columnPrimary = true →
      columnNotNull = true)
    (exclusive : columnPrimary = true → columnTextPrimary = false)
    (separator : endsBaseColumn rest = true ∨ (columnNotNull = true ∧ columnPrimary = false)) :
    parseBaseColumn (baseColumnChars
      { name := columnName, notNull := columnNotNull, integerPrimaryKey := columnPrimary, textPrimaryKey := columnTextPrimary } ++ rest)
      = some
        ({ name := columnName, notNull := columnNotNull, integerPrimaryKey := columnPrimary, textPrimaryKey := columnTextPrimary }, rest) := by
  cases columnPrimary <;> cases columnTextPrimary <;> cases columnNotNull
  all_goals simp only [Bool.false_eq_true, Bool.true_eq_false, and_false, false_and, or_false] at separator
  · have shape : baseColumnChars
        ({ name := columnName, notNull := false, integerPrimaryKey := false, textPrimaryKey := false } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' :: rest) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by
      intro leadingQuote
      cases rest with
      | nil => simp at leadingQuote
      | cons character rest =>
          have : character = '"' := by simpa using leadingQuote
          subst character
          simp [endsBaseColumn, endsColumn] at separator)]
    simp [separator]
  · have shape : baseColumnChars
        ({ name := columnName, notNull := true, integerPrimaryKey := false, textPrimaryKey := false } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' :: (" NOT NULL".toList ++ rest)) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by simp)]
    simp [endsBaseColumn, endsColumn, stripPrefix]
  · have noNotNull := stripPrefix_notNull_end rest separator
    have shape : baseColumnChars
        ({ name := columnName, notNull := false, integerPrimaryKey := false, textPrimaryKey := true } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' ::
          (" TEXT PRIMARY KEY".toList ++ rest)) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by simp)]
    simp [endsBaseColumn, endsColumn, stripPrefix] at noNotNull ⊢
    exact noNotNull ▸ rfl
  · have shape : baseColumnChars
        ({ name := columnName, notNull := true, integerPrimaryKey := false, textPrimaryKey := true } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' ::
          (" TEXT PRIMARY KEY NOT NULL".toList ++ rest)) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by simp)]
    simp [endsBaseColumn, endsColumn, stripPrefix]
  · exact absurd (consistent rfl) (by simp)
  · have shape : baseColumnChars
        ({ name := columnName, notNull := true, integerPrimaryKey := true, textPrimaryKey := false } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' :: (" INTEGER PRIMARY KEY".toList ++ rest)) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by simp)]
    have noNotNull := stripPrefix_notNull_end rest separator
    simp [endsBaseColumn, endsColumn, stripPrefix] at noNotNull ⊢
    exact noNotNull ▸ rfl
  · exact absurd (exclusive rfl) (by simp)
  · exact absurd (exclusive rfl) (by simp)

private theorem separator_not_quote {rest : List Char} (separator : endsBaseColumn rest = true) :
    rest.head? ≠ some '"' := by
  cases rest with
  | nil => simp
  | cons c rest =>
      intro equal
      have : c = '"' := by simpa using equal
      subst c
      simp [endsBaseColumn, endsColumn] at separator

private theorem typeCase_not_quote (name : String) (rest : List Char)
    (boundary : rest.head? ≠ some '"') :
    (typeCaseChars name ++ rest).head? ≠ some '"' := by
  unfold typeCaseChars
  split
  · simpa using boundary
  · split <;> simp_all

theorem parseBaseColumn_typed_append (name typeName : String) (notNull : Bool)
    (rest : List Char) (separator : endsBaseColumn rest = true ∨ notNull = true) :
    parseBaseColumn (baseColumnChars (Core.Column.typed name typeName notNull) ++ rest) =
      some (Core.Column.typed name typeName notNull, rest) := by
  cases notNull
  · have separator := separator.resolve_right (by decide)
    have shape : baseColumnChars (Core.Column.typed name typeName false) ++ rest =
        '"' :: (escapeIdent name.toList ++ '"' :: ' ' :: '"' ::
          (escapeIdent typeName.toList ++ '"' :: (typeCaseChars typeName ++ rest))) := by
      by_cases empty : typeName = ""
      · simp [Core.Column.typed, empty, baseColumnChars, columnTypeChars, columnSuffix, quoteChars, typeCaseChars]
      · have nonempty : typeName.isEmpty = false := by simpa using empty
        simp [Core.Column.typed, empty, baseColumnChars, columnTypeChars, nonempty, columnSuffix, quoteChars, List.append_assoc]
    rw [shape]
    simp only [parseBaseColumn]
    rw [takeIdent_escape _ _ (by simp)]
    change parseTypedColumn name.toList (escapeIdent typeName.toList ++ '"' :: (typeCaseChars typeName ++ rest)) = _
    unfold parseTypedColumn
    rw [takeIdent_escape _ _ (typeCase_not_quote _ _ (separator_not_quote separator))]
    simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
    rw [stripPrefix_append]
    simp [separator, bind, Option.bind]
  · have shape : baseColumnChars (Core.Column.typed name typeName true) ++ rest =
        '"' :: (escapeIdent name.toList ++ '"' :: ' ' :: '"' ::
          (escapeIdent typeName.toList ++ '"' :: (typeCaseChars typeName ++ (" NOT NULL".toList ++ rest)))) := by
      by_cases empty : typeName = ""
      · simp [Core.Column.typed, empty, baseColumnChars, columnTypeChars, columnSuffix, quoteChars, typeCaseChars, List.append_assoc]
      · have nonempty : typeName.isEmpty = false := by simpa using empty
        simp [Core.Column.typed, empty, baseColumnChars, columnTypeChars, nonempty, columnSuffix, quoteChars, List.append_assoc]
    rw [shape]
    simp only [parseBaseColumn]
    rw [takeIdent_escape _ _ (by simp)]
    change parseTypedColumn name.toList
      (escapeIdent typeName.toList ++ '"' :: (typeCaseChars typeName ++ (" NOT NULL".toList ++ rest))) = _
    unfold parseTypedColumn
    rw [takeIdent_escape _ _ (typeCase_not_quote _ _ (by simp))]
    simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
    rw [stripPrefix_append]
    simp [endsBaseColumn, endsColumn, stripPrefix, bind, Option.bind]

theorem parseBaseColumn_integerNotNull_append (name : String) (rest : List Char) :
    let column : Core.Column := { name, notNull := true, integerPrimaryKey := true, integerPrimaryNotNull := true }
    parseBaseColumn (baseColumnChars column ++ rest) = some (column, rest) := by
  dsimp only
  have shape : baseColumnChars
      ({ name, notNull := true, integerPrimaryKey := true, integerPrimaryNotNull := true } : Core.Column) ++ rest =
      '"' :: (escapeIdent name.toList ++ '"' :: (" INTEGER PRIMARY KEY NOT NULL".toList ++ rest)) := by
    simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
  rw [shape]
  simp only [parseBaseColumn]
  rw [takeIdent_escape _ _ (by simp)]
  simp [endsBaseColumn, endsColumn, stripPrefix]

theorem parseBaseColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (policy : column.notNullConflict = .abort)
    (primaryPolicy : column.primaryConflict = .abort)
    (noDefault : column.defaultValue = none)
    (noIndexed : column.indexedType = none)
    (separator : endsBaseColumn rest = true ∨ (column.notNull = true ∧
      (column.integerPrimaryKey = false ∨ column.integerPrimaryNotNull = true))) :
    parseBaseColumn (baseColumnChars column ++ rest) = some (column, rest) := by
  by_cases explicitType : column.explicitEmptyType = true
  · have flags := column.explicitEmptyTypeOnly explicitType
    have noExplicitKey : column.integerPrimaryNotNull = false := by
      cases h : column.integerPrimaryNotNull
      · rfl
      · have key := column.integerPrimaryNotNullOnly h
        simp_all
    have equal : column = Core.Column.typed column.name "" column.notNull := by
      cases column
      simp_all [Core.Column.typed]
    have ending : endsBaseColumn rest = true ∨ column.notNull = true := by
      rcases separator with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    rw [equal]
    exact parseBaseColumn_typed_append _ _ _ rest ending
  have notExplicitType : column.explicitEmptyType = false := Bool.eq_false_iff.mpr explicitType
  by_cases declared : column.integerPrimaryNotNull = true
  · have primary := column.integerPrimaryNotNullOnly declared
    have required := consistent primary
    have notText := exclusive primary
    have empty := column.primaryType (by simp [primary])
    have equal : column = { name := column.name, notNull := true, integerPrimaryKey := true, integerPrimaryNotNull := true } := by cases column; simp_all
    rw [equal]
    exact parseBaseColumn_integerNotNull_append _ rest
  · have undeclared : column.integerPrimaryNotNull = false := Bool.eq_false_iff.mpr declared
    by_cases empty : column.declaredType = ""
    · have equal : column = { name := column.name, notNull := column.notNull, integerPrimaryKey := column.integerPrimaryKey, textPrimaryKey := column.textPrimaryKey } := by cases column; simp_all
      rw [equal]
      exact parseBaseColumn_append _ _ _ _ rest consistent exclusive (by simpa [undeclared] using separator)
    · have notPrimary : column.integerPrimaryKey = false ∧ column.textPrimaryKey = false := by
        have h := column.primaryType
        cases hi : column.integerPrimaryKey <;> cases ht : column.textPrimaryKey <;> simp_all
      have equal : column = { name := column.name, notNull := column.notNull, declaredType := column.declaredType } := by cases column; simp_all
      rw [equal]
      simpa [Core.Column.typed, empty] using
        parseBaseColumn_typed_append column.name column.declaredType column.notNull rest
          (by rcases separator with h | h; exact Or.inl h; exact Or.inr h.1)

theorem parsePlainColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (primaryPolicy : column.primaryConflict = .abort)
    (noDefault : column.defaultValue = none)
    (noIndexed : column.indexedType = none)
    (separator : endsBaseColumn rest = true) :
    parsePlainColumn (plainColumnChars column ++ rest) = some (column, rest) := by
  let base := column.withoutNotNullConflict
  have allowed : endsBaseColumn (notNullConflictChars column.notNullConflict ++ rest) = true ∨
      (base.notNull = true ∧ (base.integerPrimaryKey = false ∨ base.integerPrimaryNotNull = true)) := by
    by_cases plain : column.notNullConflict = .abort
    · exact .inl (by simpa [plain, notNullConflictChars] using separator)
    · have required := column.notNullConflictOnly plain
      apply Or.inr
      refine ⟨required.1, ?_⟩
      cases key : column.integerPrimaryKey with
      | false => exact Or.inl key
      | true => exact Or.inr (required.2 key)
  have parsed := parseBaseColumn_any_append base
    (notNullConflictChars column.notNullConflict ++ rest) consistent exclusive rfl primaryPolicy noDefault noIndexed allowed
  have restored := Core.Column.restoreNotNullConflict column
  change parsePlainColumn (baseColumnChars base ++ notNullConflictChars column.notNullConflict ++ rest) = _
  rw [List.append_assoc]
  unfold parsePlainColumn
  rw [parsed]
  simp only [Option.bind_eq_bind, Option.bind]
  cases policy : column.notNullConflict with
  | abort =>
      have same : base = column := by
        dsimp [base, Core.Column.withoutNotNullConflict]
        cases column
        simp_all
      rcases baseSeparator_cases rest separator with ordinary | ⟨tail, rfl⟩
      · cases rest with
        | nil => simp [notNullConflictChars, stripPrefix, same]
        | cons character tail =>
            have notSpace : character ≠ ' ' := by
              intro equal
              subst character
              simp [endsColumn] at ordinary
            simp [notNullConflictChars, stripPrefix, same, Ne.symm notSpace]
      · simp [notNullConflictChars, stripPrefix, same]
  | ignore =>
      rw [policy] at restored
      simp [notNullConflictChars, stripPrefix, bind, Option.bind, base, restored]
  | replace =>
      rw [policy] at restored
      simp [notNullConflictChars, stripPrefix, bind, Option.bind, base, restored]

theorem primaryFromBase_inverse (column : Core.Column)
    (primary : (column.integerPrimaryKey || column.textPrimaryKey) = true)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none)
    (noIndexed : column.indexedType = none) :
    primaryFromBase (primaryBase column) column.primaryConflict = some column := by
  have notExplicitType : column.explicitEmptyType = false := by
    cases declared : column.explicitEmptyType
    · rfl
    · have flags := column.explicitEmptyTypeOnly declared
      simp_all
  have explicitOnly := column.integerPrimaryNotNullOnly
  have empty := column.primaryType primary
  cases hi : column.integerPrimaryKey <;> cases ht : column.textPrimaryKey <;>
    cases hn : column.integerPrimaryNotNull <;> cases column <;> simp_all [primaryBase, primaryFromBase]

theorem parseLegacyKeyColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none)
    (noIndexed : column.indexedType = none)
    (separator : endsColumn rest = true) :
    parseLegacyKeyColumn (legacyKeyColumnChars column ++ rest) = some (column, rest) := by
  by_cases plain : column.primaryConflict = .abort
  · have parsed := parsePlainColumn_any_append column rest consistent exclusive plain noDefault noIndexed
      (by simp [endsBaseColumn, separator])
    simp only [legacyKeyColumnChars, plain, if_pos, parseLegacyKeyColumn, parsed, Option.bind_eq_bind, Option.bind]
    cases rest with
    | nil => rfl
    | cons character tail =>
        have notSpace : character ≠ ' ' := by
          intro equal
          subst character
          simp [endsColumn] at separator
        simp [stripPrefix, Ne.symm notSpace]
  · have primary := column.primaryConflictOnly plain
    have restored := primaryFromBase_inverse column primary consistent exclusive noDefault noIndexed
    have baseConsistent : (primaryBase column).integerPrimaryKey = true → (primaryBase column).notNull = true := by
      simp [primaryBase]; split <;> simp
    have baseExclusive : (primaryBase column).integerPrimaryKey = true → (primaryBase column).textPrimaryKey = false := by
      simp [primaryBase]; split <;> simp
    have basePolicy : (primaryBase column).primaryConflict = .abort := by
      simp [primaryBase]; split <;> rfl
    have tail : endsBaseColumn (primaryConflictChars column.primaryConflict ++ rest) = true := by
      cases policy : column.primaryConflict <;> simp_all [primaryConflictChars, endsBaseColumn]
    have parsed := parsePlainColumn_any_append (primaryBase column)
      (primaryConflictChars column.primaryConflict ++ rest) baseConsistent baseExclusive basePolicy (by simp [primaryBase]; split <;> rfl) (by simp [primaryBase]; split <;> rfl) tail
    simp only [legacyKeyColumnChars, if_neg plain, List.append_assoc]
    unfold parseLegacyKeyColumn
    rw [parsed]
    simp only [Option.bind_eq_bind, Option.bind]
    cases policy : column.primaryConflict with
    | abort => contradiction
    | ignore =>
        rw [policy] at restored
        simp [primaryConflictChars, stripPrefix, bind, Option.bind, restored]
    | replace =>
        rw [policy] at restored
        simp [primaryConflictChars, stripPrefix, bind, Option.bind, restored]

private theorem parseIndexedType_absent (rest : List Char)
    (boundary : rest.take 2 ≠ [' ', '"']) :
    parseIndexedType rest = some ({ declaredType := "" }, rest) := by
  unfold parseIndexedType
  split <;> simp_all

theorem parseIndexedType_quoted (name : String) (rest : List Char) :
    parseIndexedType ((' ' :: (quoteChars name ++ "(0)".toList)) ++ rest) =
      some (typedIndexedType name, rest) := by
  simp only [quoteChars, List.cons_append, List.append_assoc, List.nil_append, parseIndexedType]
  rw [takeIdent_escape _ _ (by simp)]
  simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
  rw [stripPrefix_append]
  rfl

theorem parseIndexedType_append (typ : Core.IndexedType) (rest : List Char)
    (boundary : rest.take 2 ≠ [' ', '"']) :
    parseIndexedType (indexedTypeChars typ ++ rest) = some (typ, rest) := by
  cases typ with
  | mk name explicit consistent =>
      cases explicit
      · by_cases empty : name = ""
        · subst name
          simpa [indexedTypeChars] using parseIndexedType_absent rest boundary
        · have nonempty : name.isEmpty = false := by simpa using empty
          simpa [indexedTypeChars, nonempty, typedIndexedType, empty] using
            parseIndexedType_quoted name rest
      · have empty := consistent rfl
        subst name
        simpa [indexedTypeChars, typedIndexedType] using parseIndexedType_quoted "" rest

theorem fromIndexed_inverse (column : Core.Column) (typ : Core.IndexedType)
    (declared : column.indexedType = some typ)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none) :
    fromIndexed column.name typ column.notNull column.notNullConflict column.primaryConflict = some column := by
  have textKey : column.textPrimaryKey = true := column.indexedTypeOnly (by simp [declared])
  have noInteger : column.integerPrimaryKey = false := by
    cases key : column.integerPrimaryKey
    · rfl
    · have notText := exclusive key
      simp_all
  have noIntegerNull : column.integerPrimaryNotNull = false := by
    cases h : column.integerPrimaryNotNull
    · rfl
    · have key := column.integerPrimaryNotNullOnly h
      simp_all
  have empty := column.primaryType (by simp [textKey])
  have notEmptyType : column.explicitEmptyType = false := by
    cases h : column.explicitEmptyType
    · rfl
    · have flags := column.explicitEmptyTypeOnly h
      simp_all
  unfold fromIndexed
  have equal : ({
      name := column.name
      notNull := column.notNull
      textPrimaryKey := true
      indexedType := some typ
      primaryConflict := column.primaryConflict
      primaryConflictOnly := by simp
      indexedTypeOnly := by simp } : Core.Column) =
      column.withoutNotNullConflict := by
    cases column
    simp_all [Core.Column.withoutNotNullConflict]
  rw [equal]
  exact Core.Column.restoreNotNullConflict column

theorem parseIndexedBody_append (column : Core.Column) (typ : Core.IndexedType) (rest : List Char)
    (declared : column.indexedType = some typ)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none) :
    parseIndexedBody (indexedBodyChars column typ ++ rest) = some (column, rest) := by
  have restored := fromIndexed_inverse column typ declared exclusive noDefault
  simp only [indexedBodyChars, quoteChars, List.cons_append, List.append_assoc, List.nil_append,
    parseIndexedBody]
  rw [takeIdent_escape _ _ (by
    unfold indexedTypeChars
    split <;> cases column.notNull <;> simp)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseIndexedType_append typ _ (by cases column.notNull <;> simp)]
  simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
  cases hn : column.notNull <;> cases np : column.notNullConflict <;>
    cases pp : column.primaryConflict <;>
    simp_all [parseNullPolicy, parseExplicitPrimary, notNullConflictChars, explicitPrimaryChars,
      stripPrefix, Option.bind_eq_bind, Option.bind]

theorem parseKeyColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none)
    (separator : endsColumn rest = true) :
    parseKeyColumn (keyColumnChars column ++ rest) = some (column, rest) := by
  cases declared : column.indexedType with
  | none =>
      have parsed := parseLegacyKeyColumn_any_append column rest consistent exclusive noDefault declared separator
      have noTag : stripPrefix "/*sqleanite-key*/".toList (legacyKeyColumnChars column ++ rest) = none := by
        unfold legacyKeyColumnChars
        split <;> simp [plainColumnChars, baseColumnChars, quoteChars, stripPrefix]
      simp only [keyColumnChars, declared, parseKeyColumn]
      rw [noTag]
      exact parsed
  | some typ =>
      simp only [keyColumnChars, declared, List.append_assoc, parseKeyColumn]
      rw [stripPrefix_append]
      exact parseIndexedBody_append column typ rest declared exclusive noDefault

theorem keyColumnChars_noDefaultTag (column : Core.Column) (rest : List Char) :
    stripPrefix "/*sqleanite-default ".toList (keyColumnChars column ++ rest) = none := by
  cases declared : column.indexedType with
  | none =>
      simp only [keyColumnChars, declared, legacyKeyColumnChars]
      split <;> simp [plainColumnChars, baseColumnChars, quoteChars, stripPrefix]
  | some typ => simp [keyColumnChars, declared, stripPrefix]

theorem takeQuotedNat_quote (number : Nat) (rest : List Char)
    (boundary : rest.head? ≠ some '"') :
    takeQuotedNat (quoteChars (toString number) ++ rest) = some (number, rest) := by
  unfold takeQuotedNat quoteChars
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [takeIdent_escape _ _ boundary]
  simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
  change ((Nat.repr number).toNat?.bind (fun value => some (value, rest))) = _
  rw [Nat.toNat?_repr]
  rfl

theorem parseColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (separator : endsColumn rest = true) :
    parseColumn (columnChars column ++ rest) = some (column, rest) := by
  cases hd : column.defaultValue with
  | none =>
      have parsed := parseKeyColumn_any_append column rest consistent exclusive hd separator
      simp only [columnChars, hd, parseColumn]
      rw [keyColumnChars_noDefaultTag]
      exact parsed
  | some spec =>
      let base : Core.Column := { column with defaultValue := none }
      have parsed := parseKeyColumn_any_append base [] consistent exclusive rfl (by rfl)
      have restored : { base with defaultValue := some spec } = column := by cases column; simp_all [base]
      simp only [columnChars, hd, List.append_assoc, parseColumn, defaultHeader]
      rw [stripPrefix_append]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [takeQuotedNat_quote _ _ (by simp)]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [stripPrefix_append]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [takeQuotedNat_quote _ _ (by simp)]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [stripPrefix_append]
      simp only [Option.bind_eq_bind, Option.bind, List.take_left, List.drop_left]
      have p : parseKeyColumn (keyColumnChars base) = some (base, []) := by simpa using parsed
      rw [p]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [stripPrefix_append]
      simp only [Option.bind_eq_bind, Option.bind, List.take_left, List.drop_left, String.ofList_toList]
      rw [ColumnDefault.fromSource_spec]
      simp [stripPrefix, restored]

theorem parseColumns_append : (columns : List Core.Column) → (fuel : Nat) →
    (suffix : List Char) →
    columns ≠ [] → columns.length ≤ fuel →
    (∀ c ∈ columns, c.integerPrimaryKey = true →
      c.notNull = true) →
    (∀ c ∈ columns, c.integerPrimaryKey = true → c.textPrimaryKey = false) →
    parseColumns fuel (columnsChars columns ++ ')' :: suffix) =
      some (columns, ')' :: suffix)
  | [], _, _, h, _, _, _ => absurd rfl h
  | [c], fuel + 1, suffix, _, _, cons, exclusive => by
      have : columnsChars [c] = columnChars c := rfl
      rw [this]
      have step := parseColumn_any_append c
        (')' :: suffix)
        (cons c (by simp)) (exclusive c (by simp)) rfl
      simp only [parseColumns]
      rw [step]
      rfl
  | c :: d :: cs, fuel + 1, suffix, _, bound, cons, exclusive => by
      have expand : columnsChars (c :: d :: cs)
          = columnChars c ++ ',' :: columnsChars (d :: cs) := rfl
      rw [expand, List.append_assoc]
      have step := parseColumn_any_append c
        (',' :: (columnsChars (d :: cs) ++ ')' :: suffix))
        (cons c (by simp)) (exclusive c (by simp)) rfl
      simp only [parseColumns]
      rw [show ',' :: columnsChars (d :: cs) ++ ')' :: suffix
            = ',' :: (columnsChars (d :: cs) ++ ')' :: suffix) from rfl] at *
      rw [step]
      have tail := parseColumns_append (d :: cs) fuel suffix (by simp)
        (by simp at bound ⊢; omega)
        (fun x m => cons x (by simp [m]))
        (fun x m => exclusive x (by simp [m]))
      simp [tail]

theorem legacyKeyColumnChars_length_ge (column : Core.Column) : 1 ≤ (legacyKeyColumnChars column).length := by
  have plain (column : Core.Column) : 1 ≤ (plainColumnChars column).length := by
    simp [plainColumnChars, baseColumnChars, quoteChars]
  unfold legacyKeyColumnChars
  split
  · exact plain column
  · have enough := plain (primaryBase column)
    simp only [List.length_append]
    omega

theorem keyColumnChars_length_ge (column : Core.Column) : 1 ≤ (keyColumnChars column).length := by
  cases h : column.indexedType with
  | none => simpa [keyColumnChars, h] using legacyKeyColumnChars_length_ge column
  | some typ => simp [keyColumnChars, h]

theorem columnChars_length_ge (column : Core.Column) : 1 ≤ (columnChars column).length := by
  cases hd : column.defaultValue with
  | none => simpa [columnChars, hd] using keyColumnChars_length_ge column
  | some spec =>
      have enough := keyColumnChars_length_ge { column with defaultValue := none }
      simp only [columnChars, hd, List.length_append, List.length_singleton]
      omega

theorem columnsChars_length_ge : (columns : List Core.Column) →
    columns.length ≤ (columnsChars columns).length
  | [] => by simp [columnsChars]
  | [c] => by simpa [columnsChars] using columnChars_length_ge c
  | c :: d :: cs => by
      have ih := columnsChars_length_ge (d :: cs)
      have head := columnChars_length_ge c
      simp only [columnsChars, List.length_cons, List.length_append] at ih ⊢
      omega

theorem parseChars_tableChars (s : Core.Schema) (printable : Printable s) :
    parseChars (tableChars s) = some s := by
  have shape : tableChars s
      = "CREATE TABLE ".toList ++
        ('"' :: (escapeIdent s.name.toList ++ '"' ::
          ('(' :: (columnsChars s.catalogColumns ++ [')'])))) := by
    simp [tableChars, quoteChars]
  have body := parseColumns_append s.catalogColumns
    ((columnsChars s.catalogColumns ++ [')']).length + 1)
    []
    printable.nonempty
    (by have := columnsChars_length_ge s.columns; simp only [List.length_append,
          List.length_singleton];
        have catalog := columnsChars_length_ge s.catalogColumns
        omega)
    printable.primaryKeyNotNull
    (by
      intro column member integer
      have catalogShape := printable.catalogShape
      unfold Core.Schema.CatalogShape at catalogShape
      split at catalogShape
      · have noInteger := catalogShape.2.2.1
        rw [List.findIdx?_eq_none_iff] at noInteger
        have contradiction := noInteger column member
        rw [integer] at contradiction
        contradiction
      · have noText := catalogShape.2.2.2
        rw [List.findIdx?_eq_none_iff] at noText
        exact noText column member)
  simp only [List.length_append, List.length_singleton, List.length_nil,
    Nat.add_zero] at body
  have body' :
      parseColumns
        ((columnsChars s.catalogColumns).length + 1 + 1)
        (columnsChars s.catalogColumns ++ [')']) =
        some (s.catalogColumns, [')']) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using body
  rw [shape]
  unfold parseChars
  rw [stripPrefix_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [takeIdent_escape s.name.toList
    ('(' :: (columnsChars s.catalogColumns ++ [')'])) (by simp)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show (columnsChars s.catalogColumns ++ [')']).length + 1 =
    (columnsChars s.catalogColumns).length + 1 + 1 by simp]
  rw [body']
  simp only [Option.bind_eq_bind, Option.bind]
  have catalogShape := printable.catalogShape
  unfold Core.Schema.CatalogShape at catalogShape
  split at catalogShape
  · rw [catalogShape.2.2.1]
    simp only
    simp only [String.ofList_toList]
    apply congrArg some
    congr
    · exact catalogShape.1.symm
    · exact catalogShape.2.1.symm
    · rw [catalogShape.2.2.2.2]
      have width : s.columns.length = s.catalogColumns.length + 1 := by
        rw [catalogShape.1]
        simp
      rw [width]
  · rw [catalogShape.2.2.1]
    simp only
    simp only [String.ofList_toList]
    apply congrArg some
    congr
    · exact catalogShape.1
    · exact catalogShape.2.1.symm

end SQLeanite.CanonicalSchemaSQL
