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

Working in `List Char` rather than `String` is deliberate: `String.mk` and
`String.data` are inverse definitionally, so no string reasoning is needed.

`Printable` contains only structural schema facts. Identifier text is arbitrary:
the printer uses SQLite's doubled-quote convention and the inverse proof covers
embedded quotes and separators.
-/

namespace SQLeanite.CanonicalSchemaSQL

/-- The structural conditions needed to recover exactly the schema that was
printed. Identifier text itself is unrestricted: `quoteChars` escapes quotes. -/
structure Printable (schema : Core.Schema) : Prop where
  nonempty : schema.columns ≠ []
  primaryKeyIndex : schema.columns.findIdx? (·.integerPrimaryKey) = some schema.primaryKey
  primaryKeyNotNull : ∀ column ∈ schema.columns, column.integerPrimaryKey → column.notNull

theorem Printable.ofWellFormed (schema : Core.Schema)
    (wellFormed : schema.WellFormed) : Printable schema := by
  refine {
    nonempty := ?_
    primaryKeyIndex := wellFormed.2.2.2.2.2.1
    primaryKeyNotNull := wellFormed.2.2.2.2.2.2 }
  intro empty
  have := wellFormed.2.1
  simp [empty] at this

/-! ## Printer -/

def escapeIdent : List Char → List Char
  | [] => []
  | '"' :: rest => '"' :: '"' :: escapeIdent rest
  | character :: rest => character :: escapeIdent rest

def quoteChars (name : String) : List Char := '"' :: escapeIdent name.data ++ ['"']

def columnSuffix (column : Core.Column) : List Char :=
  if column.integerPrimaryKey then " INTEGER PRIMARY KEY".data
  else if column.notNull then " NOT NULL".data
  else []

def columnChars (column : Core.Column) : List Char :=
  quoteChars column.name ++ columnSuffix column

def columnsChars : List Core.Column → List Char
  | [] => []
  | [column] => columnChars column
  | column :: columns => columnChars column ++ ',' :: columnsChars columns

def tableChars (schema : Core.Schema) : List Char :=
  "CREATE TABLE ".data ++ quoteChars schema.name ++
    '(' :: columnsChars schema.columns ++ [')']

def print (schema : Core.Schema) : String := String.mk (tableChars schema)

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

/-- Terminators that end a column with no suffix. -/
def endsColumn : List Char → Bool
  | [] => true
  | ',' :: _ => true
  | ')' :: _ => true
  | _ => false

def parseColumn : List Char → Option (Core.Column × List Char)
  | '"' :: rest => do
      let (name, afterName) ← takeIdent rest
      if endsColumn afterName then
        some ({ name := String.mk name, notNull := false,
                integerPrimaryKey := false }, afterName)
      else
        match stripPrefix " INTEGER PRIMARY KEY".data afterName with
        | some tail =>
            some ({ name := String.mk name, notNull := true,
                    integerPrimaryKey := true }, tail)
        | none =>
          match stripPrefix " NOT NULL".data afterName with
          | some tail =>
              some ({ name := String.mk name, notNull := true,
                      integerPrimaryKey := false }, tail)
          | none => none
  | _ => none

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
  let afterKeyword ← stripPrefix "CREATE TABLE ".data input
  match afterKeyword with
  | '"' :: rest => do
      let (name, afterName) ← takeIdent rest
      match afterName with
      | '(' :: afterParen => do
          let (columns, tail) ← parseColumns (afterParen.length + 1) afterParen
          match tail with
          | [')'] => do
              let primaryKey ← columns.findIdx? (·.integerPrimaryKey)
              some { name := String.mk name, columns, primaryKey }
          | _ => none
      | _ => none
  | _ => none

def parse (sql : String) : Option Core.Schema := parseChars sql.data

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
    stripPrefix " NOT NULL".data
      (' ' :: 'N' :: 'O' :: 'T' :: ' ' :: 'N' :: 'U' :: 'L' :: 'L' :: rest)
      = some rest := rfl

theorem stripPrefix_ipk_miss (rest : List Char) :
    stripPrefix " INTEGER PRIMARY KEY".data
      (' ' :: 'N' :: 'O' :: 'T' :: ' ' :: 'N' :: 'U' :: 'L' :: 'L' :: rest)
      = none := rfl

theorem stripPrefix_ipk_cons (rest : List Char) :
    stripPrefix " INTEGER PRIMARY KEY".data
      (' ' :: 'I' :: 'N' :: 'T' :: 'E' :: 'G' :: 'E' :: 'R' :: ' ' :: 'P' :: 'R'
        :: 'I' :: 'M' :: 'A' :: 'R' :: 'Y' :: ' ' :: 'K' :: 'E' :: 'Y' :: rest)
      = some rest := rfl

theorem parseColumn_append (columnName : String) (columnNotNull columnPrimary : Bool)
    (rest : List Char)
    (consistent : columnPrimary = true → columnNotNull = true)
    (separator : endsColumn rest = true) :
    parseColumn (columnChars ⟨columnName, columnNotNull, columnPrimary⟩ ++ rest)
      = some (⟨columnName, columnNotNull, columnPrimary⟩, rest) := by
  cases columnPrimary <;> cases columnNotNull
  · have shape : columnChars (⟨columnName, false, false⟩ : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.data ++ '"' :: rest) := by
      simp [columnChars, quoteChars, columnSuffix]
    rw [shape]; simp only [parseColumn]; rw [takeIdent_escape _ _ (by
      intro leadingQuote
      cases rest with
      | nil => simp at leadingQuote
      | cons character rest =>
          have : character = '"' := by simpa using leadingQuote
          subst character
          simp [endsColumn] at separator)]
    simp [separator]
  · have shape : columnChars (⟨columnName, true, false⟩ : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.data ++ '"' :: (" NOT NULL".data ++ rest)) := by
      simp [columnChars, quoteChars, columnSuffix]
    rw [shape]; simp only [parseColumn]; rw [takeIdent_escape _ _ (by simp)]
    simp [endsColumn, stripPrefix]
  · exact absurd (consistent rfl) (by simp)
  · have shape : columnChars (⟨columnName, true, true⟩ : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.data ++ '"' :: (" INTEGER PRIMARY KEY".data ++ rest)) := by
      simp [columnChars, quoteChars, columnSuffix]
    rw [shape]; simp only [parseColumn]; rw [takeIdent_escape _ _ (by simp)]
    simp [endsColumn, stripPrefix]

theorem parseColumns_append : (columns : List Core.Column) → (fuel : Nat) →
    columns ≠ [] → columns.length ≤ fuel →
    (∀ c ∈ columns, c.integerPrimaryKey = true → c.notNull = true) →
    parseColumns fuel (columnsChars columns ++ [')']) = some (columns, [')'])
  | [], _, h, _, _ => absurd rfl h
  | [c], fuel + 1, _, _, cons => by
      have : columnsChars [c] = columnChars c := rfl
      rw [this]
      have step := parseColumn_append c.name c.notNull c.integerPrimaryKey [')']
        (cons c (by simp)) rfl
      simp only [parseColumns]
      rw [show (⟨c.name, c.notNull, c.integerPrimaryKey⟩ : Core.Column) = c from rfl] at step
      rw [step]
      rfl
  | c :: d :: cs, fuel + 1, _, bound, cons => by
      have expand : columnsChars (c :: d :: cs)
          = columnChars c ++ ',' :: columnsChars (d :: cs) := rfl
      rw [expand, List.append_assoc]
      have step := parseColumn_append c.name c.notNull c.integerPrimaryKey
        (',' :: (columnsChars (d :: cs) ++ [')']))
        (cons c (by simp)) rfl
      rw [show (⟨c.name, c.notNull, c.integerPrimaryKey⟩ : Core.Column) = c from rfl] at step
      simp only [parseColumns]
      rw [show ',' :: columnsChars (d :: cs) ++ [')']
            = ',' :: (columnsChars (d :: cs) ++ [')']) from rfl] at *
      rw [step]
      have tail := parseColumns_append (d :: cs) fuel (by simp)
        (by simp at bound ⊢; omega)
        (fun x m => cons x (by simp [m]))
      simp [tail]

theorem columnsChars_length_ge : (columns : List Core.Column) →
    columns.length ≤ (columnsChars columns).length
  | [] => by simp [columnsChars]
  | [c] => by simp [columnsChars, columnChars, quoteChars]
  | c :: d :: cs => by
      have ih := columnsChars_length_ge (d :: cs)
      simp only [columnsChars, columnChars, quoteChars, List.length_cons,
        List.length_append, List.length_singleton, List.length_nil] at ih ⊢
      omega

theorem parseChars_tableChars (s : Core.Schema) (printable : Printable s) :
    parseChars (tableChars s) = some s := by
  have shape : tableChars s
      = "CREATE TABLE ".data ++
        ('"' :: (escapeIdent s.name.data ++ '"' ::
          ('(' :: (columnsChars s.columns ++ [')'])))) := by
    simp [tableChars, quoteChars]
  have body := parseColumns_append s.columns ((columnsChars s.columns ++ [')']).length + 1)
    printable.nonempty
    (by have := columnsChars_length_ge s.columns; simp only [List.length_append,
          List.length_singleton]; omega)
    printable.primaryKeyNotNull
  simp only [List.length_append, List.length_singleton] at body
  rw [shape]
  unfold parseChars
  rw [stripPrefix_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [takeIdent_escape s.name.data
    ('(' :: (columnsChars s.columns ++ [')'])) (by simp)]
  simp [body, printable.primaryKeyIndex]

end SQLeanite.CanonicalSchemaSQL
