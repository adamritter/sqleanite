import SQLeanite.CoreSchemaSQL

/-! Catalog text is observable database content. A retained source carries a
checked relation to its schema; arbitrary SQL cannot be attached to a table.
Canonical sources have a unique empty representation so encoding and decoding
remain exact, including the optional source metadata. -/
namespace SQLeanite.CoreCatalogSQL

def parse (sql : String) : Option Core.Schema :=
  match CanonicalSchemaSQL.parse sql with
  | some schema => some schema
  | none => CoreSchemaSQL.tableSchema sql

theorem parse_print (schema : Core.Schema)
    (printable : CanonicalSchemaSQL.Printable schema) :
    parse (CanonicalSchemaSQL.print schema) = some schema := by
  unfold parse CanonicalSchemaSQL.print CanonicalSchemaSQL.parse
  rw [String.toList_ofList,
    CanonicalSchemaSQL.parseChars_tableChars schema printable]

structure Source (schema : Core.Schema) where
  text : String
  decoded : parse text = some schema
  noncanonical : text ≠ CanonicalSchemaSQL.print schema

def retain (schema : Core.Schema) (text : String)
    (decoded : parse text = some schema) : Option (Source schema) :=
  if equal : text = CanonicalSchemaSQL.print schema then none
  else some ⟨text, decoded, equal⟩

def text (schema : Core.Schema) (source : Option (Source schema)) : String :=
  match source with
  | none => CanonicalSchemaSQL.print schema
  | some source => source.text

theorem parse_text (schema : Core.Schema)
    (printable : CanonicalSchemaSQL.Printable schema)
    (source : Option (Source schema)) :
    parse (text schema source) = some schema := by
  cases source with
  | none => exact parse_print schema printable
  | some source => exact source.decoded

theorem text_retain (schema : Core.Schema) (sql : String)
    (decoded : parse sql = some schema) :
    text schema (retain schema sql decoded) = sql := by
  unfold retain
  split
  next equal => exact equal.symm
  next => rfl

theorem retain_text (schema : Core.Schema) (source : Option (Source schema))
    (decoded : parse (text schema source) = some schema) :
    retain schema (text schema source) decoded = source := by
  cases source with
  | none => simp [retain, text]
  | some source => simp [retain, text, source.noncanonical]

end SQLeanite.CoreCatalogSQL
