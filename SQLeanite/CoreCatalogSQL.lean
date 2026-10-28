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

def checks (sql : String) : Except String (List CheckDef) := do
  let some statements := CoreSchemaSQL.statements sql | throw "invalid CHECK catalog source"
  let (name, columns, constraints) ← match statements.toList with
    | [.createTable name columns constraints _] | [.createStrictTable name columns constraints _] => pure (name, columns, constraints)
    | _ => throw "invalid CHECK table source"
  return (CoreCheck.collect columns constraints).map fun check =>
    { check with expression := CoreCollationSyntax.forTable name columns check.expression }

def foreignKeys (sql : String) : Except String (List (Nat × ForeignKeyDef)) := do
  let some statements := CoreSchemaSQL.statements sql | throw "invalid foreign-key catalog source"
  let (columns, constraints) ← match statements.toList with
    | [.createTable _ columns constraints _] | [.createStrictTable _ columns constraints _] => pure (columns, constraints)
    | _ => throw "invalid foreign-key table source"
  CoreForeignKeySyntax.collect columns constraints

def strictColumns (sql : String) : Except String (Option (List CoreStrictSyntax.Spec)) := do
  let some statements := CoreSchemaSQL.statements sql | throw "invalid STRICT catalog source"
  match statements.toList with
  | [.createTable ..] => pure none
  | [.createStrictTable name columns _ _] => some <$> CoreStrictSyntax.specs name columns
  | _ => throw "invalid STRICT table source"

def generatedColumns (schema : Core.Schema) (sql : String) : Except String (List CoreGeneratedSyntax.Spec) := do
  let some statements := CoreSchemaSQL.statements sql | throw "invalid generated-column catalog source"
  match statements.toList with
  | [.createTable _ columns constraints _] | [.createStrictTable _ columns constraints _] =>
      CoreGeneratedSyntax.compile schema columns constraints
  | _ => throw "invalid generated-column table source"

def collations (sql : String) : Except String (List CoreCollationSyntax.Spec) := do
  let some parsed := CoreSchemaSQL.statements sql | throw "invalid collation catalog source"
  match parsed.toList with
  | [.createTable _ columns _ _] | [.createStrictTable _ columns _ _] => return CoreCollationSyntax.collect columns
  | _ => throw "invalid collation table source"

structure Source (schema : Core.Schema) where
  text : String
  decoded : parse text = some schema
  noncanonical : text ≠ CanonicalSchemaSQL.print schema
  /-- Compile once when retaining the catalog, rather than reparsing per row. -/
  compiledChecks : Except String (List CheckDef)
  checks_eq : compiledChecks = checks text
  compiledForeignKeys : Except String (List (Nat × ForeignKeyDef))
  foreignKeys_eq : compiledForeignKeys = foreignKeys text
  compiledStrictColumns : Except String (Option (List CoreStrictSyntax.Spec))
  strictColumns_eq : compiledStrictColumns = strictColumns text
  compiledGeneratedColumns : Except String (List CoreGeneratedSyntax.Spec)
  generatedColumns_eq : compiledGeneratedColumns = generatedColumns schema text
  compiledCollations : Except String (List CoreCollationSyntax.Spec)
  collations_eq : compiledCollations = collations text

def retain (schema : Core.Schema) (text : String)
    (decoded : parse text = some schema) : Option (Source schema) :=
  if equal : text = CanonicalSchemaSQL.print schema then none
  else some ⟨text, decoded, equal, checks text, rfl, foreignKeys text, rfl, strictColumns text, rfl, generatedColumns schema text, rfl, collations text, rfl⟩

theorem retain_compiledChecks {schema : Core.Schema} {sql : String}
    {decoded : parse sql = some schema} {source : Source schema}
    (retained : retain schema sql decoded = some source) : source.compiledChecks = checks sql := by
  unfold retain at retained
  split at retained
  · contradiction
  · cases retained
    rfl

theorem retain_compiledForeignKeys {schema : Core.Schema} {sql : String}
    {decoded : parse sql = some schema} {source : Source schema}
    (retained : retain schema sql decoded = some source) :
    source.compiledForeignKeys = foreignKeys sql := by
  unfold retain at retained
  split at retained
  · contradiction
  · cases retained
    rfl

theorem retain_compiledStrictColumns {schema : Core.Schema} {sql : String}
    {decoded : parse sql = some schema} {source : Source schema}
    (retained : retain schema sql decoded = some source) :
    source.compiledStrictColumns = strictColumns sql := by
  unfold retain at retained
  split at retained
  · contradiction
  · cases retained
    rfl

theorem retain_compiledGeneratedColumns {schema : Core.Schema} {sql : String}
    {decoded : parse sql = some schema} {source : Source schema}
    (retained : retain schema sql decoded = some source) :
    source.compiledGeneratedColumns = generatedColumns schema sql := by
  unfold retain at retained
  split at retained
  · contradiction
  · cases retained
    rfl

theorem retain_compiledCollations {schema : Core.Schema} {sql : String}
    {decoded : parse sql = some schema} {source : Source schema}
    (retained : retain schema sql decoded = some source) : source.compiledCollations = collations sql := by
  unfold retain at retained
  split at retained
  · contradiction
  · cases retained
    rfl

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
  | some source =>
      cases source with
      | mk sql parsed noncanonical compiled equal compiledForeign foreignEqual compiledStrict strictEqual compiledGenerated generatedEqual compiledCollations collationsEqual =>
          subst compiled
          subst compiledForeign
          subst compiledStrict
          subst compiledGenerated
          subst compiledCollations
          simp [retain, text, noncanonical]

end SQLeanite.CoreCatalogSQL
