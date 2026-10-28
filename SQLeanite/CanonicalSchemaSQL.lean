import SQLeanite.CanonicalSchemaSQL.Printable
import SQLeanite.CanonicalSchemaSQL.StripPrefixNotNullEnd
import SQLeanite.CanonicalSchemaSQL.ParseExplicitPrimaryAppend

/-! Compatibility import for the responsibility modules above. -/

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

/-! ## Printer -/

/-! ## Recognizer -/

/-! ## The inverse proof -/
