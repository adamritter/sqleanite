import SQLeanite.CoreSQLGrammar.LiteralSyntax
import SQLeanite.CoreSQLGrammar.JoinComparisonOperandsOfSuccess

/-! Compatibility import for the responsibility modules above. -/

/-!
# Declarative grammar for the verified Core SQL surface

`CoreSQL` is executable translation code.  This module gives its accepted AST
forms an independent, inductive description.  The propositions erase at
runtime; the accompanying theorems show that successful live translations
cannot escape the advertised grammar without breaking a proof.
-/
