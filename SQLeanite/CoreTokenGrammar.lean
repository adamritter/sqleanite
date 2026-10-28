import SQLeanite.CoreTokenGrammar.Significant
import SQLeanite.CoreTokenGrammar.MatchExpr
import SQLeanite.CoreTokenGrammar.MatchColumnConstraints
import SQLeanite.CoreTokenGrammar.MatchInsertPrefix

/-! Compatibility import for the responsibility modules above. -/

/-!
# Independent concrete grammar for the live Core SQL surface

The broad compatibility parser proposes an AST.  This module does not call any
of its recursive-descent routines: it independently replays the significant
token stream against that exact AST.  Consequently a successful certificate
checks names, literal values, operator-tree precedence, delimiters, statement
boundaries, aliases, joins, and transaction commands rather than trusting the
parser's final equation.

The checker is intentionally narrower than the compatibility parser.  Syntax
which the verified Core cannot execute is rejected here and remains available
only to the legacy conformance fixture.
-/
