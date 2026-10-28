import SQLeanite.SQLite.Scalar.TypedValues
import SQLeanite.SQLite.Scalar.RealResult
import SQLeanite.SQLite.Scalar.PrepareFuel
import SQLeanite.SQLite.Scalar.TestBetweenArgumentError

/-! Compatibility import for the responsibility modules above. -/

/-!
Pure SQLite scalar operations. Arithmetic/bit operations follow vdbe.c;
CAST follows vdbemem.c; the small built-in set follows func.c. The evaluator
uses the parsed expression tree instead of pretending to be a complete VDBE.
Column affinity is supplied by the row context; explicit expression collations
use the pinned built-in byte comparators.
-/
