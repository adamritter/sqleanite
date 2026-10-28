import SQLeanite.RelationalAlgebra.Relation
import SQLeanite.RelationalAlgebra.OfListWhereRows
import SQLeanite.RelationalAlgebra.CoreGroupOutputValueRefines
import SQLeanite.RelationalAlgebra.JoinedLeftOuterRowsEval
import SQLeanite.RelationalAlgebra.SelectLeftOuterLeftEval

/-! Compatibility import for the responsibility modules above. -/

/-!
# Typed multiplicity-valued relational algebra

This is the general algebra layer beneath optimizer rewrites.  Every expression
denotes a `KRelation.Relation`, so duplicate behavior is explicit in `Nat`
rather than inherited accidentally from a list implementation.  Products,
selection, projection, set operations, renaming/permutation, grouping and left
outer join are constructors; an inner join is derived as selection over a
product.
-/
