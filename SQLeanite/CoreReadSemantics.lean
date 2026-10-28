import SQLeanite.CoreReadSemantics.CoreRow
import SQLeanite.CoreReadSemantics.ReorderValuesInvertSymm

/-! Compatibility import for the responsibility modules above. -/

/-!
# Live Core reads and multiplicity semantics

This module is deliberately compositional.  It does not define another query
evaluator.  It connects the live `Core.execute` results to the independently
defined `KRelation` bag algebra, while retaining list equality for SQLite's
observable `ORDER BY`/`LIMIT` suffix.
-/

/-! ## POPL'10 permutation parity, on the live read path

`RelationalAlgebra.permute_eval` and `permute_symm_eval` establish that the
algebra has POPL'10's permutation operator. On their own they say nothing about
the shipped executor: they are theorems about a standalone module that the live
read path never mentions.

What follows closes that. A live `Core.Query` projects by a list of column
indices; reordering that list is a column permutation. These lemmas prove the
reordered live projection *is* `RelationalAlgebra.permute` applied to the
unreordered one, on the denotation both are observed through -- so the parity
claim becomes a claim about `Core.execute`.
-/
