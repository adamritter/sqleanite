import SQLeanite.CoreOptimizerBridge.ToSemantics
import SQLeanite.CoreOptimizerBridge.SymbolicLeftOnPlan

/-! Compatibility import for the responsibility modules above. -/

/-! ## Live Core join refinement

The live join executor has a richer predicate language than a single-table
query: either operand can be a left column, right column, or literal. The
definitions below embed that language exactly into `QuerySemantics`, construct
the corresponding inner-join plan, and prove the optimized denotation is the
same ordered list selected by `CoreJoin`. -/

/-! ## Representation-equality compound algebra

SQL numeric set equality is implemented and proved in `CoreCompound`. These
generic optimizer laws retain their representation-equality domain. -/
