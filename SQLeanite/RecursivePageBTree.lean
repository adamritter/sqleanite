import SQLeanite.RecursivePageBTree.Plan
import SQLeanite.RecursivePageBTree.PlanEncodePagesFrom
import SQLeanite.RecursivePageBTree.IndexPlanInsertAtToCells
import SQLeanite.RecursivePageBTree.IndexPlanReplaceCellsBalanced
import SQLeanite.RecursivePageBTree.IndexStore
import SQLeanite.RecursivePageBTree.EncodeIndexRefines

/-! Compatibility import for the responsibility modules above. -/

/-!
# Arbitrary-depth SQLite table-page plans

This module is the physical refinement layer between a sequence of already
encoded table cells and SQLite's page graph.  Leaves retain the page-sized
chunks produced by `CellPagination`; interior pages form a capacity-three
2-3 tree.  Page allocation is preorder and every child reference is derived
from `pageCount`, rather than accepted as an unchecked integer.
-/

/-! ## Recursive physical index trees -/
