import SQLeanite.CoreWideIndex.Cell
import SQLeanite.CoreWideIndex.PromoteChildrenToCells
import SQLeanite.CoreWideIndex.IndexRowsInline
import SQLeanite.CoreWideIndex.DecodeCanonicalIndexesForTableEncodeIndexes

/-! Compatibility import for the responsibility modules above. -/

/-!
# High-fanout physical index pages

SQLite index interior cells are promoted records, not synthetic separators.
This module therefore cannot reuse the table encoder verbatim: construction
starts with page-packed leaves, gives them the same 256-way physical topology,
then removes the greatest record from every non-rightmost child and stores that
record in its parent.  `Node.toCells` includes those promoted records exactly
once.
-/
