import SQLeanite.WidePageTree.LeafCapacity
import SQLeanite.WidePageTree.NumberedBranchesRootNePendingBytePage
import SQLeanite.WidePageTree.AppendStepToList

/-! Compatibility import for the responsibility modules above. -/

/-!
# High-fanout physical page topology

The logical ordered-map development uses a 2-3 tree because its branching
proofs are compact.  A physical SQLite interior page must not inherit that
branching factor: a 4096-byte page can hold hundreds of four-byte child
pointers and nine-byte worst-case integer separators.  Materializing each
logical 2-3 node as one disk page made roughly half of every database consist
of almost-empty interior pages.

This module is the replacement physical topology.  Leaves contain one
page-budgeted chunk, while an interior node contains up to 256
children.  The builder is total, preserves the exact entry sequence at every
level, and exposes the bounds needed by the SQLite page encoder.  Stable page
identity and localized mutation are layered on this plan in the subsequent
migration step; there is deliberately no second byte encoder here.
-/

/-! ## Stable page identities

`Plan` is the proof-facing bulk topology.  The live store below gives every
page a persistent identity.  Bulk construction allocates leaves first and
then one contiguous interval for each interior layer; consequently the root
is the last allocated page, not an artificial page placed before its
children.  SQLite permits that layout, and later mutations can keep the root
identity fixed without renumbering an unchanged sibling.
-/

/-! ## Byte-selected interior fanout

Table separators are fixed-width rowids, so `interiorFanout` is exact there.
Index separators are promoted records whose byte widths depend on the indexed
value.  The generic builder below lets the index codec select a smaller, proved
page-fitting fanout without returning to a 2-3 physical topology. -/

/-! ## Linear admission of ordered entry streams

`List.Pairwise` is the proof-facing invariant, but its generic decision
procedure checks every pair.  For a transitive key order, adjacent comparisons
are equivalent and linear.  Validating open uses this decision procedure so a
million-row image does not pay a quadratic proof-construction tax. -/

/-! ## Local right-spine insertion

SQLite rowids allocated by the Core are strictly increasing.  Appending the
new terminal chunk therefore needs one right-spine descent, not a comparison
against every existing chunk.  A full leaf splits into two leaves; a full
interior page splits into two pages and propagates one level upward. -/

/-! ## Identity-preserving terminal replacement

Appending a row usually changes the last byte-budgeted chunk rather than
creating a new chunk.  This operation rewrites exactly the right spine and
keeps every page identity.  Its theorem exposes both the removed terminal
entry and the exact replacement sequence, so callers never validate the
result by flattening and comparing the complete table. -/
