import SQLeanite.CorePageLoad.LoadFreelist
import SQLeanite.CorePageLoad.RetargetOpenTablesWithoutIndexes

/-! Compatibility import for the responsibility modules above. -/

/-!
# Recovering the proof-carrying representation from physical pages

This loader accepts the binary 2-3-tree shape emitted by `CorePageCodec` and
also accepts compatible externally modified files.  Wider SQLite interior
pages return `none`; callers then retain the general decoder and bulk-commit
fallback.  Successful construction rechecks both the recursive tree invariant
and the exact abstraction equation in Lean before manufacturing any proof
field.
-/
