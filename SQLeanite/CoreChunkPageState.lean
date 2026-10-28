import SQLeanite.CoreChunkPageState.Chunk
import SQLeanite.CoreChunkPageState.TableStateBuildTable

/-! Compatibility import for the responsibility modules above. -/

/-!
# Packed proof-carrying table pages

The generic verified 2-3 tree stores *page chunks*, not individual rows.  This
keeps its small, fully proved branching algorithm while making physical page
count proportional to SQLite leaf capacity rather than row count.
`chunkCapacityFor` is the one-chunk page budget used by the high-fanout tree.
The retained 2-3 compatibility tree uses `legacyChunkCapacityFor`, since one of
its leaves may contain two chunks.  Both positive capacities are carried in
their proof-carrying table states.
-/
