import SQLeanite.PersistentPageTree.PageId
import SQLeanite.PersistentPageTree.NodeInsertStepDonePathAgrees
import SQLeanite.PersistentPageTree.StoreReuseFreshGetDRootId
import SQLeanite.PersistentPageTree.NodeDeleteCandidateRootId

/-! Compatibility import for the responsibility modules above. -/

/-!
# Stable page identities for the recursive B+ tree

`RecursiveBPlusTree` proves the logical insertion and deletion algorithms.  This
module adds the piece a persistent database needs but a purely functional tree
does not: stable page identities.  The erasure map deliberately forgets only
those identities, so the executable page mutation and the previously proved
tree algorithm cannot silently diverge.
-/

/-! ## Stable-identity deletion

The logical 2-3 tree already implements borrow, merge, underflow propagation,
and root shrink.  The following algorithm is the same state machine with page
identities threaded through every constructor.  Parent IDs remain parent IDs;
an absorbed interior page is returned in the freed-page list. -/
