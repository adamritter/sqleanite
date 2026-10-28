import SQLeanite.CoreDurability.ImagePagesStorageImage
import SQLeanite.CoreDurability.SqliteHeaderMatchesStorageImageEncodeBulkFreelistEmpty
import SQLeanite.CoreDurability.CoreFileAdapterPreparedOrdinaryDeltaChangedTableOnFinalWritesIndexed
import SQLeanite.CoreDurability.CoreFileAdapterPreparedOrdinaryDeltaDatabaseOnFinalWritesIndexedInline
import SQLeanite.CoreDurability.CoreFileAdapterPreparedOrdinaryDeltaPostImageCertificateOfCommittedIndexedInline
import SQLeanite.CoreDurability.LocalizedRepresentationOfComponents
import SQLeanite.CoreDurability.RollbackCommitRepresentsRepeatedRecoveryAtomic

/-! Compatibility import for the responsibility modules above. -/

/-!
# Core database durability composition

This module is the missing lifting step between the growable page/journal
protocol and the canonical Core SQLite codec.  The protocol theorem speaks
about page-image equivalence; the results below turn that into an old-or-new
theorem about databases obtained by decoding the recovered bytes.
-/
