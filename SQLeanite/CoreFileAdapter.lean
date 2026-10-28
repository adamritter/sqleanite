import SQLeanite.CoreFileAdapter.Paths
import SQLeanite.CoreFileAdapter.AddLocalizedHeaderWriteBaseMem
import SQLeanite.CoreFileAdapter.PreadPageSource
import SQLeanite.CoreFileAdapter.ByteArrayPageSourceEqStorageImage
import SQLeanite.CoreFileAdapter.IOIndexPageMutationsPageSource
import SQLeanite.CoreFileAdapter.MutationPageWrites
import SQLeanite.CoreFileAdapter.PreparePageDirectedIndexInsert
import SQLeanite.CoreFileAdapter.PrimaryJoinLookup
import SQLeanite.CoreFileAdapter.RowsForExpectedIndexEntries
import SQLeanite.CoreFileAdapter.LookupGeneratedIndexCandidates

/-! Compatibility import for the responsibility modules above. -/

/-! ## Page-directed generated-index deletion -/
