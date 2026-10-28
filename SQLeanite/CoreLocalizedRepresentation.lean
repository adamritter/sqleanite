import SQLeanite.CoreLocalizedRepresentation.TableOnSource
import SQLeanite.CoreLocalizedRepresentation.TablesOnSourceTablesDecode
import SQLeanite.CoreLocalizedRepresentation.AlignTablesIndexImagesNone
import SQLeanite.CoreLocalizedRepresentation.IndexGroupCertificatesEncodeIndexTableGroups
import SQLeanite.CoreLocalizedRepresentation.ExistsDatabaseOnSourceEncodeBulkIn
import SQLeanite.CoreLocalizedRepresentation.DatabaseOnSourceUpdateStateApplyWritesBelowExtension
import SQLeanite.CoreLocalizedRepresentation.PageSourceContainsUpdateStateTreeExtension
import SQLeanite.CoreLocalizedRepresentation.TablesDecodeConsOverflowEncoded

/-! Compatibility import for the responsibility modules above. -/

/-!
# Local page deltas preserve table decoding

These lemmas isolate the two physical facts needed by the live localized
writer.  A changed encoded page is read from its exact write, and an omitted
page is read from the represented old image.  The resulting containment
certificate feeds the existing recursive table-decoder refinement directly;
there is no decode-and-compare admission check.
-/
