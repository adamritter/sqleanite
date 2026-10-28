import SQLeanite.CorePageCodec.NumberedPage
import SQLeanite.CorePageCodec.PhysicalChunkPagesFastEq
import SQLeanite.CorePageCodec.EncodeChangedChunkPagesSubset
import SQLeanite.CorePageCodec.InteriorChildrenInteriorPageTwo
import SQLeanite.CorePageCodec.DecodeTableInteriorEncodeChunkRootBranch2
import SQLeanite.CorePageCodec.EncodeChunkPathSubsetEncodeChunkNode
import SQLeanite.CorePageCodec.TableCellPlansNoOverflowEncodeCells
import SQLeanite.CorePageCodec.EncodeChunkTablesWithOverflow
import SQLeanite.CorePageCodec.DecodeSubtreeRowsFromEncodeChunkNodeWithOverflow
import SQLeanite.CorePageCodec.DecodeAbstractTableTreeFromEncodeChunkNodeWithOverflow
import SQLeanite.CorePageCodec.LookupTableRangeFromEncodeChunkNodeWithOverflowExact
import SQLeanite.CorePageCodec.LookupTableRowidFromEncodeChunkNodeWithOverflow
import SQLeanite.CorePageCodec.EncodeBulkFromState
import SQLeanite.CorePageCodec.PageSourceRepresentsEncodeBulkIn

/-! Compatibility import for the responsibility modules above. -/

/-! ## Physical page descriptors

`PersistentPageTree.Page` deliberately describes the generic 2-3 tree.  A
SQLite table interior cell additionally stores the greatest rowid reachable
through its left child.  The descriptor below records exactly the inputs that
determine one physical page, including that derived key.  It is therefore the
right equality notion for selecting a byte-exact localized write set. -/
