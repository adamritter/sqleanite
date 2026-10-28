import SQLeanite.CoreLocalizedRepresentation.PageSourceContainsUpdateStateTreeExtension

namespace SQLeanite
namespace CoreLocalizedRepresentation

/-- Insert a changed table, including its separately allocated overflow run,
directly into the database-wide table certificate.  This is the final
list-level composition step: callers no longer have to restate the decoder
equation produced by `decodeTableFrom_applyWrites`. -/
theorem TablesDecode.consOverflowEncoded
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (entry : CoreDecode.CatalogEntry)
    (entries : List CoreDecode.CatalogEntry)
    (state : CoreChunkPageState.TableState) (tables : List Core.Table)
    (entryExact : entry = CoreDecode.CatalogEntry.ofEncoded
      (CorePageCodec.chunkTableCatalogEntry state))
    (nextOverflow : Nat) (encoding : CorePageCodec.OverflowEncoding)
    (encoded : CorePageCodec.encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (accounted : ∀ numbered ∈ encoding.treePages,
      (∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) ∨
      (0 < numbered.pageNumber ∧
        numbered.pageNumber ≤ image.pageCount ∧
        (CorePageSource.ofStorageImage image).readPage numbered.pageNumber =
          some numbered.page.bytes ∧
        ∀ write ∈ writes, write.pageId + 1 ≠ numbered.pageNumber))
    (overflowContains : CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      nextOverflow encoding.overflowPages)
    (heightBound : state.tree.root.erase.height <
      (GrowableStorage.applyWrites image writes).pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length <
      (GrowableStorage.applyWrites image writes).pageCount + 1)
    (tail : TablesDecode
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) entries tables) :
    TablesDecode
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      (entry :: entries) (state.table :: tables) := by
  subst entry
  exact .cons
    (decodeTableFrom_applyWrites image writes distinct state nextOverflow
      encoding encoded accounted overflowContains heightBound nextPositive
      pageBound fuelBound)
    tail

end CoreLocalizedRepresentation

end SQLeanite
