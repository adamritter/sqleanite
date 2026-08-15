import SQLeanite.CorePageCodec
import SQLeanite.CoreMultiFreelist

namespace SQLeanite
namespace CoreFreelistCodec

/-- Extending a canonical bulk image with a verified SQLite freelist preserves
the logical database seen by the page-source decoder.  Active table and index
pages remain a prefix; only the database header and unreachable tail change. -/
theorem pageSourceRepresents_padded
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (layout : CoreMultiFreelist.Layout)
    (encoded : CorePageCodec.encodeBulk database = some layout.image) :
    CoreDecode.PageSourceRepresents
      (.ofList (layout.paddedImage.pages.map CoreFile.Page.bytes)) database := by
  let source : CoreDecode.PageSource :=
    .ofList (layout.paddedImage.pages.map CoreFile.Page.bytes)
  apply CorePageCodec.pageSourceRepresents_encodeBulk_in utf8 database
    layout.image encoded source
  · have catalogSame :=
      CorePageCodec.decodeCatalogForOpen_encodeBulk_replaceHeader utf8
        database layout.image encoded layout.firstPage layout.remainingActive
        layout.pages_eq
        (FileFormat.encodeDatabaseHeader layout.databaseHeader)
        (FileFormat.encodeDatabaseHeader_length layout.databaseHeader)
    have paddedFirst : source.readPage 1 = some layout.schemaPage.bytes := by
      simp [source, CoreDecode.PageSource.ofList, CoreDecode.page?,
        CoreMultiFreelist.Layout.paddedImage, CoreMultiFreelist.Layout.pages,
        CoreMultiFreelist.Layout.activePages]
    have canonicalFirst :
        (CoreDecode.PageSource.ofList
          (layout.image.pages.map CoreFile.Page.bytes)).readPage 1 =
            some layout.firstPage.bytes := by
      rw [layout.pages_eq]
      simp [CoreDecode.PageSource.ofList, CoreDecode.page?]
    rw [paddedFirst, canonicalFirst]
    simp only [Option.bind_eq_bind, Option.bind]
    simpa [CoreMultiFreelist.Layout.schemaPage] using catalogSame
  · rw [layout.pages_eq]
    have reads := CoreDecode.ReadsPagesFrom.ofList_append
      [layout.schemaPage.bytes] layout.remainingActive
      (layout.freelistPages.map CoreFile.Page.bytes)
    simpa [source, CoreMultiFreelist.Layout.paddedImage,
      CoreMultiFreelist.Layout.pages, CoreMultiFreelist.Layout.activePages,
      List.map_append] using reads
  · change layout.image.pageCount ≤
      (layout.paddedImage.pages.map CoreFile.Page.bytes).length
    rw [List.length_map]
    change layout.image.pageCount ≤ layout.pages.length
    rw [CoreMultiFreelist.Layout.pages_length]
    exact layout.active_le_total

theorem decodeFromPageSource_padded
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (layout : CoreMultiFreelist.Layout)
    (encoded : CorePageCodec.encodeBulk database = some layout.image) :
    CoreDecode.decodeFromPageSource
      (.ofList (layout.paddedImage.pages.map CoreFile.Page.bytes)) =
        some database.canonicalize :=
  (pageSourceRepresents_padded utf8 database layout encoded).decode

/-- Whole-file inverse for a freelist-padded live image.  This closes the
decoder gap on shrinking commits: the extra pages are valid freelist space,
not unexplained bytes, and reopening yields the exact canonical database. -/
theorem decode_paddedImage (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (layout : CoreMultiFreelist.Layout)
    (encoded : CorePageCodec.encodeBulk database = some layout.image) :
    CoreDecode.decode layout.paddedImage.fileBytes =
      some database.canonicalize := by
  have bytesLayout : layout.paddedImage.fileBytes =
      FileFormat.encodeDatabaseHeader layout.databaseHeader ++
        (layout.firstPage.bytes.drop 100 ++
          (layout.remainingActive ++ layout.freelistPages).flatMap
            CoreFile.Page.bytes) := by
    unfold CoreFile.Image.fileBytes
    simp [CoreMultiFreelist.Layout.paddedImage,
      CoreMultiFreelist.Layout.pages, CoreMultiFreelist.Layout.activePages,
      CoreMultiFreelist.Layout.schemaPage, List.flatMap_append,
      List.append_assoc]
  have fileLength : layout.paddedImage.fileBytes.length =
      layout.totalPageCount * PhysicalCodec.pageSize := by
    rw [CoreFile.Image.fileBytes_length,
      CoreMultiFreelist.Layout.paddedImage_pageCount, Nat.mul_comm]
  have splitPages :
      CoreDecode.pages layout.totalPageCount layout.paddedImage.fileBytes =
        layout.paddedImage.pages.map CoreFile.Page.bytes := by
    rw [← CoreMultiFreelist.Layout.paddedImage_pageCount]
    exact CoreDecode.pages_image layout.paddedImage
  unfold CoreDecode.decode
  rw [bytesLayout, FileFormat.decodeDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show layout.databaseHeader.databaseSizePages.val =
    layout.totalPageCount from rfl]
  rw [dif_pos (by rfl), dif_pos (by rfl), dif_pos (by rfl)]
  rw [← bytesLayout]
  rw [dif_pos fileLength, splitPages]
  exact decodeFromPageSource_padded utf8 database layout encoded

end CoreFreelistCodec
end SQLeanite
