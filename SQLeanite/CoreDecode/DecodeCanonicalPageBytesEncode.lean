import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.ValidateCanonicalIndexGroupsFromEncodeOverflowIndexTableGroups

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem decodeCanonicalPageBytes_encode (utf8 : UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CoreFile.encode database = some image) :
    decodeCanonicalPageBytes (image.pages.map CoreFile.Page.bytes) =
      some database.canonicalize := by
  have reencoded := encoded
  unfold CoreFile.encode at encoded
  cases tableResult : CoreFile.encodeTables 2 database.tables with
  | none => simp [tableResult] at encoded
  | some tableEncodings =>
    simp only [tableResult, Option.bind_eq_bind, Option.bind] at encoded
    let layouts := CoreFile.tableLayoutsOf tableEncodings
    cases indexResult : CoreFile.encodeIndexTableGroups
        (CoreFile.indexRootBase layouts) database.tables with
    | none => simp [layouts, indexResult] at encoded
    | some indexEncodings =>
      simp only [layouts, indexResult] at encoded
      let tableEntries := CoreFile.tableEntries database layouts
      let indexEntries := CoreFile.indexEntriesOf indexEncodings
      let remaining := CoreFile.tablePagesOf tableEncodings ++
        CoreFile.indexPagesOf indexEncodings
      let total := 1 + remaining.length
      split at encoded
      next countFits =>
        let count : U32Value :=
          ⟨1 + (CoreFile.tablePagesOf tableEncodings ++
            CoreFile.indexPagesOf indexEncodings).length, countFits⟩
        cases schemaResult : CoreFile.schemaPageForEntries?
            (tableEntries ++ indexEntries) count with
        | none =>
          simp only [tableEntries, indexEntries, layouts, count] at schemaResult
          rw [schemaResult] at encoded
          contradiction
        | some schemaPage =>
          simp only [tableEntries, indexEntries, layouts, count] at schemaResult
          rw [schemaResult] at encoded
          simp only [Option.bind_eq_bind, Option.bind] at encoded
          injection encoded with equal
          subst image
          have safe : ∀ entry ∈ tableEntries ++ indexEntries,
              CatalogTextRoundtrips entry := by
            intro entry _
            exact ⟨utf8 entry.kind, utf8 entry.name,
              utf8 entry.table, utf8 entry.sql⟩
          have catalogDecoded := decodeCanonicalCatalog_schemaPageForEntries
            (tableEntries ++ indexEntries) count safe schemaResult
          have splitDecoded := encodedCatalogKinds tableEntries indexEntries
            (fun entry member => CoreFile.tableEntriesFor_kind
              database.tables layouts entry member)
            (fun entry member => CoreFile.indexEntriesOf_kind
              indexEncodings entry member)
          have tablesDecoded := decodeCanonicalTables_encodeTables 2
            database.tables tableEncodings
            ((CoreFile.indexPagesOf indexEncodings).map CoreFile.Page.bytes)
            tableResult
          have databaseDecoded := rebuildCanonicalDatabase_encoded database
            (CoreFile.indexRootBase layouts) indexEncodings indexResult
          have canonicalPages := CoreFile.encode_canonicalize_pages database
          rw [reencoded] at canonicalPages
          cases canonicalResult : CoreFile.encode database.canonicalize with
          | none => simp [canonicalResult] at canonicalPages
          | some canonicalImage =>
            rw [canonicalResult] at canonicalPages
            change some canonicalImage.pages = some
              (schemaPage :: (CoreFile.tablePagesOf tableEncodings ++
                CoreFile.indexPagesOf indexEncodings)) at canonicalPages
            injection canonicalPages with canonicalPagesEqual
            unfold decodeCanonicalPageBytes
            simp only [List.map_cons, List.getElem?_cons_zero,
              Option.bind_eq_bind, Option.bind]
            rw [catalogDecoded]
            simp only
            rw [splitDecoded]
            simp only [Prod.fst, Prod.snd]
            simp only [List.tail_cons, tableEntries, indexEntries, layouts,
              CoreFile.tableEntries]
            unfold CoreFile.tableEntries at tablesDecoded
            simp only [CoreFile.tablePagesOf, CoreFile.indexPagesOf,
              List.map_append] at tablesDecoded ⊢
            rw [tablesDecoded]
            simp only [Option.bind_eq_bind, Option.bind]
            simp only [CoreFile.indexEntriesOf, List.map_map,
              Function.comp_apply]
            rw [show indexEncodings.map
                (CatalogEntry.ofEncoded ∘ fun encoding => encoding.catalogEntry) =
                indexEncodings.map (fun encoding =>
                  CatalogEntry.ofEncoded encoding.catalogEntry) by rfl]
            rw [databaseDecoded]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [canonicalResult]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [dif_pos (by
              rw [canonicalPagesEqual]
              simp [CoreFile.tablePagesOf, CoreFile.indexPagesOf])]
      next countTooLarge => contradiction

theorem pages_length (count : Nat) (input : List UInt8) :
    (pages count input).length = count := by
  induction count generalizing input with
  | zero => rfl
  | succ count induction => simp [pages, induction]

theorem pages_flatten : (chunks : List (List UInt8)) →
    (∀ chunk ∈ chunks, chunk.length = PhysicalCodec.pageSize) →
    pages chunks.length chunks.flatten = chunks
  | [], _ => rfl
  | chunk :: chunks, sized => by
      have headSize := sized chunk (by simp)
      have tailSize : ∀ candidate ∈ chunks,
          candidate.length = PhysicalCodec.pageSize := by
        intro candidate member
        exact sized candidate (by simp [member])
      simp only [List.flatten_cons, List.length_cons, pages]
      rw [show (chunk ++ chunks.flatten).take PhysicalCodec.pageSize = chunk by
        rw [← headSize]
        simp]
      rw [show (chunk ++ chunks.flatten).drop PhysicalCodec.pageSize =
          chunks.flatten by
        rw [← headSize]
        simp]
      rw [pages_flatten chunks tailSize]

theorem pages_image (image : CoreFile.Image) :
    pages image.pageCount image.fileBytes = image.pages.map CoreFile.Page.bytes := by
  unfold CoreFile.Image.pageCount CoreFile.Image.fileBytes
  rw [show image.pages.flatMap CoreFile.Page.bytes =
      (image.pages.map CoreFile.Page.bytes).flatten by
    simp [List.flatMap]]
  have sized : ∀ bytes ∈ image.pages.map CoreFile.Page.bytes,
      bytes.length = PhysicalCodec.pageSize := by
    intro bytes member
    simp only [List.mem_map] at member
    rcases member with ⟨page, _, rfl⟩
    exact page.length_eq
  simpa using pages_flatten (image.pages.map CoreFile.Page.bytes) sized

/-- Byte-string entry point for the strict canonical decoder. The database
header determines the page count; logical decoding plus exact re-encoding in
`decodeCanonicalPageBytes` validates every page. -/
def decodeCanonicalFile (input : List UInt8) : Option Core.Database := do
  let (header, _) ← decodeDatabaseHeader input
  let count := header.databaseSizePages.val
  if _fileLength : input.length = count * PhysicalCodec.pageSize then
    decodeCanonicalPageBytes (pages count input)
  else none

theorem decodeCanonicalFile_encode (utf8 : UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CoreFile.encode database = some image) :
    decodeCanonicalFile image.fileBytes = some database.canonicalize := by
  rcases CoreFile.encode_header encoded with
    ⟨count, schema, remaining, body, pagesEqual, countEqual, headerEqual⟩
  have bytesLayout : image.fileBytes =
      encodeDatabaseHeader (CoreFile.databaseHeader count) ++
        (body ++ remaining.flatMap CoreFile.Page.bytes) := by
    unfold CoreFile.Image.fileBytes
    rw [pagesEqual]
    simp only [List.flatMap_cons]
    rw [headerEqual]
    simp [List.append_assoc]
  have fileLength : image.fileBytes.length =
      count.val * PhysicalCodec.pageSize := by
    rw [CoreFile.Image.fileBytes_length, countEqual, Nat.mul_comm]
  have splitPages : pages count.val image.fileBytes =
      image.pages.map CoreFile.Page.bytes := by
    rw [← countEqual]
    exact pages_image image
  unfold decodeCanonicalFile
  rw [bytesLayout, decodeDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show (CoreFile.databaseHeader count).databaseSizePages.val = count.val
    from rfl]
  rw [← bytesLayout]
  rw [dif_pos fileLength]
  rw [splitPages]
  exact decodeCanonicalPageBytes_encode utf8 database image encoded

end CoreDecode

end SQLeanite
