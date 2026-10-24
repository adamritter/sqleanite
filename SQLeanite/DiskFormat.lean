import SQLeanite.PageFormat

namespace SQLeanite
namespace DiskFormat

open FileFormat

/-- The pager dimensions discovered from a validated SQLite database header.
The current physical subset has no reserved tail, so `usable.val` is both the
usable and serialized page size. -/
structure DatabaseGeometry where
  usable : UsablePageSize
  pageCount : Nat
  header : ValidDatabaseHeader usable pageCount
  deriving DecidableEq

def decodeDatabaseGeometry (input : List UInt8) :
    Option (DatabaseGeometry × List UInt8) := do
  let (header, suffix) ← decodeDatabaseHeader input
  let pageSize := header.headerPrefix.pageSize
  let pageCount := header.databaseSizePages.val
  if minimum : 480 ≤ pageSize then
    if maximum : pageSize ≤ 65536 then
      let usable : UsablePageSize := ⟨pageSize, minimum, maximum⟩
      if valid : header.WellFormedFor usable pageCount then
        some (⟨usable, pageCount, ⟨header, valid⟩⟩, suffix)
      else
        none
    else
      none
  else
    none

theorem decodeDatabaseGeometry_encode (geometry : DatabaseGeometry)
    (suffix : List UInt8) :
    decodeDatabaseGeometry
      (encodeDatabaseHeader geometry.header.header ++ suffix) =
        some (geometry, suffix) := by
  rcases geometry with ⟨usable, pageCount, header⟩
  rcases usable with ⟨pageSize, minimum, maximum⟩
  rcases header with ⟨header, wellFormed⟩
  unfold decodeDatabaseGeometry
  rw [decodeDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  have pageSizeEq : header.headerPrefix.pageSize = pageSize := by
    have total := wellFormed.2.1
    have noReserved := wellFormed.2.2.2.2.2.2.2.2.2.2
    simp [noReserved] at total
    exact total
  have pageCountEq : header.databaseSizePages.val = pageCount := wellFormed.2.2.1
  subst pageSize
  subst pageCount
  simp only [dif_pos minimum, dif_pos maximum, dif_pos wellFormed]

def sizedBytesToPage {pageSize : Nat}
    (bytes : SizedBytes pageSize) : Storage.Page pageSize := {
  bytes := bytes.bytes.toArray
  sizeInvariant := by simp [bytes.length_eq] }

def pageToSizedBytes {pageSize : Nat}
    (page : Storage.Page pageSize) : SizedBytes pageSize := {
  bytes := page.bytes.toList
  length_eq := by simpa using page.sizeInvariant }

theorem sizedBytesToPage_pageToSizedBytes {pageSize : Nat}
    (page : Storage.Page pageSize) :
    sizedBytesToPage (pageToSizedBytes page) = page := by
  cases page with
  | mk bytes sizeInvariant =>
      simp [sizedBytesToPage, pageToSizedBytes]

def decodeStoragePage (pageSize : Nat) (input : List UInt8) :
    Option (Storage.Page pageSize × List UInt8) := do
  let (bytes, suffix) ← decodeSizedBytes pageSize input
  some (sizedBytesToPage bytes, suffix)

theorem decodeStoragePage_encode {pageSize : Nat}
    (page : Storage.Page pageSize) (suffix : List UInt8) :
    decodeStoragePage pageSize (page.bytes.toList ++ suffix) =
      some (page, suffix) := by
  unfold decodeStoragePage
  rw [show page.bytes.toList = (pageToSizedBytes page).bytes by rfl]
  rw [decodeSizedBytes_append]
  simp only [Option.bind_eq_bind, Option.bind, sizedBytesToPage_pageToSizedBytes]

theorem decodeStoragePage_sound {pageSize : Nat} {input suffix : List UInt8}
    {page : Storage.Page pageSize}
    (decoded : decodeStoragePage pageSize input = some (page, suffix)) :
    input = page.bytes.toList ++ suffix := by
  unfold decodeStoragePage at decoded
  cases bytesResult : decodeSizedBytes pageSize input with
  | none => simp [bytesResult] at decoded
  | some result =>
      rcases result with ⟨bytes, remaining⟩
      rw [bytesResult] at decoded
      simp only [Option.bind_eq_bind, Option.bind] at decoded
      have pairEquality := Option.some.inj decoded
      injection pairEquality with pageEquality suffixEquality
      subst page
      subst suffix
      rw [decodeSizedBytes_sound bytesResult]
      simp [sizedBytesToPage]

structure SizedPages (pageSize pageCount : Nat) where
  pages : List (Storage.Page pageSize)
  length_eq : pages.length = pageCount

def encodePages {pageSize : Nat} :
    List (Storage.Page pageSize) → List UInt8
  | [] => []
  | page :: pages => page.bytes.toList ++ encodePages pages

def decodeSizedPages (pageSize : Nat) : (pageCount : Nat) → List UInt8 →
    Option (SizedPages pageSize pageCount × List UInt8)
  | 0, input => some (⟨[], rfl⟩, input)
  | pageCount + 1, input => do
    let (page, afterPage) ← decodeStoragePage pageSize input
    let (pages, suffix) ← decodeSizedPages pageSize pageCount afterPage
    some (⟨page :: pages.pages, by simp [pages.length_eq]⟩, suffix)

theorem decodeSizedPages_encode {pageSize pageCount : Nat}
    (pages : SizedPages pageSize pageCount) (suffix : List UInt8) :
    decodeSizedPages pageSize pageCount (encodePages pages.pages ++ suffix) =
      some (pages, suffix) := by
  rcases pages with ⟨pages, length_eq⟩
  induction pages generalizing pageCount with
  | nil =>
      simp only [List.length_nil] at length_eq
      subst pageCount
      rfl
  | cons page pages induction =>
      cases pageCount with
      | zero => simp at length_eq
      | succ pageCount =>
          simp only [List.length_cons, Nat.succ.injEq] at length_eq
          unfold encodePages
          rw [List.append_assoc]
          unfold decodeSizedPages
          rw [decodeStoragePage_encode]
          simp only [Option.bind_eq_bind, Option.bind]
          let tail : SizedPages pageSize pageCount := ⟨pages, length_eq⟩
          have decodedTail :
              decodeSizedPages pageSize pageCount (encodePages pages ++ suffix) =
                some (tail, suffix) := induction length_eq
          rw [decodedTail]

theorem decodeSizedPages_sound {pageSize pageCount : Nat}
    {input suffix : List UInt8} {pages : SizedPages pageSize pageCount}
    (decoded : decodeSizedPages pageSize pageCount input = some (pages, suffix)) :
    input = encodePages pages.pages ++ suffix := by
  induction pageCount generalizing input suffix with
  | zero =>
      simp only [decodeSizedPages] at decoded
      have pairEquality := Option.some.inj decoded
      injection pairEquality with pagesEquality suffixEquality
      subst pages
      subst suffix
      rfl
  | succ pageCount induction =>
      unfold decodeSizedPages at decoded
      cases pageResult : decodeStoragePage pageSize input with
      | none => simp [pageResult] at decoded
      | some result =>
          rcases result with ⟨page, afterPage⟩
          rw [pageResult] at decoded
          simp only [Option.bind_eq_bind, Option.bind] at decoded
          cases pagesResult : decodeSizedPages pageSize pageCount afterPage with
          | none => simp [pagesResult] at decoded
          | some result =>
              rcases result with ⟨tail, remaining⟩
              rw [pagesResult] at decoded
              simp only [Option.bind_eq_bind, Option.bind] at decoded
              have pairEquality := Option.some.inj decoded
              injection pairEquality with pagesEquality suffixEquality
              subst pages
              subst suffix
              rw [decodeStoragePage_sound pageResult, induction pagesResult]
              simp [encodePages, List.append_assoc]

def diskToSizedPages {pageSize pageCount : Nat}
    (disk : Storage.Disk pageSize pageCount) : SizedPages pageSize pageCount := {
  pages := List.ofFn disk.read
  length_eq := by simp }

def SizedPages.toDisk {pageSize pageCount : Nat}
    (pages : SizedPages pageSize pageCount) : Storage.Disk pageSize pageCount := {
  read := fun pageId => pages.pages.get ⟨pageId.val, by simp [pages.length_eq]⟩ }

theorem SizedPages.toDisk_diskToSizedPages {pageSize pageCount : Nat}
    (disk : Storage.Disk pageSize pageCount) : (diskToSizedPages disk).toDisk = disk := by
  cases disk with
  | mk read =>
      have sameRead :
          (diskToSizedPages (Storage.Disk.mk read)).toDisk.read = read := by
        funext pageId
        simp [diskToSizedPages, SizedPages.toDisk]
      change Storage.Disk.mk _ = Storage.Disk.mk read
      exact congrArg (fun diskRead => Storage.Disk.mk diskRead) sameRead

def encodeDisk {pageSize pageCount : Nat}
    (disk : Storage.Disk pageSize pageCount) : List UInt8 :=
  encodePages (diskToSizedPages disk).pages

theorem encodeDisk_starts_with_first_page {pageSize pageCount : Nat}
    (disk : Storage.Disk pageSize pageCount) (positive : 0 < pageCount) :
    ∃ remainingPages,
      encodeDisk disk =
        (disk.read ⟨0, positive⟩).bytes.toList ++ remainingPages := by
  cases pageCount with
  | zero => omega
  | succ pageCount =>
      unfold encodeDisk
      change ∃ remainingPages,
        encodePages (List.ofFn disk.read) =
          (disk.read ⟨0, positive⟩).bytes.toList ++ remainingPages
      rw [List.ofFn_succ]
      unfold encodePages
      exact ⟨encodePages (List.ofFn fun i => disk.read i.succ), rfl⟩

def decodeDisk (pageSize pageCount : Nat) (input : List UInt8) :
    Option (Storage.Disk pageSize pageCount × List UInt8) := do
  let (pages, suffix) ← decodeSizedPages pageSize pageCount input
  some (pages.toDisk, suffix)

/-- A physical database image whose dependent pager dimensions were obtained
from its SQLite header rather than supplied by an external caller. -/
structure DatabaseImage where
  geometry : DatabaseGeometry
  disk : Storage.Disk geometry.usable.val geometry.pageCount

def decodeDatabaseImage (input : List UInt8) :
    Option (DatabaseImage × List UInt8) := do
  let (geometry, _) ← decodeDatabaseGeometry input
  let (disk, suffix) ←
    decodeDisk geometry.usable.val geometry.pageCount input
  some (⟨geometry, disk⟩, suffix)

def DatabaseImage.encode (image : DatabaseImage) : List UInt8 :=
  encodeDisk image.disk

/-- A semantic image invariant: the header stored in the dependent geometry
is the actual prefix of the physical pager bytes. -/
def DatabaseImage.HeaderEncoded (image : DatabaseImage) : Prop :=
  ∃ afterHeader,
    image.encode =
      encodeDatabaseHeader image.geometry.header.header ++ afterHeader

def verifiedDatabaseImage {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedDatabasePageSet usable pageCount)
    (old : Storage.Disk usable.val pageCount) : DatabaseImage := {
  geometry := {
    usable
    pageCount
    header := ⟨pages.firstPage.databaseHeader,
      pages.firstPage.headerWellFormed⟩ }
  disk := Storage.applyWrites old pages.writes }

theorem verifiedDatabaseImage_headerEncoded
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedDatabasePageSet usable pageCount)
    (old : Storage.Disk usable.val pageCount) :
    (verifiedDatabaseImage pages old).HeaderEncoded := by
  let materialized := Storage.applyWrites old pages.writes
  have starts := encodeDisk_starts_with_first_page materialized
    pages.firstPage.headerWellFormed.2.2.2.1
  rcases starts with ⟨remainingPages, starts⟩
  have firstPageRead :
      materialized.read
          ⟨0, pages.firstPage.headerWellFormed.2.2.2.1⟩ =
        pages.firstPage.encodePage := by
    simpa [materialized, DatabaseFirstPage.toPageWrite] using pages.applyWrites_read_first old
  have pageSplit :
      pages.firstPage.encodePage.bytes.toList =
        encodeDatabaseHeader pages.firstPage.databaseHeader ++
          pages.firstPage.encodePage.bytes.toList.drop 100 := by
    rw [← pages.firstPage.encodePage_take_header]
    exact (List.take_append_drop 100
      pages.firstPage.encodePage.bytes.toList).symm
  let pageTail := pages.firstPage.encodePage.bytes.toList.drop 100
  refine ⟨pageTail ++ remainingPages, ?_⟩
  change encodeDisk materialized =
    encodeDatabaseHeader pages.firstPage.databaseHeader ++
      (pageTail ++ remainingPages)
  calc
    encodeDisk materialized =
        (materialized.read
          ⟨0, pages.firstPage.headerWellFormed.2.2.2.1⟩).bytes.toList ++
            remainingPages := starts
    _ = pages.firstPage.encodePage.bytes.toList ++ remainingPages := by
      rw [firstPageRead]
    _ = (encodeDatabaseHeader pages.firstPage.databaseHeader ++ pageTail) ++
          remainingPages := by rw [show pages.firstPage.encodePage.bytes.toList =
        encodeDatabaseHeader pages.firstPage.databaseHeader ++ pageTail by
          simpa [pageTail] using pageSplit]
    _ = encodeDatabaseHeader pages.firstPage.databaseHeader ++
          (pageTail ++ remainingPages) := List.append_assoc _ _ _

theorem decodeDisk_encode {pageSize pageCount : Nat}
    (disk : Storage.Disk pageSize pageCount) (suffix : List UInt8) :
    decodeDisk pageSize pageCount (encodeDisk disk ++ suffix) =
      some (disk, suffix) := by
  unfold encodeDisk decodeDisk
  rw [decodeSizedPages_encode]
  simp only [Option.bind_eq_bind, Option.bind, SizedPages.toDisk_diskToSizedPages]

theorem decodeDatabaseImage_encode (image : DatabaseImage)
    (headerEncoded : image.HeaderEncoded) (suffix : List UInt8) :
    decodeDatabaseImage (image.encode ++ suffix) = some (image, suffix) := by
  rcases image with ⟨geometry, disk⟩
  rcases headerEncoded with ⟨afterHeader, encoding⟩
  change encodeDisk disk =
    encodeDatabaseHeader geometry.header.header ++ afterHeader at encoding
  have decodedGeometry :
      decodeDatabaseGeometry (encodeDisk disk ++ suffix) =
        some (geometry, afterHeader ++ suffix) := by
    rw [encoding, List.append_assoc]
    exact decodeDatabaseGeometry_encode geometry (afterHeader ++ suffix)
  unfold DatabaseImage.encode decodeDatabaseImage
  rw [decodedGeometry]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeDisk_encode]

theorem decodeVerifiedDatabaseImage_encode
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedDatabasePageSet usable pageCount)
    (old : Storage.Disk usable.val pageCount) (suffix : List UInt8) :
    decodeDatabaseImage ((verifiedDatabaseImage pages old).encode ++ suffix) =
      some (verifiedDatabaseImage pages old, suffix) :=
  decodeDatabaseImage_encode (verifiedDatabaseImage pages old)
    (verifiedDatabaseImage_headerEncoded pages old) suffix

theorem encodeDisk_injective {pageSize pageCount : Nat} :
    ∀ {left right : Storage.Disk pageSize pageCount},
      encodeDisk left = encodeDisk right → left = right := by
  intro left right equalEncoding
  have equalDecoding := congrArg (decodeDisk pageSize pageCount) equalEncoding
  have decodeLeft := decodeDisk_encode left []
  have decodeRight := decodeDisk_encode right []
  simp only [List.append_nil] at decodeLeft decodeRight
  rw [decodeLeft, decodeRight] at equalDecoding
  exact congrArg Prod.fst (Option.some.inj equalDecoding)

theorem encodePages_length {pageSize : Nat}
    (pages : List (Storage.Page pageSize)) :
    (encodePages pages).length = pageSize * pages.length := by
  induction pages with
  | nil => rfl
  | cons page pages induction =>
      simp [encodePages, page.sizeInvariant, induction, Nat.mul_add, Nat.add_comm]

theorem encodeDisk_length {pageSize pageCount : Nat}
    (disk : Storage.Disk pageSize pageCount) :
    (encodeDisk disk).length = pageSize * pageCount := by
  rw [encodeDisk, encodePages_length]
  simp [diskToSizedPages]

theorem decodeDisk_consumes {pageSize pageCount : Nat}
    {input suffix : List UInt8} {disk : Storage.Disk pageSize pageCount}
    (decoded : decodeDisk pageSize pageCount input = some (disk, suffix)) :
    input.length = pageSize * pageCount + suffix.length := by
  unfold decodeDisk at decoded
  cases pagesResult : decodeSizedPages pageSize pageCount input with
  | none => simp [pagesResult] at decoded
  | some result =>
      rcases result with ⟨pages, remaining⟩
      rw [pagesResult] at decoded
      simp only [Option.bind_eq_bind, Option.bind] at decoded
      have pairEquality := Option.some.inj decoded
      injection pairEquality with diskEquality suffixEquality
      subst disk
      subst suffix
      rw [decodeSizedPages_sound pagesResult]
      simp [encodePages_length, pages.length_eq]

theorem decodeDatabaseImage_consumes {input suffix : List UInt8}
    {image : DatabaseImage}
    (decoded : decodeDatabaseImage input = some (image, suffix)) :
    input.length = image.geometry.usable.val * image.geometry.pageCount +
      suffix.length := by
  unfold decodeDatabaseImage at decoded
  cases geometryResult : decodeDatabaseGeometry input with
  | none => simp [geometryResult] at decoded
  | some result =>
      rcases result with ⟨geometry, afterHeader⟩
      rw [geometryResult] at decoded
      simp only [Option.bind_eq_bind, Option.bind] at decoded
      cases diskResult : decodeDisk geometry.usable.val geometry.pageCount input with
      | none => simp [diskResult] at decoded
      | some result =>
          rcases result with ⟨disk, remaining⟩
          rw [diskResult] at decoded
          simp only [Option.bind_eq_bind, Option.bind] at decoded
          have pairEquality := Option.some.inj decoded
          injection pairEquality with imageEquality suffixEquality
          subst image
          subst suffix
          exact decodeDisk_consumes diskResult

/-- The page-level rollback theorem remains old-or-new after serialization to
the exact contiguous bytes of a SQLite database file. -/
theorem verifiedDatabasePageSet_serialized_crash_atomic
    {usable : FileFormat.UsablePageSize} {pageCount : Nat}
    (pages : FileFormat.VerifiedDatabasePageSet usable pageCount)
    (old : Storage.Disk usable.val pageCount) (phase : Storage.CommitPhase)
    (recoveredMain : Storage.Disk usable.val pageCount)
    (recoveredJournal : Option (Storage.Disk usable.val pageCount))
    (outcome : Storage.JournaledCrashOutcome
      (Storage.rollbackCommitState old pages.writes phase)
      recoveredMain recoveredJournal) :
    encodeDisk (Storage.recoverWithJournal recoveredMain recoveredJournal) =
        encodeDisk old ∨
      encodeDisk (Storage.recoverWithJournal recoveredMain recoveredJournal) =
        encodeDisk (Storage.applyWrites old pages.writes) := by
  rcases pages.rollbackCommit_crash_atomic old phase recoveredMain
      recoveredJournal outcome with oldState | newState
  · left
    exact congrArg encodeDisk oldState
  · right
    exact congrArg encodeDisk newState

end DiskFormat
end SQLeanite
