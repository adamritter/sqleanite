import SQLeanite.PhysicalTableBTree

namespace SQLeanite
namespace PhysicalMultiPageCodec

open FileFormat
open PhysicalCodec
open PhysicalTableBTree

/-!
# Growable SQLite image encoder for the physical MVP table tree

This module replaces the fixed two-page geometry at the codec boundary.  The
schema root remains page one and points at table root page two.  A one-leaf
tree therefore has two pages; a split tree stores its interior root on page two
and its leaves consecutively from page three.
-/

def filePageCount (tree : Tree) : Nat :=
  if tree.leaves.length = 1 then 2 else tree.leaves.length + 2

theorem filePageCount_pos (tree : Tree) : 0 < filePageCount tree := by
  unfold filePageCount
  split <;> omega

theorem filePageCountFits (tree : Tree) :
    filePageCount tree < 2 ^ 32 := by
  unfold filePageCount
  split
  · decide
  · exact tree.pageCountFits

def databaseHeader (tree : Tree) : DatabaseHeader :=
  { PhysicalCodec.databaseHeader with
    databaseSizePages := ⟨filePageCount tree, filePageCountFits tree⟩ }

theorem databaseHeader_wellFormed (tree : Tree) :
    (databaseHeader tree).WellFormedFor PhysicalCodec.usablePageSize
      (filePageCount tree) := by
  have base := PhysicalCodec.databaseHeader_wellFormed
  unfold DatabaseHeader.WellFormedFor at base ⊢
  rcases base with
    ⟨validPageSize, usableMatches, _oldCount, _oldPositive,
      writeVersion, readVersion, schemaLower, schemaUpper,
      encodingLower, encodingUpper, noReserved⟩
  unfold databaseHeader
  exact ⟨validPageSize, usableMatches, rfl, filePageCount_pos tree,
    writeVersion, readVersion, schemaLower, schemaUpper,
    encodingLower, encodingUpper, noReserved⟩

def geometry (tree : Tree) : DiskFormat.DatabaseGeometry := {
  usable := PhysicalCodec.usablePageSize
  pageCount := filePageCount tree
  header := ⟨databaseHeader tree, databaseHeader_wellFormed tree⟩ }

/-- The page-one B-tree body is independent of the database page count.  It is
reused from the already roundtripped fixed codec; only the 100-byte database
header is regenerated. -/
def schemaPageBody : List UInt8 := PhysicalCodec.schemaPageBytes.drop 100

theorem schemaPageBody_length :
    schemaPageBody.length = PhysicalCodec.pageSize - 100 := by
  unfold schemaPageBody
  rw [List.length_drop, PhysicalCodec.schemaPageBytes_length]

def schemaPageBytes (tree : Tree) : List UInt8 :=
  encodeDatabaseHeader (databaseHeader tree) ++ schemaPageBody

theorem schemaPageBytes_length (tree : Tree) :
    (schemaPageBytes tree).length = PhysicalCodec.pageSize := by
  unfold schemaPageBytes
  rw [List.length_append, encodeDatabaseHeader_length,
    schemaPageBody_length]
  simp [PhysicalCodec.pageSize]

def schemaPage (tree : Tree) : Storage.Page PhysicalCodec.pageSize := {
  bytes := (schemaPageBytes tree).toArray
  sizeInvariant := by simp [schemaPageBytes_length] }

def pages (tree : Tree) : List (Storage.Page PhysicalCodec.pageSize) :=
  schemaPage tree :: tree.tablePages

theorem pages_length (tree : Tree) :
    (pages tree).length = filePageCount tree := by
  rw [pages, List.length_cons, tree.tablePages_length]
  unfold filePageCount
  split <;> omega

def disk (tree : Tree) :
    Storage.Disk PhysicalCodec.pageSize (filePageCount tree) := {
  read := fun pageId => (pages tree).get ⟨pageId.val, by
    rw [pages_length]
    exact pageId.isLt⟩ }

def image (tree : Tree) : DiskFormat.DatabaseImage := {
  geometry := geometry tree
  disk := disk tree }

theorem disk_read_first (tree : Tree) :
    (disk tree).read ⟨0, filePageCount_pos tree⟩ = schemaPage tree := by
  simp [disk, pages]

theorem image_headerEncoded (tree : Tree) : (image tree).HeaderEncoded := by
  have starts := DiskFormat.encodeDisk_starts_with_first_page (image tree).disk
    (filePageCount_pos tree)
  rcases starts with ⟨remaining, starts⟩
  refine ⟨schemaPageBody ++ remaining, ?_⟩
  change DiskFormat.encodeDisk (disk tree) =
    encodeDatabaseHeader (databaseHeader tree) ++
      (schemaPageBody ++ remaining)
  calc
    DiskFormat.encodeDisk (disk tree) =
        ((disk tree).read ⟨0, filePageCount_pos tree⟩).bytes.toList ++
          remaining := starts
    _ = (schemaPage tree).bytes.toList ++ remaining := by
      rw [disk_read_first]
    _ = schemaPageBytes tree ++ remaining := by
      simp [schemaPage]
    _ = (encodeDatabaseHeader (databaseHeader tree) ++ schemaPageBody) ++
          remaining := by rfl
    _ = encodeDatabaseHeader (databaseHeader tree) ++
          (schemaPageBody ++ remaining) := List.append_assoc _ _ _

def fileBytes (tree : Tree) : List UInt8 := (image tree).encode

theorem fileBytes_length (tree : Tree) :
    (fileBytes tree).length = PhysicalCodec.pageSize * filePageCount tree := by
  exact DiskFormat.encodeDisk_length (image tree).disk

theorem decodeDatabaseImage_fileBytes (tree : Tree) :
    DiskFormat.decodeDatabaseImage (fileBytes tree) = some (image tree, []) := by
  simpa [fileBytes] using
    DiskFormat.decodeDatabaseImage_encode (image tree) (image_headerEncoded tree) []

def decodeLeafPages {physicalPageSize : Nat} : List (Storage.Page physicalPageSize) →
    Option (List PhysicalCodec.Row)
  | [] => some []
  | page :: pages => do
      let database ← PhysicalCodec.decodeDataPage page.bytes.toList
      let rows ← decodeLeafPages pages
      some (database.rows ++ rows)

theorem decodeLeafPages_dataPages (databases : List PhysicalCodec.Database) :
    decodeLeafPages (databases.map PhysicalCodec.Database.dataPage) =
      some (databases.flatMap PhysicalCodec.Database.rows) := by
  induction databases with
  | nil => rfl
  | cons database databases induction =>
      simp only [List.map_cons, decodeLeafPages]
      change (PhysicalCodec.decodeDataPage database.dataPageBytes).bind _ = _
      rw [PhysicalCodec.decodeDataPage_encode]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [induction]
      rfl

theorem decodeLeafPages_tree (tree : Tree) :
    decodeLeafPages tree.leafStoragePages = some tree.database.rows := by
  rw [Tree.leafStoragePages, decodeLeafPages_dataPages]
  rw [show tree.leafDatabases.flatMap PhysicalCodec.Database.rows = tree.toList by
    exact tree.leafDatabases_flatten_rows]
  rw [tree.toList_eq]

def imagePages (databaseImage : DiskFormat.DatabaseImage) :
    List (Storage.Page databaseImage.geometry.usable.val) :=
  List.ofFn databaseImage.disk.read

theorem imagePages_image (tree : Tree) : imagePages (image tree) = pages tree := by
  apply List.ext_getElem
  · simp only [imagePages, List.length_ofFn]
    exact (pages_length tree).symm
  · intro index leftBound rightBound
    simp [imagePages, image, disk, List.getElem_ofFn]
    rfl

/-- Select physical leaves from a decoded image.  Two pages means page two is
the root leaf; larger images reserve page two for the interior root.  Canonical
re-encoding below validates the root bytes and every child reference. -/
def physicalLeafPages (databaseImage : DiskFormat.DatabaseImage) :
    Option (List (Storage.Page databaseImage.geometry.usable.val)) :=
  if _two : databaseImage.geometry.pageCount = 2 then
    some (imagePages databaseImage |>.drop 1)
  else if _more : 2 < databaseImage.geometry.pageCount then
    some (imagePages databaseImage |>.drop 2)
  else none

theorem physicalLeafPages_image (tree : Tree) :
    physicalLeafPages (image tree) = some tree.leafStoragePages := by
  unfold physicalLeafPages
  rw [imagePages_image]
  by_cases single : tree.leaves.length = 1
  · have countTwo : (image tree).geometry.pageCount = 2 := by
      simp [image, geometry, filePageCount, single]
    rw [dif_pos countTwo]
    simp [pages, Tree.tablePages, single]
  · have countNotTwo : (image tree).geometry.pageCount ≠ 2 := by
      change (if tree.leaves.length = 1 then 2 else tree.leaves.length + 2) ≠ 2
      rw [if_neg single]
      have positive : 0 < tree.leaves.length :=
        List.length_pos_iff.mpr (by
          simpa [Tree.leaves] using paginateRows_nonempty tree.database.rows)
      omega
    rw [dif_neg countNotTwo]
    have more : 2 < (image tree).geometry.pageCount := by
      change 2 < (if tree.leaves.length = 1 then 2 else tree.leaves.length + 2)
      rw [if_neg single]
      have positive : 0 < tree.leaves.length :=
        List.length_pos_iff.mpr (by
          simpa [Tree.leaves] using paginateRows_nonempty tree.database.rows)
      omega
    rw [dif_pos more]
    simp [pages, Tree.tablePages, single]

def decodeImage (databaseImage : DiskFormat.DatabaseImage) :
    Option PhysicalCodec.Database := do
  if _pageSize : databaseImage.geometry.usable.val = PhysicalCodec.pageSize then
    let leaves ← physicalLeafPages databaseImage
    let rows ← decodeLeafPages leaves
    if sorted : rows.Pairwise PhysicalCodec.Row.keyLess then
      if fits : PhysicalCodec.PageFit 0 (rows.map PhysicalCodec.Row.encodeCell) then
        let database : PhysicalCodec.Database := ⟨rows, sorted, fits⟩
        let tree ← PhysicalTableBTree.build database
        if _canonical : fileBytes tree = databaseImage.encode then
          some database
        else none
      else none
    else none
  else none

def decodeFile (input : List UInt8) : Option PhysicalCodec.Database := do
  let (databaseImage, suffix) ← DiskFormat.decodeDatabaseImage input
  if _consumed : suffix = [] then decodeImage databaseImage else none

set_option maxHeartbeats 800000 in
theorem decodeImage_image (tree : Tree) :
    decodeImage (image tree) = some tree.database := by
  unfold decodeImage
  have pageSize : (image tree).geometry.usable.val = PhysicalCodec.pageSize := rfl
  rw [dif_pos pageSize]
  rw [physicalLeafPages_image]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeLeafPages_tree]
  simp only [tree.database.rowidsSorted, tree.database.pageFits, dif_pos]
  have rebuilt : PhysicalTableBTree.build tree.database = some tree := by
    unfold PhysicalTableBTree.build
    rw [dif_pos tree.pageCountFits]
    rcases tree.rootFits with single | rootFit
    · rw [dif_pos single]
    · by_cases single : (paginateRows tree.database.rows).length = 1
      · rw [dif_pos single]
      · rw [dif_neg single, dif_pos rootFit]
  rw [rebuilt]
  simp only [Option.bind_eq_bind, Option.bind]
  have canonical : fileBytes tree = (image tree).encode := rfl
  rw [dif_pos canonical]

theorem decodeFile_fileBytes (tree : Tree) :
    decodeFile (fileBytes tree) = some tree.database := by
  unfold decodeFile
  rw [decodeDatabaseImage_fileBytes]
  simp [decodeImage_image]

def storageImage (tree : Tree) : GrowableStorage.Image PhysicalCodec.pageSize := {
  pageCount := filePageCount tree
  read := fun pageId =>
    if within : pageId < filePageCount tree then
      (disk tree).read ⟨pageId, within⟩
    else schemaPage tree }

def storageBytes (storage : GrowableStorage.Image PhysicalCodec.pageSize) : List UInt8 :=
  DiskFormat.encodePages (List.ofFn fun pageId : Fin storage.pageCount =>
    storage.read pageId.val)

theorem storageBytes_storageImage (tree : Tree) :
    storageBytes (storageImage tree) = fileBytes tree := by
  unfold storageBytes storageImage fileBytes DiskFormat.DatabaseImage.encode
    DiskFormat.encodeDisk DiskFormat.diskToSizedPages
  apply congrArg DiskFormat.encodePages
  apply List.ext_getElem
  · simp [image, geometry]
  · intro index leftBound rightBound
    simp [disk, image, List.getElem_ofFn]

theorem storageBytes_eq_of_equiv
    {left right : GrowableStorage.Image PhysicalCodec.pageSize}
    (equivalent : left.Equiv right) :
    storageBytes left = storageBytes right := by
  rcases equivalent with ⟨countEqual, pagesEqual⟩
  rcases left with ⟨leftCount, leftRead⟩
  rcases right with ⟨rightCount, rightRead⟩
  dsimp only at countEqual pagesEqual ⊢
  subst rightCount
  unfold storageBytes
  apply congrArg DiskFormat.encodePages
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp only [List.getElem_ofFn]
    exact pagesEqual index (by simpa using leftBound)

def decodeStorageImage
    (storage : GrowableStorage.Image PhysicalCodec.pageSize) : Option PhysicalCodec.Database :=
  decodeFile (storageBytes storage)

theorem decodeStorageImage_equiv (tree : Tree)
    {storage : GrowableStorage.Image PhysicalCodec.pageSize}
    (equivalent : storage.Equiv (storageImage tree)) :
    decodeStorageImage storage = some tree.database := by
  unfold decodeStorageImage
  rw [storageBytes_eq_of_equiv equivalent, storageBytes_storageImage]
  exact decodeFile_fileBytes tree

def transactionWrites (tree : Tree) :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize) :=
  GrowableStorage.replaceWrites (storageImage tree)

theorem apply_transactionWrites_equiv (old new : Tree)
    (doesNotShrink : filePageCount old ≤ filePageCount new) :
    (GrowableStorage.applyWrites (storageImage old)
      (transactionWrites new)).Equiv (storageImage new) := by
  exact GrowableStorage.apply_replaceWrites_equiv _ _ doesNotShrink

/-- Concrete old-or-new recovery for a multi-page commit that preserves or
grows the file.  Shrinking is intentionally excluded until freed pages are
encoded in SQLite's freelist. -/
theorem rollbackCommit_database_crash_atomic (old new : Tree)
    (doesNotShrink : filePageCount old ≤ filePageCount new)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState (storageImage old)
        (transactionWrites new) phase)
      recoveredMain recoveredJournal) :
    decodeStorageImage
        (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal) =
          some old.database ∨
      decodeStorageImage
        (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal) =
          some new.database := by
  rcases GrowableStorage.rollbackCommit_crash_atomic (storageImage old)
    (transactionWrites new) phase recoveredMain recoveredJournal outcome with
    recoveredOld | recoveredWrites
  · exact .inl (decodeStorageImage_equiv old recoveredOld)
  · exact .inr (decodeStorageImage_equiv new
      (recoveredWrites.trans
        (apply_transactionWrites_equiv old new doesNotShrink)))

end PhysicalMultiPageCodec
end SQLeanite
