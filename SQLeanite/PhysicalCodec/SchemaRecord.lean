import SQLeanite.Durability
import SQLeanite.GrowableStorage.RollbackCommitCrashAtomic
import SQLeanite.PhysicalCodec.PageSize

namespace SQLeanite
namespace PhysicalCodec
open FileFormat

private def schemaRecord : PhysicalRecord := {
  fields := [schemaType.recordField, schemaName.recordField,
    schemaName.recordField, .integer .eight rootPageInteger,
    schemaSQL.recordField]
  headerSizeBound := by
    have serialBound := encodeRecordSerialTypes_length_le
      [schemaType.recordField, schemaName.recordField,
        schemaName.recordField, .integer .eight rootPageInteger,
        schemaSQL.recordField]
    have headerBound := recordHeaderSize_le
      (encodeRecordSerialTypes [schemaType.recordField, schemaName.recordField,
        schemaName.recordField, .integer .eight rootPageInteger,
        schemaSQL.recordField]).length
    simp only [List.length_cons, List.length_nil] at serialBound
    omega }

private def schemaRowid : SignedInteger .eight :=
  ⟨1, by decide, by decide⟩

private theorem schemaRecord_encode_length_lt :
    schemaRecord.encode.length < pageSize := by
  rw [PhysicalRecord.encode_length]
  have headerValue : schemaRecord.headerSize.val = 6 := by decide
  have payloadValue : schemaRecord.encodePayload.length = 78 := by decide
  rw [headerValue, payloadValue]
  decide

def schemaCell : List UInt8 :=
  encodeVarint ⟨schemaRecord.encode.length, by
    have encodedLength := schemaRecord_encode_length_lt
    simp only [pageSize] at encodedLength
    omega⟩ ++
    encodeVarint (signedInteger64Bits schemaRowid) ++ schemaRecord.encode

theorem schemaPageFits : PageFit 100 [schemaCell] := by
  unfold PageFit schemaCell schemaRecord schemaType schemaName schemaSQL
  decide

def databaseHeader : DatabaseHeader := {
  headerPrefix := {
    pageSizeField := ⟨4096, by omega⟩
    writeVersion := 1
    readVersion := 1
    reservedSpace := 0
    changeCounter := ⟨1, by omega⟩ }
  databaseSizePages := ⟨2, by omega⟩
  firstFreelistTrunk := ⟨0, by omega⟩
  freelistPageCount := ⟨0, by omega⟩
  schemaCookie := ⟨1, by omega⟩
  schemaFormat := ⟨4, by omega⟩
  defaultPageCacheSize := ⟨0, by omega⟩
  largestRootBTreePage := ⟨0, by omega⟩
  textEncoding := ⟨1, by omega⟩
  userVersion := ⟨0, by omega⟩
  incrementalVacuum := ⟨0, by omega⟩
  applicationId := ⟨0, by omega⟩
  versionValidFor := ⟨1, by omega⟩
  sqliteVersion := ⟨3050004, by omega⟩ }

def usablePageSize : UsablePageSize :=
  ⟨pageSize, by decide, by decide⟩

theorem databaseHeader_wellFormed :
    databaseHeader.WellFormedFor usablePageSize 2 := by decide

def geometry : DiskFormat.DatabaseGeometry := {
  usable := usablePageSize
  pageCount := 2
  header := ⟨databaseHeader, databaseHeader_wellFormed⟩ }

def schemaPageBytes : List UInt8 :=
  encodeDatabaseHeader databaseHeader ++ leafPageBody 100 [schemaCell]

theorem schemaPageBytes_length : schemaPageBytes.length = pageSize := by
  unfold schemaPageBytes
  rw [List.length_append, encodeDatabaseHeader_length,
    leafPageBody_length 100 [schemaCell] schemaPageFits]
  simp [pageSize]

def schemaPage : Storage.Page pageSize := {
  bytes := schemaPageBytes.toArray
  sizeInvariant := by simp [schemaPageBytes_length] }

def Database.image (database : Database) : DiskFormat.DatabaseImage := {
  geometry
  disk := {
    read := fun pageId =>
      if pageId.val = 0 then schemaPage
      else database.dataPage } }

theorem Database.image_read_schema (database : Database) :
    (database.image.disk.read ⟨0, by
      simp [Database.image, geometry]⟩).bytes.toList = schemaPageBytes := by
  change schemaPageBytes.toArray.toList = schemaPageBytes
  exact List.toList_toArray

theorem Database.image_read_data (database : Database) :
    (database.image.disk.read ⟨1, by
      simp [Database.image, geometry]⟩).bytes.toList =
      database.dataPageBytes := by
  change database.dataPageBytes.toArray.toList = database.dataPageBytes
  exact List.toList_toArray

def Database.fileBytes (database : Database) : List UInt8 :=
  database.image.encode

theorem Database.fileBytes_length (database : Database) :
    database.fileBytes.length = 2 * pageSize := by
  unfold Database.fileBytes DiskFormat.DatabaseImage.encode
  rw [DiskFormat.encodeDisk_length]
  simp [Database.image, geometry, usablePageSize]
  omega

theorem Database.fileBytes_layout (database : Database) :
    database.fileBytes = schemaPageBytes ++ database.dataPageBytes := by
  unfold Database.fileBytes DiskFormat.DatabaseImage.encode DiskFormat.encodeDisk
  change DiskFormat.encodePages (List.ofFn (fun i : Fin 2 => database.image.disk.read i)) = _
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [DiskFormat.encodePages, List.append_nil]
  change schemaPage.bytes.toList ++ database.dataPage.bytes.toList =
    schemaPageBytes ++ database.dataPageBytes
  rw [show schemaPage.bytes.toList = schemaPageBytes by
      exact List.toList_toArray,
    show database.dataPage.bytes.toList = database.dataPageBytes by
      exact List.toList_toArray]

theorem Database.image_headerEncoded (database : Database) :
    database.image.HeaderEncoded := by
  refine ⟨leafPageBody 100 [schemaCell] ++ database.dataPageBytes, ?_⟩
  change database.fileBytes = encodeDatabaseHeader databaseHeader ++
    (leafPageBody 100 [schemaCell] ++ database.dataPageBytes)
  rw [database.fileBytes_layout]
  simp [schemaPageBytes, List.append_assoc]

instance (left right : Row) : Decidable (Row.keyLess left right) :=
  inferInstanceAs (Decidable (left.rowid.value < right.rowid.value))

instance (headerOffset : Nat) (cells : List (List UInt8)) :
    Decidable (PageFit headerOffset cells) := by
  unfold PageFit
  infer_instance

def decodeDataPage : List UInt8 → Option Database
  | 13 :: 0 :: 0 :: afterFreeblock => do
      let (cellCount, afterCount) ← decodeUnsignedFixed 2 afterFreeblock
      let (contentStart, afterContentStart) ← decodeUnsignedFixed 2 afterCount
      match afterContentStart with
      | 0 :: _ =>
          let (rows, suffix) ← decodeCells cellCount
            ((13 :: 0 :: 0 :: afterFreeblock).drop contentStart)
          if _suffixEmpty : suffix = [] then
            if sorted : rows.Pairwise Row.keyLess then
              if fits : PageFit 0 (rows.map Row.encodeCell) then
                let database : Database := ⟨rows, sorted, fits⟩
                if _canonical : database.dataPageBytes =
                    13 :: 0 :: 0 :: afterFreeblock then
                  some database
                else none
              else none
            else none
          else none
      | _ => none
  | _ => none

theorem cellBytes_map_encodeCell (rows : List Row) :
    cellBytes (rows.map Row.encodeCell) = encodeCells rows := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      change row.encodeCell ++ cellBytes (rows.map Row.encodeCell) =
        row.encodeCell ++ encodeCells rows
      rw [induction]

set_option maxHeartbeats 600000 in
theorem decodeDataPage_encode (database : Database) :
    decodeDataPage database.dataPageBytes = some database := by
  let cells := database.rows.map Row.encodeCell
  let contentStart := pageSize - (cellBytes cells).length
  let afterHeader := leafPointers contentStart cells ++
    List.replicate
      (contentStart -
        (leafHeader cells.length contentStart ++ leafPointers contentStart cells).length) 0 ++
    cellBytes cells
  have bodyLayout : database.dataPageBytes =
      13 :: 0 :: 0 ::
        (encodeU16Nat cells.length ++ encodeU16Nat contentStart ++ 0 :: afterHeader) := by
    unfold Database.dataPageBytes leafPageBody leafHeader
    simp only [List.cons_append, List.nil_append]
    rfl
  have countBound : cells.length < 256 ^ 2 := by
    simpa [cells] using database.pageFits.cellCount_lt
  have contentBound : contentStart < 256 ^ 2 := by
    exact contentStart_lt cells
  have dropped : database.dataPageBytes.drop contentStart = encodeCells database.rows := by
    change (leafPageBody 0 cells).drop contentStart = encodeCells database.rows
    rw [show contentStart = pageSize - (cellBytes cells).length by rfl,
      leafPageBody_drop_content cells database.pageFits]
    exact cellBytes_map_encodeCell database.rows
  rw [bodyLayout]
  unfold decodeDataPage
  change (do
    let (cellCount, afterCount) ← decodeUnsignedFixed 2
      (encodeU16Nat cells.length ++ encodeU16Nat contentStart ++ 0 :: afterHeader)
    let (decodedStart, afterContentStart) ← decodeUnsignedFixed 2 afterCount
    match afterContentStart with
    | 0 :: _ =>
        let (rows, suffix) ← decodeCells cellCount
          (database.dataPageBytes.drop decodedStart)
        if suffixEmpty : suffix = [] then
          if sorted : rows.Pairwise Row.keyLess then
            if fits : PageFit 0 (rows.map Row.encodeCell) then
              let decoded : Database := ⟨rows, sorted, fits⟩
              if decoded.dataPageBytes = database.dataPageBytes then some decoded else none
            else none
          else none
        else none
    | _ => none) = some database
  unfold encodeU16Nat
  simp only [List.append_assoc]
  rw [decodeUnsignedFixed_encode _ countBound]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeUnsignedFixed_encode _ contentBound]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dropped]
  have cellsLength : cells.length = database.rows.length := by simp [cells]
  rw [cellsLength]
  have decodedRows := decodeCells_encode database.rows []
  simp only [List.append_nil] at decodedRows
  rw [decodedRows]
  simp only [dif_pos rfl, database.rowidsSorted, database.pageFits]
  let decoded : Database :=
    ⟨database.rows, database.rowidsSorted, database.pageFits⟩
  have decodedEq : decoded = database := Database.ext rfl
  simp [decoded, decodedEq]

def decodeImage (image : DiskFormat.DatabaseImage) : Option Database :=
  match image with
  | ⟨actualGeometry, disk⟩ =>
      if geometryMatches : actualGeometry = geometry then
        let schemaId : Fin actualGeometry.pageCount := ⟨0, by
          rw [geometryMatches]
          decide⟩
        let dataId : Fin actualGeometry.pageCount := ⟨1, by
          rw [geometryMatches]
          decide⟩
        if _schemaMatches : (disk.read schemaId).bytes.toList = schemaPageBytes then
          decodeDataPage (disk.read dataId).bytes.toList
        else none
      else none

theorem decodeImage_encode (database : Database) :
    decodeImage database.image = some database := by
  unfold decodeImage
  change (if _geometryMatches : geometry = geometry then
    if _schemaMatches : schemaPage.bytes.toList = schemaPageBytes then
      decodeDataPage database.dataPage.bytes.toList
    else none
  else none) = some database
  rw [dif_pos rfl]
  have schemaMatches : schemaPage.bytes.toList = schemaPageBytes := by
    change schemaPageBytes.toArray.toList = schemaPageBytes
    exact List.toList_toArray
  rw [dif_pos schemaMatches]
  change decodeDataPage database.dataPageBytes = some database
  exact decodeDataPage_encode database

def decodeFile (input : List UInt8) : Option Database := do
  let (image, suffix) ← DiskFormat.decodeDatabaseImage input
  if _consumed : suffix = [] then decodeImage image else none

theorem decodeFile_encode (database : Database) :
    decodeFile database.fileBytes = some database := by
  unfold decodeFile Database.fileBytes
  have decoded := DiskFormat.decodeDatabaseImage_encode database.image
    database.image_headerEncoded []
  simp only [List.append_nil] at decoded
  rw [decoded]
  simp [decodeImage_encode]

def codec : Durability.DiskCodec Database := {
  Equiv := Eq
  encode := Database.image
  decode := decodeImage
  decode_encode := fun database =>
    ⟨database, decodeImage_encode database, rfl⟩ }

def Database.storageImage (database : Database) : GrowableStorage.Image pageSize := {
  pageCount := 2
  read := fun pageId => if pageId = 0 then schemaPage else database.dataPage }

def transactionWrites (database : Database) :
    List (GrowableStorage.PageWrite pageSize) :=
  [⟨1, database.dataPage⟩]

theorem apply_transactionWrites_equiv (old new : Database) :
    (GrowableStorage.applyWrites old.storageImage
      (transactionWrites new)).Equiv new.storageImage := by
  constructor
  · simp [GrowableStorage.applyWrites, transactionWrites,
      GrowableStorage.Image.write, Database.storageImage]
  · intro pageId bound
    by_cases zero : pageId = 0
    · subst pageId
      simp [GrowableStorage.applyWrites, transactionWrites,
        GrowableStorage.Image.write, Database.storageImage]
    · have one : pageId = 1 := by
        simp [GrowableStorage.applyWrites, transactionWrites,
          GrowableStorage.Image.write, Database.storageImage] at bound
        omega
      subst pageId
      simp [GrowableStorage.applyWrites, transactionWrites,
        GrowableStorage.Image.write, Database.storageImage]

def decodeStorageImage (image : GrowableStorage.Image pageSize) : Option Database :=
  if _countMatches : image.pageCount = 2 then
    decodeImage {
      geometry
      disk := { read := fun pageId => image.read pageId.val } }
  else none

theorem decodeStorageImage_equiv (database : Database)
    {image : GrowableStorage.Image pageSize}
    (equivalent : image.Equiv database.storageImage) :
    decodeStorageImage image = some database := by
  have countMatches : image.pageCount = 2 := by
    simpa [Database.storageImage] using equivalent.1
  let opened : DiskFormat.DatabaseImage := {
    geometry
    disk := { read := fun pageId => image.read pageId.val } }
  have openedEq : opened = database.image := by
    unfold opened Database.image
    apply congrArg (fun disk => DiskFormat.DatabaseImage.mk geometry disk)
    apply congrArg Storage.Disk.mk
    funext pageId
    have pageBound : pageId.val < 2 := pageId.isLt
    have imageBound : pageId.val < image.pageCount := by
      rw [countMatches]
      exact pageBound
    rw [equivalent.2 pageId.val imageBound]
    by_cases zero : pageId.val = 0
    · simp [Database.storageImage, zero]
    · have one : pageId.val = 1 := by omega
      simp [Database.storageImage, zero, one]
  unfold decodeStorageImage
  rw [dif_pos countMatches]
  change decodeImage opened = some database
  rw [openedEq]
  exact decodeImage_encode database

/-- Logical old-or-new recovery for the concrete codec. This connects the
page-level rollback protocol to reopening the actual SQLite image. -/
theorem rollbackCommit_database_crash_atomic (old new : Database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image pageSize)
    (recoveredJournal : Option (GrowableStorage.Journal pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState old.storageImage
        (transactionWrites new) phase)
      recoveredMain recoveredJournal) :
    decodeStorageImage
        (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal) =
          some old ∨
      decodeStorageImage
        (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal) =
          some new := by
  rcases GrowableStorage.rollbackCommit_crash_atomic old.storageImage
    (transactionWrites new) phase recoveredMain recoveredJournal outcome with
    recoveredOld | recoveredWrites
  · exact .inl (decodeStorageImage_equiv old recoveredOld)
  · exact .inr (decodeStorageImage_equiv new
      (recoveredWrites.trans (apply_transactionWrites_equiv old new)))

theorem rollbackCommit_database_committed_recovers_new (old new : Database)
    (recoveredMain : GrowableStorage.Image pageSize)
    (recoveredJournal : Option (GrowableStorage.Journal pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState old.storageImage
        (transactionWrites new) GrowableStorage.CommitPhase.committed)
      recoveredMain recoveredJournal) :
    decodeStorageImage
      (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal) =
        some new := by
  apply decodeStorageImage_equiv new
  exact (GrowableStorage.rollbackCommit_committed_recovers_new old.storageImage
    (transactionWrites new) recoveredMain recoveredJournal outcome).trans
      (apply_transactionWrites_equiv old new)

end PhysicalCodec

end SQLeanite
