import SQLeanite.CoreFileAdapter.PreadPageSource

namespace SQLeanite
namespace CoreFileAdapter

/-- The fast array-backed decoder source and the growable-storage view read
the same page bytes.  The equality is proof-only: live opens retain O(1)
array slicing and never build the range/list used by `ofStorageImage`. -/
theorem byteArrayPageSource_eq_storageImage
    (input : ByteArray) (pageCount : Nat)
    (exactSize : input.size = pageCount * PhysicalCodec.pageSize) :
    byteArrayPageSource input pageCount =
      CorePageSource.ofStorageImage
        (byteArrayStorageImage input pageCount exactSize) := by
  apply CorePageSource.pageSource_ext
  · simp [byteArrayPageSource, byteArrayStorageImage]
  · funext pageNumber
    by_cases zero : pageNumber = 0
    · subst pageNumber
      simp [byteArrayPageSource, CorePageSource.readPage_zero]
    by_cases high : pageCount < pageNumber
    · rw [CorePageSource.readPage_out_of_bounds _ _ high]
      simp [byteArrayPageSource, zero, high]
    · have bound : pageNumber - 1 < pageCount := by omega
      have pageNumberEq : pageNumber - 1 + 1 = pageNumber := by omega
      have stopBound : (pageNumber - 1) * PhysicalCodec.pageSize +
          PhysicalCodec.pageSize ≤ input.size := by
        rw [exactSize]
        have pageWithin : pageNumber - 1 + 1 ≤ pageCount := by omega
        have scaled := Nat.mul_le_mul_right PhysicalCodec.pageSize pageWithin
        simpa [Nat.add_mul] using scaled
      have pageWithin : pageNumber - 1 + 1 ≤ pageCount := by omega
      rw [← pageNumberEq,
        CorePageSource.readPage_ofStorageImage _ (pageNumber - 1) bound]
      simp [byteArrayPageSource, byteArrayStorageImage, zero, high, bound,
        stopBound, pageWithin]

/-- Read a supported physical image once and recover its logical database and
persistent page identities together.  The returned capability records that
the index images were validated by this same open. Returning `none` is an
optimization miss: callers retain the general compatibility path. -/
def loadOpenState (paths : Paths) :
    IO (Option ValidatedOpenState) := do
  let input ← IO.FS.readBinFile paths.main
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let some (header, _) := FileFormat.decodeDatabaseHeader firstPageBytes |
    return none
  let count := header.databaseSizePages.val
  unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
      header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
      input.size = count * PhysicalCodec.pageSize do return none
  let source := byteArrayPageSource input count
  let opened := match CorePageLoad.openGenerated? source with
    | some state => some state
    | none => CorePageLoad.open? source
  return opened.map fun state => ⟨state, ()⟩

structure CertifiedIndexEncoding (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) where
  value : CoreOverflow.IndexEncoding
  encoded : CoreOverflow.encodeIndex rootPage table index = some value

def certifyIndexEncoding? (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) :
    Option (CertifiedIndexEncoding rootPage table index) :=
  match encoded : CoreOverflow.encodeIndex rootPage table index with
  | none => none
  | some value => some ⟨value, encoded⟩

theorem certifyIndexEncoding?_exact {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {certified : CertifiedIndexEncoding rootPage table index}
    (success : certifyIndexEncoding? rootPage table index = some certified) :
    CoreOverflow.encodeIndex rootPage table index = some certified.value := by
  unfold certifyIndexEncoding? at success
  split at success
  next => contradiction
  next value encoded =>
    injection success with equal
    subst certified
    exact encoded

/-- A physical, page-directed index image is accepted only with an exact
decoder witness for the logical post-state. This is deliberately stronger
than a byte-count or successful-mutation flag. -/
structure DecodedIndexCertificate (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) where
  source : CoreDecode.PageSource
  exact : CoreDecode.decodeIndexSubtreeFrom source (source.pageCount + 1)
      rootPage = some (CoreDecode.expectedIndexEntries table index)

def certifyDecodedIndex? (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) (source : CoreDecode.PageSource) :
    Option (DecodedIndexCertificate rootPage table index) :=
  match decoded : CoreDecode.decodeIndexSubtreeFrom source
      (source.pageCount + 1) rootPage with
  | none => none
  | some entries =>
      if same : entries = CoreDecode.expectedIndexEntries table index then
        some ⟨source, by simpa [same] using decoded⟩
      else none

theorem certifyDecodedIndex?_source {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {source : CoreDecode.PageSource}
    {certified : DecodedIndexCertificate rootPage table index}
    (success : certifyDecodedIndex? rootPage table index source =
      some certified) :
    certified.source = source := by
  unfold certifyDecodedIndex? at success
  split at success
  next => contradiction
  next entries decoded =>
    split at success
    next =>
      injection success with equal
      exact congrArg DecodedIndexCertificate.source equal.symm
    next => contradiction

theorem certifyDecodedIndex?_exact {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {source : CoreDecode.PageSource}
    {certified : DecodedIndexCertificate rootPage table index}
    (success : certifyDecodedIndex? rootPage table index source =
      some certified) :
    CoreDecode.decodeIndexSubtreeFrom source (source.pageCount + 1) rootPage =
      some (CoreDecode.expectedIndexEntries table index) := by
  rw [← certifyDecodedIndex?_source success]
  exact certified.exact

/-- Retain the source identity hidden by the ordinary optional certificate.
This wrapper is proof-only and lets the localized writer connect a successful
decoder check to the exact storage overlay it checked. -/
structure CertifiedDecodedIndexAt (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) (source : CoreDecode.PageSource) where
  certificate : DecodedIndexCertificate rootPage table index
  sourceExact : certificate.source = source

def certifyDecodedIndexAt? (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) (source : CoreDecode.PageSource) :
    Option (CertifiedDecodedIndexAt rootPage table index source) :=
  match success : certifyDecodedIndex? rootPage table index source with
  | none => none
  | some certificate =>
      some ⟨certificate, certifyDecodedIndex?_source success⟩

inductive LocalizedIndexCertificate (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) where
  | encoded (certificate : CertifiedIndexEncoding rootPage table index)
  | decoded (certificate : DecodedIndexCertificate rootPage table index)

/-- A routed index mutation was decoded over the finite write overlay of an
exact old storage image. -/
def DecodedIndexCertificate.OnStorage
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    (certificate : DecodedIndexCertificate rootPage table index)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : Prop :=
  ∃ oldImage : GrowableStorage.Image PhysicalCodec.pageSize,
    certificate.source = CorePageSource.ofStorageImage
      (GrowableStorage.applyWrites oldImage writes)

def CertifiedIndexEncoding.OnStorage
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    (certificate : CertifiedIndexEncoding rootPage table index)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : Prop :=
  ∃ oldImage : GrowableStorage.Image PhysicalCodec.pageSize,
    CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage writes))
      rootPage certificate.value.pages ∧
    0 < rootPage ∧
    rootPage + certificate.value.pages.length < 2 ^ 32 ∧
    rootPage + certificate.value.pages.length ≤
      (GrowableStorage.applyWrites oldImage writes).pageCount + 1

structure LocalizedLastIndexDelta
    (delta : CoreChunkPageDelta.StateDelta) where
  candidate : CoreChunkPageDelta.updateStateCandidate? delta.before
    delta.after.database = some delta
  state : CoreChunkPageState.State
  index : Core.Index
  rootPage : Nat
  entry : CoreDecode.CatalogEntry
  entryTable : entry.table = delta.table.after.table.schema.name
  entryRoot : entry.rootPage = rootPage
  entryMetadata : CoreDecode.decodeCanonicalIndex
    delta.table.after.table.schema delta.table.after.table.schema.name entry =
      some index
  tableExpectedBefore : List
    (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  tableWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  tableExpectedBeforeEq : CoreChunkPageDelta.beforeWrites delta.table =
    some tableExpectedBefore
  tableWritesEq : CoreChunkPageDelta.writes delta.table = some tableWrites
  expectedBefore : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  certificate : LocalizedIndexCertificate rootPage
    delta.table.after.table index
  storage : match certificate with
    | .encoded encoded => encoded.OnStorage writes
    | .decoded decoded => decoded.OnStorage writes
  writesDistinct : writes.Pairwise (fun left right => left.pageId ≠ right.pageId)
  allocation : state.AllocationWellFormed
  validated : ValidatedOpenState

/-- Turn one small decidable boundary check into erased evidence retained by a
prepared delta.  This is used only for catalog identity, never to validate a
table or index by re-running its logical operation. -/
def decideProof? (proposition : Prop) [Decidable proposition] :
    Option (PLift proposition) :=
  if proof : proposition then some ⟨proof⟩ else none

/-- Retain the defining equation of an `Option` value selected by executable
preparation.  The equation is erased when used in proof fields, but prevents
the durability layer from attaching a page list reconstructed separately. -/
structure ExactOptionResult (result : Option α) where
  value : α
  exact : result = some value

def exactOptionResult? (result : Option α) :
    Option (ExactOptionResult result) :=
  match exact : result with
  | none => none
  | some value => some ⟨value, by cases exact; rfl⟩

def storagePage? (bytes : List UInt8) :
    Option (Storage.Page PhysicalCodec.pageSize) :=
  if exact : bytes.length = PhysicalCodec.pageSize then
    some {
      bytes := bytes.toArray
      sizeInvariant := by simp [exact] }
  else none

private theorem storagePage?_bytes {bytes : List UInt8}
    {page : Storage.Page PhysicalCodec.pageSize}
    (success : storagePage? bytes = some page) :
    page.bytes.toList = bytes := by
  unfold storagePage? at success
  split at success
  next =>
    injection success with equal
    subst page
    simp
  next => contradiction

/-- Read one exact contiguous pre-image run.  The recursive form retains a
simple kernel proof that every returned page really came from its numbered
source read. -/
def readPageWrites? (source : CoreDecode.PageSource) :
    Nat → Nat → Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
  | _, 0 => some []
  | pageNumber, count + 1 => do
      let bytes ← source.readPage pageNumber
      let page ← storagePage? bytes
      let tail ← readPageWrites? source (pageNumber + 1) count
      some (⟨pageNumber - 1, page⟩ :: tail)

structure ReadPageWritesResult (source : CoreDecode.PageSource)
    (start count : Nat) where
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  exact : readPageWrites? source start count = some writes

def readPageWritesCertified? (source : CoreDecode.PageSource)
    (start count : Nat) : Option (ReadPageWritesResult source start count) :=
  match success : readPageWrites? source start count with
  | none => none
  | some writes => some ⟨writes, success⟩

theorem readPageWrites?_reads
    (source : CoreDecode.PageSource) :
    ∀ {start count : Nat}
      {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)},
      0 < start →
      readPageWrites? source start count = some writes →
      ∀ write ∈ writes,
        source.readPage (write.pageId + 1) = some write.page.bytes.toList
  | _, 0, writes, _, success => by
      simp only [readPageWrites?, Option.some.injEq] at success
      subst writes
      simp
  | start, count + 1, writes, positive, success => by
      simp only [readPageWrites?, Option.bind_eq_bind, Option.bind] at success
      cases readResult : source.readPage start with
      | none => simp [readResult] at success
      | some bytes =>
          simp only [readResult] at success
          cases pageResult : storagePage? bytes with
          | none => simp [pageResult] at success
          | some page =>
              simp only [pageResult] at success
              cases tailResult : readPageWrites? source (start + 1) count with
              | none => simp [tailResult] at success
              | some tail =>
                  simp only [tailResult, Option.some.injEq] at success
                  subst writes
                  intro write member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · have pageNumber : start - 1 + 1 = start := by omega
                    rw [pageNumber, readResult, storagePage?_bytes pageResult]
                  · exact readPageWrites?_reads source (by omega) tailResult
                      write member

def indexPageWrites (rootPage : Nat) :
    List CoreFile.Page →
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  | [] => []
  | page :: pages =>
      ⟨rootPage - 1, page.storage⟩ :: indexPageWrites (rootPage + 1) pages

theorem indexPageWrites_length (rootPage : Nat) (pages : List CoreFile.Page) :
    (indexPageWrites rootPage pages).length = pages.length := by
  induction pages generalizing rootPage with
  | nil => rfl
  | cons page pages induction =>
      simp only [indexPageWrites, List.length_cons, induction]

theorem indexPageWrites_covers (rootPage : Nat) (pages : List CoreFile.Page)
    (positive : 0 < rootPage) :
    ∀ (offset : Nat) (inBounds : offset < pages.length),
      ∃ write ∈ indexPageWrites rootPage pages,
        write.pageId + 1 = rootPage + offset ∧
        write.page.bytes.toList = (pages.get ⟨offset, inBounds⟩).bytes := by
  induction pages generalizing rootPage with
  | nil => simp
  | cons page pages induction =>
      intro offset inBounds
      cases offset with
      | zero =>
          refine ⟨⟨rootPage - 1, page.storage⟩, by simp [indexPageWrites], ?_, ?_⟩
          · change rootPage - 1 + 1 = rootPage
            omega
          · simp [CoreFile.Page.storage]
      | succ offset =>
          have tailBound : offset < pages.length := by
            simpa using inBounds
          rcases induction (rootPage := rootPage + 1) (by omega) offset tailBound
            with ⟨write, member, pageNumber, bytes⟩
          refine ⟨write, by simp [indexPageWrites, member], ?_, ?_⟩
          · omega
          · simpa using bytes

theorem indexPageWrites_member_exact (rootPage : Nat)
    (pages : List CoreFile.Page) :
    ∀ {write : GrowableStorage.PageWrite PhysicalCodec.pageSize},
      write ∈ indexPageWrites rootPage pages →
      ∃ (offset : Nat) (inBounds : offset < pages.length),
        write = ⟨rootPage + offset - 1,
          (pages.get ⟨offset, inBounds⟩).storage⟩ := by
  induction pages generalizing rootPage with
  | nil => simp [indexPageWrites]
  | cons page pages induction =>
      intro write member
      simp only [indexPageWrites, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨0, by simp, by simp⟩
      · rcases induction (rootPage := rootPage + 1) member with
          ⟨offset, inBounds, exactWrite⟩
        refine ⟨offset + 1, by simpa, ?_⟩
        rw [exactWrite]
        congr 1 <;> omega

theorem indexPageWrites_eq_of_pageId_eq (rootPage : Nat)
    (pages : List CoreFile.Page)
    (positive : 0 < rootPage)
    {left right : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (leftMember : left ∈ indexPageWrites rootPage pages)
    (rightMember : right ∈ indexPageWrites rootPage pages)
    (samePage : left.pageId = right.pageId) : left = right := by
  rcases indexPageWrites_member_exact rootPage pages leftMember with
    ⟨leftOffset, leftBound, leftExact⟩
  rcases indexPageWrites_member_exact rootPage pages rightMember with
    ⟨rightOffset, rightBound, rightExact⟩
  subst left
  subst right
  simp only [GrowableStorage.PageWrite.pageId] at samePage
  have offsets : leftOffset = rightOffset := by omega
  subst rightOffset
  rfl

/-- Drop a proposed write only when the validated old tail already contains
the exact same page ID and bytes.  This scopes both journal pre-images and main
writes to the physical index delta instead of the complete rebuilt image. -/
def changedPageWrites
    (before writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize) :=
  writes.filter fun write =>
    !before.any fun old => old.pageId == write.pageId && old.page == write.page

theorem changedPageWrites_sublist (before writes :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    (changedPageWrites before writes).Sublist writes := by
  exact List.filter_sublist

theorem omitted_changedPageWrites_matches
    {before writes :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    {write : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (member : write ∈ writes)
    (omitted : write ∉ changedPageWrites before writes) :
    ∃ old ∈ before, old.pageId = write.pageId ∧ old.page = write.page := by
  unfold changedPageWrites at omitted
  simp only [List.mem_filter, member, true_and, Bool.not_eq_true] at omitted
  have anyTrue : before.any (fun old =>
      old.pageId == write.pageId && old.page == write.page) = true := by
    simpa using omitted
  simp only [List.any_eq_true] at anyTrue
  rcases anyTrue with ⟨old, oldMember, matched⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at matched
  exact ⟨old, oldMember, matched⟩

def indexEntryCell? (entry : CoreDecode.IndexEntry) : Option (List UInt8) := do
  let record ← CoreFile.physicalRecord? [
    entry.value.recordField,
    (PhysicalCodec.Value.integer entry.rowid).recordField]
  if bounded : record.encode.length < 2 ^ 64 then
    let size : FileFormat.U64Value :=
      ⟨record.encode.length, by simpa using bounded⟩
    some (FileFormat.encodeVarint size ++ record.encode)
  else none

def indexInteriorPageFromEntries? (entries : List (Nat × CoreDecode.IndexEntry))
    (rightmost : Nat) : Option CoreFile.Page := do
  let children ← entries.mapM fun entry => do
    let cell ← indexEntryCell? entry.2
    some (entry.1, cell)
  RecursivePageBTree.indexInteriorPage? children rightmost

structure IndexPageMutations where
  source : CoreDecode.PageSource
  changed : List (Nat × List UInt8) := []

/-- The file-backed counterpart of `IndexPageMutations`.  It retains only the
pages on the routed index path; unchanged pages are fetched positionally from
the main file instead of materializing the whole database before every
autocommit insert. -/
structure IOIndexPageMutations where
  source : CoreDecode.IOPageSource
  changed : List (Nat × List UInt8) := []
  nextPage : Nat

def replaceChangedPage (pageNumber : Nat) (bytes : List UInt8) :
    List (Nat × List UInt8) → List (Nat × List UInt8)
  | [] => [(pageNumber, bytes)]
  | changed :: changes =>
      if changed.1 = pageNumber then (pageNumber, bytes) :: changes
      else changed :: replaceChangedPage pageNumber bytes changes

def IndexPageMutations.readPage? (state : IndexPageMutations)
    (pageNumber : Nat) : Option (List UInt8) :=
  match state.changed.find? (fun changed => changed.1 == pageNumber) with
  | some changed => some changed.2
  | none => state.source.readPage pageNumber

def IndexPageMutations.pageSource (state : IndexPageMutations) :
    CoreDecode.PageSource := {
  pageCount := state.source.pageCount
  readPage := state.readPage? }

def IndexPageMutations.writePage? (state : IndexPageMutations)
    (pageNumber : Nat) (page : CoreFile.Page) : Option IndexPageMutations := do
  if _valid : 0 < pageNumber ∧ pageNumber ≤ state.source.pageCount then
    some { state with
      changed := replaceChangedPage pageNumber page.bytes state.changed }
  else none

def IOIndexPageMutations.readPage? (state : IOIndexPageMutations)
    (pageNumber : Nat) : IO (Option (List UInt8)) :=
  match state.changed.find? (fun changed => changed.1 == pageNumber) with
  | some changed => pure (some changed.2)
  | none => state.source.readPage pageNumber

end CoreFileAdapter

end SQLeanite
