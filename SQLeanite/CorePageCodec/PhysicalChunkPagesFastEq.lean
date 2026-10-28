import SQLeanite.CorePageCodec.NumberedPage

namespace SQLeanite
namespace CorePageCodec

/-- The cached traversal is extensionally the specification traversal. -/
theorem physicalChunkPagesFast_eq (node :
    PersistentPageTree.Node CoreChunkPageState.Chunk) :
    physicalChunkPagesFast node = physicalChunkPages node := by
  induction node with
  | leaf pageId entries => rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      unfold physicalChunkPagesFast at leftInduction rightInduction
      simp [physicalChunkPagesFast, summarizePhysicalChunkPages,
        physicalChunkPages, summarizePhysicalChunkPages_maximum,
        leftInduction, rightInduction]
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      unfold physicalChunkPagesFast at leftInduction middleInduction rightInduction
      simp [physicalChunkPagesFast, summarizePhysicalChunkPages,
        physicalChunkPages, summarizePhysicalChunkPages_maximum,
        leftInduction, middleInduction, rightInduction, List.append_assoc]

/-- Encode exactly one physical descriptor.  A missing derived separator is
the same fail-closed condition as in the recursive encoder. -/
def encodePhysicalChunkPage (schema : Core.Schema) :
    PhysicalChunkPage → Option NumberedPage
  | .leaf pageNumber entries => do
      let page ← encodeChunkLeaf schema entries
      some ⟨pageNumber, page⟩
  | .branch2 pageNumber leftPage leftKey rightPage => do
      let key ← leftKey
      let page ← RecursivePageBTree.interiorPage?
        [(leftPage, key)] rightPage
      some ⟨pageNumber, page⟩
  | .branch3 pageNumber leftPage leftKey middlePage middleKey rightPage => do
      let first ← leftKey
      let second ← middleKey
      let page ← RecursivePageBTree.interiorPage?
        [(leftPage, first), (middlePage, second)] rightPage
      some ⟨pageNumber, page⟩

@[simp] theorem encodePhysicalChunkPage_pageNumber
    (schema : Core.Schema) (descriptor : PhysicalChunkPage)
    (page : NumberedPage)
    (encoded : encodePhysicalChunkPage schema descriptor = some page) :
    page.pageNumber = descriptor.pageNumber := by
  cases descriptor with
  | leaf pageNumber entries =>
      cases result : encodeChunkLeaf schema entries with
      | none => simp [encodePhysicalChunkPage, result] at encoded
      | some encodedPage =>
        simp [encodePhysicalChunkPage, result] at encoded
        subst page
        rfl
  | branch2 pageNumber leftPage leftKey rightPage =>
      cases leftKey with
      | none => simp [encodePhysicalChunkPage] at encoded
      | some key =>
        cases result : RecursivePageBTree.interiorPage?
            [(leftPage, key)] rightPage with
        | none => simp [encodePhysicalChunkPage, result] at encoded
        | some encodedPage =>
          simp [encodePhysicalChunkPage, result] at encoded
          subst page
          rfl
  | branch3 pageNumber leftPage leftKey middlePage middleKey rightPage =>
      cases leftKey with
      | none => simp [encodePhysicalChunkPage] at encoded
      | some first =>
        cases middleKey with
        | none => simp [encodePhysicalChunkPage] at encoded
        | some second =>
          cases result : RecursivePageBTree.interiorPage?
              [(leftPage, first), (middlePage, second)] rightPage with
          | none => simp [encodePhysicalChunkPage, result] at encoded
          | some encodedPage =>
            simp [encodePhysicalChunkPage, result] at encoded
            subst page
            rfl

/-- The existing recursive encoder is precisely `mapM` over physical page
descriptors.  This is a representation theorem, not a second implementation:
all live encoding continues to use `encodeChunkNode`. -/
theorem encodeChunkNode_eq_mapM (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk) :
    encodeChunkNode schema node =
      (physicalChunkPages node).mapM (encodePhysicalChunkPage schema) := by
  induction node with
  | leaf pageId entries =>
      cases result : encodeChunkLeaf schema entries <;>
        simp [encodeChunkNode, physicalChunkPages, encodePhysicalChunkPage,
          result]
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [physicalChunkPages, List.mapM_cons, List.mapM_append,
        encodePhysicalChunkPage, ← leftInduction, ← rightInduction]
      cases keyResult : maximumChunkRowid? left with
      | none => simp [encodeChunkNode, keyResult]
      | some key =>
        cases pageResult : RecursivePageBTree.interiorPage?
            [(left.rootId, key)] right.rootId with
        | none => simp [encodeChunkNode, keyResult, pageResult]
        | some page =>
          cases leftResult : encodeChunkNode schema left with
          | none =>
            simp [encodeChunkNode, keyResult, pageResult, leftResult]
          | some leftPages =>
            cases rightResult : encodeChunkNode schema right with
            | none =>
              simp [encodeChunkNode, keyResult, pageResult, leftResult,
                rightResult]
            | some rightPages =>
              simp [encodeChunkNode, keyResult, pageResult, leftResult,
                rightResult]
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [physicalChunkPages, List.mapM_cons, List.mapM_append,
        encodePhysicalChunkPage, ← leftInduction, ← middleInduction,
        ← rightInduction]
      cases leftKeyResult : maximumChunkRowid? left with
      | none => simp [encodeChunkNode, leftKeyResult]
      | some leftKey =>
        cases middleKeyResult : maximumChunkRowid? middle with
        | none => simp [encodeChunkNode, leftKeyResult, middleKeyResult]
        | some middleKey =>
          cases pageResult : RecursivePageBTree.interiorPage?
              [(left.rootId, leftKey), (middle.rootId, middleKey)]
              right.rootId with
          | none =>
            simp [encodeChunkNode, leftKeyResult, middleKeyResult, pageResult]
          | some page =>
            cases leftResult : encodeChunkNode schema left with
            | none =>
              simp [encodeChunkNode, leftKeyResult, middleKeyResult,
                pageResult, leftResult]
            | some leftPages =>
              cases middleResult : encodeChunkNode schema middle with
              | none =>
                simp [encodeChunkNode, leftKeyResult, middleKeyResult,
                  pageResult, leftResult, middleResult]
              | some middlePages =>
                cases rightResult : encodeChunkNode schema right with
                | none =>
                  simp [encodeChunkNode, leftKeyResult, middleKeyResult,
                    pageResult, leftResult, middleResult, rightResult]
                | some rightPages =>
                  simp [encodeChunkNode, leftKeyResult, middleKeyResult,
                    pageResult, leftResult, middleResult, rightResult,
                    List.append_assoc]

def findPhysicalChunkPage? (pageNumber : Nat)
    (pages : List PhysicalChunkPage) : Option PhysicalChunkPage :=
  pages.find? (fun page => page.pageNumber = pageNumber)

/-- Byte-relevant dirty pages.  Unlike the generic persistent-tree delta,
this comparison includes SQLite's derived interior keys. -/
def changedPhysicalChunkPages
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk) :
    List PhysicalChunkPage :=
  (physicalChunkPages after).filter fun page =>
    findPhysicalChunkPage? page.pageNumber (physicalChunkPages before) !=
      some page

def physicalChunkPageSlotCount : List PhysicalChunkPage → Nat
  | [] => 0
  | page :: pages => max (page.pageNumber + 1)
      (physicalChunkPageSlotCount pages)

def fillPhysicalChunkPageSlots :
    Array (Option PhysicalChunkPage) → List PhysicalChunkPage →
      Array (Option PhysicalChunkPage)
  | slots, [] => slots
  | slots, page :: pages =>
      let next := match slots[page.pageNumber]? with
        | some none => slots.setIfInBounds page.pageNumber (some page)
        | _ => slots
      fillPhysicalChunkPageSlots next pages

def physicalChunkPageSlots (pages : List PhysicalChunkPage) :
    Array (Option PhysicalChunkPage) :=
  fillPhysicalChunkPageSlots
    (Array.replicate (physicalChunkPageSlotCount pages) none) pages

def physicalChunkPageSlotLookup
    (slots : Array (Option PhysicalChunkPage)) (pageNumber : Nat) :
    Option PhysicalChunkPage :=
  slots[pageNumber]?.join

theorem physicalChunkPageNumber_lt_slotCount
    {page : PhysicalChunkPage} {pages : List PhysicalChunkPage}
    (member : page ∈ pages) :
    page.pageNumber < physicalChunkPageSlotCount pages := by
  induction pages with
  | nil => simp at member
  | cons head pages induction =>
      simp only [List.mem_cons] at member
      simp only [physicalChunkPageSlotCount]
      rcases member with rfl | later
      · omega
      · have bound := induction later
        omega

@[simp] theorem fillPhysicalChunkPageSlots_size
    (slots : Array (Option PhysicalChunkPage))
    (pages : List PhysicalChunkPage) :
    (fillPhysicalChunkPageSlots slots pages).size = slots.size := by
  induction pages generalizing slots with
  | nil => rfl
  | cons page pages induction =>
      unfold fillPhysicalChunkPageSlots
      split <;> simp [induction]

/-- Filling a bounded slot table implements first-match lookup.  The existing
slot wins, otherwise the first page with that identity is installed. -/
theorem fillPhysicalChunkPageSlots_lookup
    (slots : Array (Option PhysicalChunkPage))
    (pages : List PhysicalChunkPage)
    (bounded : ∀ page ∈ pages, page.pageNumber < slots.size)
    (pageNumber : Nat) :
    physicalChunkPageSlotLookup
        (fillPhysicalChunkPageSlots slots pages) pageNumber =
      match physicalChunkPageSlotLookup slots pageNumber with
      | some existing => some existing
      | none => findPhysicalChunkPage? pageNumber pages := by
  induction pages generalizing slots with
  | nil =>
      cases lookup : physicalChunkPageSlotLookup slots pageNumber <;>
        simp [fillPhysicalChunkPageSlots, findPhysicalChunkPage?, lookup]
  | cons page pages induction =>
      have pageBound : page.pageNumber < slots.size :=
        bounded page (by simp)
      have tailBound : ∀ candidate ∈ pages,
          candidate.pageNumber < slots.size := by
        intro candidate member
        exact bounded candidate (by simp [member])
      unfold fillPhysicalChunkPageSlots
      cases slotResult : slots[page.pageNumber]? with
      | none => simp [pageBound] at slotResult
      | some slot =>
        cases slot with
        | none =>
          have emptySlot : slots[page.pageNumber] = none := by
            simpa only [Array.getElem?_eq_getElem pageBound, Option.some.injEq] using slotResult
          rw [induction]
          · by_cases same : page.pageNumber = pageNumber
            · subst pageNumber
              simp [physicalChunkPageSlotLookup, slotResult, pageBound, emptySlot,
                findPhysicalChunkPage?]
            · simp [physicalChunkPageSlotLookup, slotResult, pageBound,
                Array.getElem?_setIfInBounds_ne same,
                findPhysicalChunkPage?, same]
          · intro candidate member
            simpa using tailBound candidate member
        | some existing =>
          rw [induction]
          · by_cases same : page.pageNumber = pageNumber
            · subst pageNumber
              simp [physicalChunkPageSlotLookup, slotResult,
                findPhysicalChunkPage?]
            · simp [physicalChunkPageSlotLookup, slotResult,
                findPhysicalChunkPage?, same]
          · exact tailBound

theorem physicalChunkPageSlots_lookup (pages : List PhysicalChunkPage)
    (pageNumber : Nat) :
    physicalChunkPageSlotLookup (physicalChunkPageSlots pages) pageNumber =
      findPhysicalChunkPage? pageNumber pages := by
  unfold physicalChunkPageSlots
  rw [fillPhysicalChunkPageSlots_lookup]
  · by_cases inBounds : pageNumber < physicalChunkPageSlotCount pages <;>
      simp [physicalChunkPageSlotLookup, inBounds]
  · intro page member
    simpa using physicalChunkPageNumber_lt_slotCount member

def changedPhysicalChunkPagesFast
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk) :
    List PhysicalChunkPage :=
  let slots := physicalChunkPageSlots (physicalChunkPagesFast before)
  (physicalChunkPagesFast after).filter fun page =>
    physicalChunkPageSlotLookup slots page.pageNumber != some page

theorem changedPhysicalChunkPagesFast_eq (before after :
    PersistentPageTree.Node CoreChunkPageState.Chunk) :
    changedPhysicalChunkPagesFast before after =
      changedPhysicalChunkPages before after := by
  unfold changedPhysicalChunkPagesFast changedPhysicalChunkPages
  rw [physicalChunkPagesFast_eq, physicalChunkPagesFast_eq]
  apply List.filter_congr
  intro page member
  rw [physicalChunkPageSlots_lookup]

def encodeChangedChunkPages (schema : Core.Schema)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk) :
    Option (List NumberedPage) :=
  (changedPhysicalChunkPages before after).mapM
    (encodePhysicalChunkPage schema)

theorem not_mem_changedPhysicalChunkPages
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (page : PhysicalChunkPage) (member : page ∈ physicalChunkPages after)
    (unchanged : page ∉ changedPhysicalChunkPages before after) :
    findPhysicalChunkPage? page.pageNumber (physicalChunkPages before) =
      some page := by
  unfold changedPhysicalChunkPages at unchanged
  simp only [List.mem_filter, member, true_and, Bool.not_eq_true] at unchanged
  simpa using unchanged

/-- Every successful descriptor has its encoded page in a successful `mapM`
result. -/
theorem mapM_encodePhysicalChunkPage_input (schema : Core.Schema) :
    ∀ {descriptors : List PhysicalChunkPage} {pages : List NumberedPage},
      descriptors.mapM (encodePhysicalChunkPage schema) = some pages →
      ∀ descriptor ∈ descriptors,
        ∃ page ∈ pages,
          encodePhysicalChunkPage schema descriptor = some page
  | [], pages, encoded => by
      simp only [List.mapM_nil, pure, Option.pure_def,
        Option.some.injEq] at encoded
      subst pages
      simp
  | descriptor :: descriptors, pages, encoded => by
      simp only [List.mapM_cons] at encoded
      cases headResult : encodePhysicalChunkPage schema descriptor with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult, Option.bind_eq_bind, Option.bind] at encoded
        cases tailResult : descriptors.mapM
            (encodePhysicalChunkPage schema) with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          simp only [pure, Option.pure_def, Option.some.injEq] at encoded
          subst pages
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with rfl | later
          · exact ⟨head, by simp, headResult⟩
          · rcases mapM_encodePhysicalChunkPage_input schema tailResult
                candidate later with ⟨page, pageMember, pageResult⟩
            exact ⟨page, by simp [pageMember], pageResult⟩

/-- Conversely, every page in a successful `mapM` result comes from one
physical descriptor. -/
theorem mapM_encodePhysicalChunkPage_output (schema : Core.Schema) :
    ∀ {descriptors : List PhysicalChunkPage} {pages : List NumberedPage},
      descriptors.mapM (encodePhysicalChunkPage schema) = some pages →
      ∀ page ∈ pages,
        ∃ descriptor ∈ descriptors,
          encodePhysicalChunkPage schema descriptor = some page
  | [], pages, encoded => by
      simp only [List.mapM_nil, pure, Option.pure_def,
        Option.some.injEq] at encoded
      subst pages
      simp
  | descriptor :: descriptors, pages, encoded => by
      simp only [List.mapM_cons] at encoded
      cases headResult : encodePhysicalChunkPage schema descriptor with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult, Option.bind_eq_bind, Option.bind] at encoded
        cases tailResult : descriptors.mapM
            (encodePhysicalChunkPage schema) with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          simp only [pure, Option.pure_def, Option.some.injEq] at encoded
          subst pages
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with rfl | later
          · exact ⟨descriptor, by simp, headResult⟩
          · rcases mapM_encodePhysicalChunkPage_output schema tailResult
                candidate later with ⟨source, sourceMember, sourceResult⟩
            exact ⟨source, by simp [sourceMember], sourceResult⟩

theorem exists_mapM_of_forall_some (encode : α → Option β) :
    ∀ (input : List α),
      (∀ value ∈ input, ∃ output, encode value = some output) →
      ∃ output, input.mapM encode = some output
  | [], _ => ⟨[], rfl⟩
  | value :: input, total => by
      rcases total value (by simp) with ⟨head, headResult⟩
      rcases exists_mapM_of_forall_some encode input (by
          intro candidate member
          exact total candidate (by simp [member])) with ⟨tail, tailResult⟩
      exact ⟨head :: tail, by simp [headResult, tailResult]⟩

/-- A successfully encoded exact changed-descriptor set, together with an
encodable pre-state, proves that the entire post-tree is encodable.  This is
an existence theorem only: it never executes the full post-tree encoder on the
localized runtime path. -/
theorem exists_encodeChunkNode_of_changed
    (schema : Core.Schema)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (beforePages changedPages : List NumberedPage)
    (beforeEncoded : encodeChunkNode schema before = some beforePages)
    (changedEncoded : encodeChangedChunkPages schema before after =
      some changedPages) :
    ∃ afterPages, encodeChunkNode schema after = some afterPages := by
  rw [encodeChunkNode_eq_mapM] at beforeEncoded ⊢
  unfold encodeChangedChunkPages at changedEncoded
  apply exists_mapM_of_forall_some
  intro descriptor descriptorMember
  by_cases changed : descriptor ∈ changedPhysicalChunkPages before after
  · rcases mapM_encodePhysicalChunkPage_input schema changedEncoded
        descriptor changed with ⟨page, _, encoded⟩
    exact ⟨page, encoded⟩
  · have found := not_mem_changedPhysicalChunkPages before after descriptor
      descriptorMember changed
    have oldMember : descriptor ∈ physicalChunkPages before :=
      List.mem_of_find?_eq_some found
    rcases mapM_encodePhysicalChunkPage_input schema beforeEncoded descriptor
        oldMember with ⟨page, _, encoded⟩
    exact ⟨page, encoded⟩

/-- A byte-exact changed-page encoding accounts for every page in the full
post-state: selected pages occur in the delta, and every omitted page occurs
byte-for-byte in the full pre-state encoding. -/
theorem encodeChangedChunkPages_accounts (schema : Core.Schema)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (beforePages afterPages changedPages : List NumberedPage)
    (beforeEncoded : encodeChunkNode schema before = some beforePages)
    (afterEncoded : encodeChunkNode schema after = some afterPages)
    (changedEncoded : encodeChangedChunkPages schema before after =
      some changedPages) :
    ∀ page ∈ afterPages, page ∈ changedPages ∨ page ∈ beforePages := by
  rw [encodeChunkNode_eq_mapM] at beforeEncoded afterEncoded
  unfold encodeChangedChunkPages at changedEncoded
  intro page pageMember
  rcases mapM_encodePhysicalChunkPage_output schema afterEncoded page
      pageMember with ⟨descriptor, descriptorMember, descriptorEncoded⟩
  by_cases changed : descriptor ∈ changedPhysicalChunkPages before after
  · left
    rcases mapM_encodePhysicalChunkPage_input schema changedEncoded descriptor
        changed with ⟨selected, selectedMember, selectedEncoded⟩
    have equal : selected = page := Option.some.inj
      (selectedEncoded.symm.trans descriptorEncoded)
    simpa [equal] using selectedMember
  · right
    have found := not_mem_changedPhysicalChunkPages before after descriptor
      descriptorMember changed
    have oldMember : descriptor ∈ physicalChunkPages before :=
      List.mem_of_find?_eq_some found
    rcases mapM_encodePhysicalChunkPage_input schema beforeEncoded descriptor
        oldMember with ⟨old, oldMember, oldEncoded⟩
    have equal : old = page := Option.some.inj
      (oldEncoded.symm.trans descriptorEncoded)
    simpa [equal] using oldMember

end CorePageCodec

end SQLeanite
