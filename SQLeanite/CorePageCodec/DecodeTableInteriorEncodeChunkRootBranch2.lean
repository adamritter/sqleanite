import SQLeanite.CorePageCodec.InteriorChildrenInteriorPageTwo

namespace SQLeanite
namespace CorePageCodec

theorem decodeTableInterior_encodeChunkRoot_branch2 (schema : Core.Schema)
    (pageId : Nat) (left : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (separator : Nat) (right : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (root : NumberedPage) (leftPositive : 0 < left.rootId)
    (built : encodeChunkRoot schema
      (.branch2 pageId left separator right) = some root) :
    ∃ boundary,
      (CoreChunkPageState.Node.rows left).getLast? = some boundary ∧
      CoreDecode.decodeTableInterior? root.page.bytes =
        some ([(left.rootId, boundary.rowid)], right.rootId) := by
  simp only [encodeChunkRoot] at built
  cases keyResult : maximumChunkRowid? left with
  | none => simp [keyResult] at built
  | some key =>
      simp only [keyResult, Option.bind_eq_bind, Option.bind] at built
      cases pageResult : RecursivePageBTree.interiorPage?
          [(left.rootId, key)] right.rootId with
      | none => simp [pageResult] at built
      | some page =>
          simp only [pageResult, Option.some.injEq] at built
          subst root
          rcases maximumChunkRowid?_witness keyResult with
            ⟨boundary, boundaryLast, rfl⟩
          refine ⟨boundary, boundaryLast, ?_⟩
          have keyBound : boundary.rowid.toUnsigned < 2 ^ 64 := by
            simpa [FileFormat.IntegerWidth.modulus] using
              boundary.rowid.toUnsigned_lt
          rw [decodeTableInterior_interiorPage_one leftPositive keyBound
            pageResult]
          simp [FileFormat.signedIntegerFromUnsigned_toUnsigned]

theorem decodeTableInterior_encodeChunkRoot_branch3 (schema : Core.Schema)
    (pageId : Nat) (left : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (firstSeparator : Nat)
    (middle : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (secondSeparator : Nat)
    (right : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (root : NumberedPage) (leftPositive : 0 < left.rootId)
    (middlePositive : 0 < middle.rootId)
    (built : encodeChunkRoot schema
      (.branch3 pageId left firstSeparator middle secondSeparator right) =
        some root) :
    ∃ leftBoundary middleBoundary,
      (CoreChunkPageState.Node.rows left).getLast? = some leftBoundary ∧
      (CoreChunkPageState.Node.rows middle).getLast? = some middleBoundary ∧
      CoreDecode.decodeTableInterior? root.page.bytes = some
        ([(left.rootId, leftBoundary.rowid),
          (middle.rootId, middleBoundary.rowid)], right.rootId) := by
  simp only [encodeChunkRoot] at built
  cases leftKeyResult : maximumChunkRowid? left with
  | none => simp [leftKeyResult] at built
  | some leftKey =>
      simp only [leftKeyResult, Option.bind_eq_bind, Option.bind] at built
      cases middleKeyResult : maximumChunkRowid? middle with
      | none => simp [middleKeyResult] at built
      | some middleKey =>
          simp only [middleKeyResult] at built
          cases pageResult : RecursivePageBTree.interiorPage?
              [(left.rootId, leftKey), (middle.rootId, middleKey)]
                right.rootId with
          | none => simp [pageResult] at built
          | some page =>
              simp only [pageResult, Option.some.injEq] at built
              subst root
              rcases maximumChunkRowid?_witness leftKeyResult with
                ⟨leftBoundary, leftLast, rfl⟩
              rcases maximumChunkRowid?_witness middleKeyResult with
                ⟨middleBoundary, middleLast, rfl⟩
              refine ⟨leftBoundary, middleBoundary, leftLast, middleLast, ?_⟩
              have leftKeyBound : leftBoundary.rowid.toUnsigned < 2 ^ 64 := by
                simpa [FileFormat.IntegerWidth.modulus] using
                  leftBoundary.rowid.toUnsigned_lt
              have middleKeyBound :
                  middleBoundary.rowid.toUnsigned < 2 ^ 64 := by
                simpa [FileFormat.IntegerWidth.modulus] using
                  middleBoundary.rowid.toUnsigned_lt
              rw [decodeTableInterior_interiorPage_two leftPositive
                middlePositive leftKeyBound middleKeyBound pageResult]
              simp [FileFormat.signedIntegerFromUnsigned_toUnsigned]

/-- A page source contains an encoded page set when reading every advertised
page identity returns exactly the bytes emitted for that identity. -/
def PageSourceContains (source : CoreDecode.PageSource)
    (pages : List NumberedPage) : Prop :=
  ∀ numbered ∈ pages,
    source.readPage numbered.pageNumber = some numbered.page.bytes

theorem PageSourceContains.ofReadsRange (source : CoreDecode.PageSource) :
    ∀ (start : Nat) (pages : List NumberedPage),
      pages.map NumberedPage.pageNumber = List.range' start pages.length →
      CoreDecode.ReadsPagesFrom source start
        (pages.map NumberedPage.page) →
      PageSourceContains source pages
  | _, [], _, _ => by simp [PageSourceContains]
  | start, page :: pages, numbers, reads => by
      change page.pageNumber :: pages.map NumberedPage.pageNumber =
        start :: List.range' (start + 1) pages.length at numbers
      injection numbers with pageNumber tailNumbers
      have headRead : source.readPage start = some page.page.bytes := by
        have available := reads 0 (by simp)
        simpa using available
      have tailReads : CoreDecode.ReadsPagesFrom source (start + 1)
          (pages.map NumberedPage.page) := by
        have remaining := CoreDecode.ReadsPagesFrom.right
          (left := [page.page]) (right := pages.map NumberedPage.page) reads
        simpa using remaining
      have tailContains := ofReadsRange source (start + 1) pages tailNumbers
        tailReads
      intro numbered member
      simp only [List.mem_cons] at member
      rcases member with equal | later
      · subst numbered
        simpa [pageNumber] using headRead
      · exact tailContains numbered later

theorem interiorChildren_encodeChunkRoot_branch2 (schema : Core.Schema)
    (pageId : Nat) (left : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (separator : Nat)
    (right : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (root : NumberedPage)
    (built : encodeChunkRoot schema
      (.branch2 pageId left separator right) = some root) :
    CoreDecode.interiorChildren? root.page.bytes =
      some [left.rootId, right.rootId] := by
  simp only [encodeChunkRoot] at built
  cases keyResult : maximumChunkRowid? left with
  | none => simp [keyResult] at built
  | some key =>
    simp only [keyResult, Option.bind_eq_bind, Option.bind] at built
    cases pageResult : RecursivePageBTree.interiorPage?
        [(left.rootId, key)] right.rootId with
    | none => simp [pageResult] at built
    | some page =>
      simp only [pageResult, Option.some.injEq] at built
      subst root
      exact interiorChildren_interiorPage_one pageResult

theorem interiorChildren_encodeChunkRoot_branch3 (schema : Core.Schema)
    (pageId : Nat) (left : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (firstSeparator : Nat)
    (middle : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (secondSeparator : Nat)
    (right : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (root : NumberedPage)
    (built : encodeChunkRoot schema
      (.branch3 pageId left firstSeparator middle secondSeparator right) =
        some root) :
    CoreDecode.interiorChildren? root.page.bytes =
      some [left.rootId, middle.rootId, right.rootId] := by
  simp only [encodeChunkRoot] at built
  cases leftResult : maximumChunkRowid? left with
  | none => simp [leftResult] at built
  | some leftKey =>
    simp only [leftResult, Option.bind_eq_bind, Option.bind] at built
    cases middleResult : maximumChunkRowid? middle with
    | none => simp [middleResult] at built
    | some middleKey =>
      simp only [middleResult] at built
      cases pageResult : RecursivePageBTree.interiorPage?
          [(left.rootId, leftKey), (middle.rootId, middleKey)] right.rootId with
      | none => simp [pageResult] at built
      | some page =>
        simp only [pageResult, Option.some.injEq] at built
        subst root
        exact interiorChildren_interiorPage_two pageResult

def encodeChunkPath (schema : Core.Schema) (key : Nat) :
    PersistentPageTree.Node CoreChunkPageState.Chunk →
      Option (List NumberedPage)
  | node@(.leaf ..) => do
      let page ← encodeChunkRoot schema node
      some [page]
  | node@(.branch2 _ left separator right) => do
      let page ← encodeChunkRoot schema node
      let child ← if key < separator then encodeChunkPath schema key left
        else encodeChunkPath schema key right
      some (page :: child)
  | node@(.branch3 _ left firstSeparator middle secondSeparator right) => do
      let page ← encodeChunkRoot schema node
      let child ← if key < firstSeparator then encodeChunkPath schema key left
        else if key < secondSeparator then encodeChunkPath schema key middle
        else encodeChunkPath schema key right
      some (page :: child)

theorem encodeChunkPath_eq_mapM (schema : Core.Schema) (key : Nat)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk) :
    encodeChunkPath schema key node =
      (physicalChunkPath key node).mapM (encodePhysicalChunkPage schema) := by
  induction node with
  | leaf pageId entries =>
      simp only [encodeChunkPath, physicalChunkPath, List.mapM_cons,
        List.mapM_nil, pure, Option.pure_def]
      rw [encodeChunkRoot_eq_encodePhysicalChunkRoot]
      cases result : encodePhysicalChunkPage schema
          (physicalChunkRoot (.leaf pageId entries)) <;>
        simp [encodeChunkPath, physicalChunkPath, result]
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [encodeChunkPath, physicalChunkPath, List.mapM_cons]
      rw [encodeChunkRoot_eq_encodePhysicalChunkRoot]
      by_cases route : key < separator
      · rw [if_pos route]
        rw [leftInduction]
        cases rootResult : encodePhysicalChunkPage schema
            (physicalChunkRoot (.branch2 pageId left separator right)) with
        | none =>
          simp [encodeChunkPath, physicalChunkPath, route, rootResult]
        | some root =>
          cases childResult : (physicalChunkPath key left).mapM
              (encodePhysicalChunkPage schema) <;>
            simp [encodeChunkPath, physicalChunkPath, route, rootResult,
              childResult]
      · rw [if_neg route]
        rw [rightInduction]
        cases rootResult : encodePhysicalChunkPage schema
            (physicalChunkRoot (.branch2 pageId left separator right)) with
        | none =>
          simp [encodeChunkPath, physicalChunkPath, route, rootResult]
        | some root =>
          cases childResult : (physicalChunkPath key right).mapM
              (encodePhysicalChunkPage schema) <;>
            simp [encodeChunkPath, physicalChunkPath, route, rootResult,
              childResult]
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [encodeChunkPath, physicalChunkPath, List.mapM_cons]
      rw [encodeChunkRoot_eq_encodePhysicalChunkRoot]
      by_cases leftRoute : key < firstSeparator
      · rw [if_pos leftRoute]
        rw [leftInduction]
        cases rootResult : encodePhysicalChunkPage schema
            (physicalChunkRoot (.branch3 pageId left firstSeparator middle
              secondSeparator right)) with
        | none =>
          simp [encodeChunkPath, physicalChunkPath, leftRoute, rootResult]
        | some root =>
          cases childResult : (physicalChunkPath key left).mapM
              (encodePhysicalChunkPage schema) <;>
            simp [encodeChunkPath, physicalChunkPath, leftRoute, rootResult,
              childResult]
      · rw [if_neg leftRoute]
        by_cases middleRoute : key < secondSeparator
        · rw [if_pos middleRoute]
          rw [middleInduction]
          cases rootResult : encodePhysicalChunkPage schema
              (physicalChunkRoot (.branch3 pageId left firstSeparator middle
                secondSeparator right)) with
          | none =>
            simp [encodeChunkPath, physicalChunkPath, leftRoute, middleRoute,
              rootResult]
          | some root =>
            cases childResult : (physicalChunkPath key middle).mapM
                (encodePhysicalChunkPage schema) <;>
              simp [encodeChunkPath, physicalChunkPath, leftRoute, middleRoute,
                rootResult, childResult]
        · rw [if_neg middleRoute]
          rw [rightInduction]
          cases rootResult : encodePhysicalChunkPage schema
              (physicalChunkRoot (.branch3 pageId left firstSeparator middle
                secondSeparator right)) with
          | none =>
            simp [encodeChunkPath, physicalChunkPath, leftRoute, middleRoute,
              rootResult]
          | some root =>
            cases childResult : (physicalChunkPath key right).mapM
                (encodePhysicalChunkPage schema) <;>
              simp [encodeChunkPath, physicalChunkPath, leftRoute, middleRoute,
                rootResult, childResult]

theorem physicalChunkPages_accounted_of_pathAgrees (key : Nat)
    {before after : PersistentPageTree.Node CoreChunkPageState.Chunk}
    (agrees : PersistentPageTree.Node.PathAgrees key before after) :
    ∀ descriptor ∈ physicalChunkPages after,
      descriptor ∈ physicalChunkPath key after ∨
        descriptor ∈ physicalChunkPages before := by
  induction agrees with
  | leaf pageId beforeEntries afterEntries =>
      intro descriptor member
      simp only [physicalChunkPages, List.mem_singleton] at member
      subst descriptor
      exact .inl (by simp [physicalChunkPath, physicalChunkRoot])
  | branch2Left pageId beforeChild afterChild separator right route child
      induction =>
      intro descriptor member
      rw [physicalChunkPages] at member
      rcases List.mem_cons.mp member with root | descendants
      · exact .inl (by
          rw [physicalChunkPath, if_pos route]
          exact List.mem_cons.mpr (.inl root))
      rcases List.mem_append.mp descendants with inChild | inRight
      · rcases induction descriptor inChild with inPath | inBefore
        · exact .inl (by
            rw [physicalChunkPath, if_pos route]
            exact List.mem_cons.mpr (.inr inPath))
        · exact .inr (by
            rw [physicalChunkPages]
            exact List.mem_cons.mpr
              (.inr (List.mem_append.mpr (.inl inBefore))))
      · exact .inr (by
          rw [physicalChunkPages]
          exact List.mem_cons.mpr
            (.inr (List.mem_append.mpr (.inr inRight))))
  | branch2Right pageId left separator beforeChild afterChild route child
      induction =>
      intro descriptor member
      rw [physicalChunkPages] at member
      rcases List.mem_cons.mp member with root | descendants
      · exact .inl (by
          rw [physicalChunkPath, if_neg route]
          exact List.mem_cons.mpr (.inl root))
      rcases List.mem_append.mp descendants with inLeft | inChild
      · exact .inr (by
          rw [physicalChunkPages]
          exact List.mem_cons.mpr
            (.inr (List.mem_append.mpr (.inl inLeft))))
      · rcases induction descriptor inChild with inPath | inBefore
        · exact .inl (by
            rw [physicalChunkPath, if_neg route]
            exact List.mem_cons.mpr (.inr inPath))
        · exact .inr (by
            rw [physicalChunkPages]
            exact List.mem_cons.mpr
              (.inr (List.mem_append.mpr (.inr inBefore))))
  | branch3Left pageId beforeChild afterChild firstSeparator middle
      secondSeparator right route child induction =>
      intro descriptor member
      rw [physicalChunkPages] at member
      rcases List.mem_cons.mp member with root | descendants
      · exact .inl (by
          rw [physicalChunkPath, if_pos route]
          exact List.mem_cons.mpr (.inl root))
      rcases List.mem_append.mp descendants with leftAndMiddle | inRight
      rcases List.mem_append.mp leftAndMiddle with inChild | inMiddle
      · rcases induction descriptor inChild with inPath | inBefore
        · exact .inl (by
            rw [physicalChunkPath, if_pos route]
            exact List.mem_cons.mpr (.inr inPath))
        · exact .inr (by
            rw [physicalChunkPages]
            exact List.mem_cons.mpr (.inr
              (List.mem_append.mpr (.inl
                (List.mem_append.mpr (.inl inBefore))))))
      · exact .inr (by
          rw [physicalChunkPages]
          exact List.mem_cons.mpr (.inr
            (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr inMiddle))))))
      · exact .inr (by
          rw [physicalChunkPages]
          exact List.mem_cons.mpr
            (.inr (List.mem_append.mpr (.inr inRight))))
  | branch3Middle pageId left firstSeparator beforeChild afterChild
      secondSeparator right leftRoute route child induction =>
      intro descriptor member
      rw [physicalChunkPages] at member
      rcases List.mem_cons.mp member with root | descendants
      · exact .inl (by
          rw [physicalChunkPath, if_neg leftRoute, if_pos route]
          exact List.mem_cons.mpr (.inl root))
      rcases List.mem_append.mp descendants with leftAndMiddle | inRight
      rcases List.mem_append.mp leftAndMiddle with inLeft | inChild
      · exact .inr (by
          rw [physicalChunkPages]
          exact List.mem_cons.mpr (.inr
            (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inl inLeft))))))
      · rcases induction descriptor inChild with inPath | inBefore
        · exact .inl (by
            rw [physicalChunkPath, if_neg leftRoute, if_pos route]
            exact List.mem_cons.mpr (.inr inPath))
        · exact .inr (by
            rw [physicalChunkPages]
            exact List.mem_cons.mpr (.inr
              (List.mem_append.mpr (.inl
                (List.mem_append.mpr (.inr inBefore))))))
      · exact .inr (by
          rw [physicalChunkPages]
          exact List.mem_cons.mpr
            (.inr (List.mem_append.mpr (.inr inRight))))
  | branch3Right pageId left firstSeparator middle secondSeparator beforeChild
      afterChild leftRoute middleRoute child induction =>
      intro descriptor member
      rw [physicalChunkPages] at member
      rcases List.mem_cons.mp member with root | descendants
      · exact .inl (by
          rw [physicalChunkPath, if_neg leftRoute, if_neg middleRoute]
          exact List.mem_cons.mpr (.inl root))
      rcases List.mem_append.mp descendants with leftAndMiddle | inChild
      rcases List.mem_append.mp leftAndMiddle with inLeft | inMiddle
      · exact .inr (by
          rw [physicalChunkPages]
          exact List.mem_cons.mpr (.inr
            (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inl inLeft))))))
      · exact .inr (by
          rw [physicalChunkPages]
          exact List.mem_cons.mpr (.inr
            (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr inMiddle))))))
      · rcases induction descriptor inChild with inPath | inBefore
        · exact .inl (by
            rw [physicalChunkPath, if_neg leftRoute, if_neg middleRoute]
            exact List.mem_cons.mpr (.inr inPath))
        · exact .inr (by
            rw [physicalChunkPages]
            exact List.mem_cons.mpr
              (.inr (List.mem_append.mpr (.inr inBefore))))

/-- Search-path counterpart of `exists_encodeChunkNode_of_changed`.  A local
path encoder proves every changed descriptor encodable; `PathAgrees` supplies
the unchanged subtrees from the successful pre-state encoding. -/
theorem exists_encodeChunkNode_of_pathAgrees
    (schema : Core.Schema) (key : Nat)
    {before after : PersistentPageTree.Node CoreChunkPageState.Chunk}
    (path beforePages : List NumberedPage)
    (agrees : PersistentPageTree.Node.PathAgrees key before after)
    (pathEncoded : encodeChunkPath schema key after = some path)
    (beforeEncoded : encodeChunkNode schema before = some beforePages) :
    ∃ afterPages, encodeChunkNode schema after = some afterPages := by
  rw [encodeChunkPath_eq_mapM] at pathEncoded
  rw [encodeChunkNode_eq_mapM] at beforeEncoded ⊢
  apply exists_mapM_of_forall_some
  intro descriptor descriptorMember
  rcases physicalChunkPages_accounted_of_pathAgrees key agrees descriptor
      descriptorMember with inPath | inBefore
  · rcases mapM_encodePhysicalChunkPage_input schema pathEncoded descriptor
        inPath with ⟨page, _, encoded⟩
    exact ⟨page, encoded⟩
  · rcases mapM_encodePhysicalChunkPage_input schema beforeEncoded descriptor
        inBefore with ⟨page, _, encoded⟩
    exact ⟨page, encoded⟩

/-- If two persistent trees differ only along one search path, encoding that
post-state path accounts for every new byte image.  Pages off the path are
present byte-for-byte in the complete pre-state encoding. -/
theorem encodeChunkPath_accounts_of_pathAgrees (schema : Core.Schema)
    (key : Nat)
    {before after : PersistentPageTree.Node CoreChunkPageState.Chunk}
    (path beforePages afterPages : List NumberedPage)
    (agrees : PersistentPageTree.Node.PathAgrees key before after)
    (pathEncoded : encodeChunkPath schema key after = some path)
    (beforeEncoded : encodeChunkNode schema before = some beforePages)
    (afterEncoded : encodeChunkNode schema after = some afterPages) :
    ∀ page ∈ afterPages, page ∈ path ∨ page ∈ beforePages := by
  rw [encodeChunkPath_eq_mapM] at pathEncoded
  rw [encodeChunkNode_eq_mapM] at beforeEncoded afterEncoded
  intro page pageMember
  rcases mapM_encodePhysicalChunkPage_output schema afterEncoded page
      pageMember with ⟨descriptor, descriptorMember, descriptorEncoded⟩
  rcases physicalChunkPages_accounted_of_pathAgrees key agrees descriptor
      descriptorMember with inPath | inBefore
  · left
    rcases mapM_encodePhysicalChunkPage_input schema pathEncoded descriptor
        inPath with ⟨selected, selectedMember, selectedEncoded⟩
    have equal : selected = page := Option.some.inj
      (selectedEncoded.symm.trans descriptorEncoded)
    simpa [equal] using selectedMember
  · right
    rcases mapM_encodePhysicalChunkPage_input schema beforeEncoded descriptor
        inBefore with ⟨old, oldMember, oldEncoded⟩
    have equal : old = page := Option.some.inj
      (oldEncoded.symm.trans descriptorEncoded)
    simpa [equal] using oldMember

end CorePageCodec

end SQLeanite
