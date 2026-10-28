import SQLeanite.CorePageCodec.DecodeTableInteriorEncodeChunkRootBranch2
import SQLeanite.CoreWideIndex.Cell
import SQLeanite.WidePageTree.NumberedBranchesRootNePendingBytePage

namespace SQLeanite
namespace CoreWideIndex

theorem promoteChildren_toCells {fuel : Nat} {children : List Node}
    {initial : List (Node × Cell)} {rightmost : Node}
    (success : promoteChildren fuel children = some (initial, rightmost)) :
    pairsToCells initial ++ rightmost.toCells =
      (children.map Node.toCells).flatten := by
  induction children generalizing initial rightmost with
  | nil => simp [promoteChildren] at success
  | cons child children induction =>
      cases children with
      | nil =>
          simp only [promoteChildren, Option.some.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          simp [pairsToCells]
      | cons next rest =>
          simp only [promoteChildren, Option.bind_eq_bind, Option.bind] at success
          cases popped : child.popMaxStep fuel with
          | none => simp [popped] at success
          | some pair =>
              rcases pair with ⟨updated, separator⟩
              simp only [popped] at success
              cases recursive : promoteChildren fuel (next :: rest) with
              | none => simp [recursive] at success
              | some result =>
                  rcases result with ⟨remaining, final⟩
                  simp only [recursive, Option.some.injEq, Prod.mk.injEq]
                    at success
                  rcases success with ⟨rfl, rfl⟩
                  simp only [pairsToCells, List.map_cons, List.flatten_cons]
                  calc
                    updated.toCells ++ separator :: pairsToCells remaining ++
                        final.toCells =
                      (updated.toCells ++ [separator]) ++
                        (pairsToCells remaining ++ final.toCells) := by
                          simp [List.append_assoc]
                    _ = (updated.toCells ++ [separator]) ++
                        (List.map Node.toCells (next :: rest)).flatten := by
                          rw [induction recursive]
                    _ = child.toCells ++
                        (List.map Node.toCells (next :: rest)).flatten := by
                          rw [Node.popMaxStep_toCells popped]
                    _ = child.toCells ++
                        (next.toCells ++
                          (List.map Node.toCells rest).flatten) := by
                          rfl

mutual
  def fromWideStep : Nat → WidePageTree.Node Leaf → Option Node
    | 0, _ => none
    | _ + 1, .leaf pageId entries =>
        some (.leaf pageId (entries.flatMap fun entry => entry.2))
    | fuel + 1, .branch pageId children => do
        let converted ← fromWideChildren fuel children
        let (initial, rightmost) ← promoteChildren fuel converted
        some (.branch pageId initial rightmost)

  def fromWideChildren : Nat → List (WidePageTree.Node Leaf) →
      Option (List Node)
    | _, [] => some []
    | fuel, child :: children => do
        let converted ← fromWideStep fuel child
        let remaining ← fromWideChildren fuel children
        some (converted :: remaining)
end

theorem fromWideChildren_toCells_of {fuel : Nat}
    (exactChild : ∀ (child : WidePageTree.Node Leaf) (converted : Node),
      fromWideStep fuel child = some converted →
        converted.toCells = child.toList.flatMap Prod.snd) :
    ∀ (children : List (WidePageTree.Node Leaf)) (converted : List Node),
      fromWideChildren fuel children = some converted →
      (converted.map Node.toCells).flatten =
        (children.map fun child => child.toList.flatMap Prod.snd).flatten
  | [], converted, success => by
      simp only [fromWideChildren, Option.some.injEq] at success
      subst converted
      rfl
  | child :: children, converted, success => by
      simp only [fromWideChildren, Option.bind_eq_bind, Option.bind] at success
      cases headResult : fromWideStep fuel child with
      | none => simp [headResult] at success
      | some head =>
          simp only [headResult] at success
          cases tailResult : fromWideChildren fuel children with
          | none => simp [tailResult] at success
          | some tail =>
              simp only [tailResult, Option.some.injEq] at success
              subst converted
              simp only [List.map_cons, List.flatten_cons]
              rw [exactChild child head headResult,
                fromWideChildren_toCells_of exactChild children tail tailResult]

theorem fromWideStep_toCells : ∀ (fuel : Nat)
    (wide : WidePageTree.Node Leaf) (converted : Node),
    fromWideStep fuel wide = some converted →
      converted.toCells = wide.toList.flatMap Prod.snd := by
  intro fuel
  induction fuel with
  | zero =>
      intro wide converted success
      simp [fromWideStep] at success
  | succ fuel induction =>
      intro wide converted success
      cases wide with
      | leaf pageId entries =>
          simp only [fromWideStep, Option.some.injEq] at success
          subst converted
          simp [Node.toCells, WidePageTree.Node.toList]
      | branch pageId children =>
          simp only [fromWideStep, Option.bind_eq_bind, Option.bind] at success
          cases childrenResult : fromWideChildren fuel children with
          | none => simp [childrenResult] at success
          | some convertedChildren =>
              simp only [childrenResult] at success
              cases promotedResult : promoteChildren fuel convertedChildren with
              | none => simp [promotedResult] at success
              | some promoted =>
                  rcases promoted with ⟨initial, rightmost⟩
                  simp only [promotedResult, Option.some.injEq] at success
                  subst converted
                  simp only [Node.toCells, WidePageTree.Node.toList]
                  rw [promoteChildren_toCells promotedResult,
                    fromWideChildren_toCells_of induction children
                      convertedChildren childrenResult]
                  change children.flatMap
                      (fun child => child.toList.flatMap Prod.snd) =
                    (children.flatMap WidePageTree.Node.toList).flatMap Prod.snd
                  exact List.flatMap_assoc.symm

def leafEntries (leaves : List Leaf) : List (PagedBTree.Entry Leaf) :=
  leaves.mapIdx fun index leaf => (index, leaf)

theorem leafEntries_values (leaves : List Leaf) :
    (leafEntries leaves).flatMap Prod.snd = leaves.flatten := by
  unfold leafEntries
  rw [List.mapIdx_eq_zipIdx_map, List.flatMap_map]
  simp only [Function.comp_apply]
  change (leaves.zipIdx.map Prod.fst).flatten = leaves.flatten
  rw [List.zipIdx_map_fst]

structure Store where
  root : Node
  startPage : Nat
  nextPage : Nat
  cells : List Cell
  startLeNext : startPage ≤ nextPage
  represents : root.toCells = cells

def Store.build? (startPage : Nat) (cells : List Cell) : Option Store := do
  let leaves := CellPagination.paginateCells cells
  let fanout := interiorFanoutFor cells
  match built : WidePageTree.buildNumberedWithFanout fanout startPage
      (leafEntries leaves) with
  | none => none
  | some (wide, nextPage) =>
      match converted : fromWideStep (wide.height + 1) wide with
      | none => none
      | some root => some {
          root
          startPage
          nextPage
          cells
          startLeNext := WidePageTree.buildNumberedWithFanout_after_ge built
          represents := by
            rw [fromWideStep_toCells _ wide root converted,
              WidePageTree.buildNumberedWithFanout_toList built,
              leafEntries_values,
              CellPagination.flatten_paginateCells] }

theorem Store.build?_cells {startPage : Nat} {cells : List Cell}
    {store : Store} (built : Store.build? startPage cells = some store) :
    store.cells = cells := by
  simp only [Store.build?] at built
  split at built <;> try contradiction
  all_goals split at built <;> try contradiction
  all_goals
    injection built with equal
    exact congrArg Store.cells equal.symm

theorem Store.build?_startPage {startPage : Nat} {cells : List Cell}
    {store : Store} (built : Store.build? startPage cells = some store) :
    store.startPage = startPage := by
  simp only [Store.build?] at built
  split at built <;> try contradiction
  all_goals split at built <;> try contradiction
  all_goals
    injection built with equal
    exact congrArg Store.startPage equal.symm

def encodeRoot : Node → Option CorePageCodec.NumberedPage
  | .leaf pageId cells => do
      let page ← CoreFile.indexLeafPage? cells
      some ⟨pageId, page⟩
  | .branch pageId initial rightmost => do
      let page ← RecursivePageBTree.indexInteriorPage?
        (initial.map fun pair => (pair.1.rootId, pair.2)) rightmost.rootId
      some ⟨pageId, page⟩

def branchChildren (initial : List (Node × Cell)) (rightmost : Node) :
    List Node := initial.map Prod.fst ++ [rightmost]

mutual
  def Node.encodePagesStep : Nat → Node →
      Option (List CorePageCodec.NumberedPage)
    | 0, _ => none
    | _ + 1, node@(.leaf _ _) => do
        let page ← encodeRoot node
        some [page]
    | fuel + 1, node@(.branch _ initial rightmost) => do
        let page ← encodeRoot node
        let descendants ← encodeChildren fuel
          (branchChildren initial rightmost)
        some (page :: descendants)

  def encodeChildren : Nat → List Node →
      Option (List CorePageCodec.NumberedPage)
    | _, [] => some []
    | fuel, child :: children => do
        let pages ← child.encodePagesStep fuel
        let remaining ← encodeChildren fuel children
        some (pages ++ remaining)
end

def Node.encodePages (node : Node) :
    Option (List CorePageCodec.NumberedPage) :=
  node.encodePagesStep (node.pageIds.length + 1)

theorem encodeChildren_length_of {fuel : Nat}
    (nodeLength : ∀ (node : Node)
      (pages : List CorePageCodec.NumberedPage),
      node.encodePagesStep fuel = some pages →
      pages.length = node.pageIds.length) :
    ∀ (nodes : List Node) (pages : List CorePageCodec.NumberedPage),
      encodeChildren fuel nodes = some pages →
      pages.length = (nodes.flatMap Node.pageIds).length
  | [], pages, success => by
      simp only [encodeChildren, Option.some.injEq] at success
      subst pages
      rfl
  | node :: nodes, pages, success => by
      simp only [encodeChildren, Option.bind_eq_bind, Option.bind] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨headPages, headResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨tailPages, tailResult, equal⟩
      simp only [pure, Pure.pure, Option.some.injEq] at equal
      subst pages
      simp only [List.length_append, List.flatMap_cons]
      rw [nodeLength node headPages headResult,
        encodeChildren_length_of nodeLength nodes tailPages tailResult]

theorem Node.encodePagesStep_length : ∀ (fuel : Nat) (node : Node)
    (pages : List CorePageCodec.NumberedPage),
    node.encodePagesStep fuel = some pages →
    pages.length = node.pageIds.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro node pages success
      simp [Node.encodePagesStep] at success
  | succ fuel induction =>
      intro node pages success
      cases node with
      | leaf pageId cells =>
          simp only [Node.encodePagesStep, Option.bind_eq_bind, Option.bind]
            at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨page, _, equal⟩
          simp only [Option.some.injEq] at equal
          subst pages
          rfl
      | branch pageId initial rightmost =>
          simp only [Node.encodePagesStep, Option.bind_eq_bind, Option.bind]
            at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨page, _, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨childPages, childrenResult, equal⟩
          simp only [Option.some.injEq] at equal
          subst pages
          have childrenLength := encodeChildren_length_of induction
            (branchChildren initial rightmost) childPages childrenResult
          simp only [List.length_cons, Node.pageIds]
          rw [childrenLength]
          unfold branchChildren
          simp only [List.flatMap_append, List.flatMap_map,
            Function.comp_apply, List.flatMap_singleton]
          rw [pairsPageIds_eq_flatMap]
          simp only [List.length_cons, List.length_append]
          omega

theorem Node.encodePages_length {node : Node}
    {pages : List CorePageCodec.NumberedPage}
    (success : node.encodePages = some pages) :
    pages.length = node.pageIds.length :=
  Node.encodePagesStep_length _ _ _ success

theorem encodeChildren_member {fuel : Nat} {children : List Node}
    {pages : List CorePageCodec.NumberedPage}
    (encoded : encodeChildren fuel children = some pages) {child : Node}
    (member : child ∈ children) :
    ∃ childPages, child.encodePagesStep fuel = some childPages ∧
      ∀ page ∈ childPages, page ∈ pages := by
  induction children generalizing pages with
  | nil => simp at member
  | cons head tail induction =>
      simp only [encodeChildren, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : head.encodePagesStep fuel with
      | none => simp [headResult] at encoded
      | some headPages =>
          simp only [headResult] at encoded
          cases tailResult : encodeChildren fuel tail with
          | none => simp [tailResult] at encoded
          | some tailPages =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst pages
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact ⟨headPages, headResult,
                  fun page pageMember => List.mem_append_left _ pageMember⟩
              · rcases induction tailResult member with
                  ⟨childPages, childResult, subset⟩
                exact ⟨childPages, childResult,
                  fun page pageMember => by simp [subset page pageMember]⟩

theorem decodeIndexSubtreeFrom_encodePagesStep
    (source : CoreDecode.PageSource) : ∀ (encodeFuel : Nat) (node : Node)
      (pages : List CorePageCodec.NumberedPage)
      (entries : List CoreDecode.IndexEntry) (decodeFuel : Nat),
      node.encodePagesStep encodeFuel = some pages →
      CorePageCodec.PageSourceContains source pages →
      NodeDecodes source (source.pageCount + 1) node entries →
      encodeFuel ≤ decodeFuel →
      CoreDecode.decodeIndexSubtreeFrom source decodeFuel node.rootId =
        some entries
  | 0, _, _, _, _, encoded, _, _, _ => by
      simp [Node.encodePagesStep] at encoded
  | encodeFuel + 1, node@(.leaf pageId cells), pages, entries, decodeFuel,
      encoded, contains, decoded, fuelBound => by
      subst node
      simp only [Node.encodePagesStep, Option.bind_eq_bind, Option.bind]
        at encoded
      rcases Option.bind_eq_some_iff.mp encoded with
        ⟨numbered, pageResult, equal⟩
      simp only [Option.some.injEq] at equal
      subst pages
      cases decodeFuel with
      | zero => omega
      | succ childFuel =>
          cases decoded with
          | leaf cellsDecoded =>
              unfold encodeRoot at pageResult
              cases leafResult : CoreFile.indexLeafPage? cells with
              | none => simp [leafResult] at pageResult
              | some page =>
                simp only [leafResult, Option.some.injEq] at pageResult
                simp only [Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at pageResult
                subst numbered
                simp only [CoreDecode.decodeIndexSubtreeFrom, Node.rootId]
                have rootRead := contains ⟨pageId, page⟩ (by simp)
                rw [rootRead]
                simp only [Option.bind_eq_bind, Option.bind]
                rw [CoreDecode.decodeIndexInteriorFrom_indexLeafPage
                  source leafResult]
                exact CoreDecode.decodeIndexLeafFrom_indexLeafPage source
                  cellsDecoded leafResult
  | encodeFuel + 1, node@(.branch pageId initial rightmost), pages, entries,
      decodeFuel, encoded, contains, decoded, fuelBound => by
      subst node
      simp only [Node.encodePagesStep, Option.bind_eq_bind, Option.bind]
        at encoded
      rcases Option.bind_eq_some_iff.mp encoded with
        ⟨root, rootResult, encoded⟩
      rcases Option.bind_eq_some_iff.mp encoded with
        ⟨childPages, childrenResult, equal⟩
      simp only [Option.some.injEq] at equal
      subst pages
      cases decodeFuel with
      | zero => omega
      | succ childFuel =>
          have childFuelBound : encodeFuel ≤ childFuel := by omega
          have descendantContains :
              CorePageCodec.PageSourceContains source childPages := by
            intro page member
            exact contains page (by simp [member])
          have exactChild : ∀ {child : Node}
              {childEntries : List CoreDecode.IndexEntry},
              child ∈ branchChildren initial rightmost →
              NodeDecodes source (source.pageCount + 1) child childEntries →
              CoreDecode.decodeIndexSubtreeFrom source childFuel
                  child.rootId = some childEntries := by
            intro child childEntries member childDecoded
            rcases encodeChildren_member childrenResult member with
              ⟨encodedPages, childEncoded, subset⟩
            have childContains :
                CorePageCodec.PageSourceContains source encodedPages := by
              intro page pageMember
              exact descendantContains page (subset page pageMember)
            exact decodeIndexSubtreeFrom_encodePagesStep source
              encodeFuel child encodedPages childEntries childFuel
              childEncoded childContains childDecoded childFuelBound
          cases decoded with
          | @branch _ _ _ groups rightEntries initialDecoded rightDecoded =>
              unfold encodeRoot at rootResult
              cases built : RecursivePageBTree.indexInteriorPage?
                  (initial.map fun pair =>
                    (pair.1.rootId, pair.2)) rightmost.rootId with
              | none => simp [built] at rootResult
              | some page =>
                  simp only [built, Option.some.injEq] at rootResult
                  simp only [Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at rootResult
                  subst root
                  have rootRead := contains ⟨pageId, page⟩ (by simp)
                  simp only [CoreDecode.decodeIndexSubtreeFrom, Node.rootId]
                  rw [rootRead]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [decodeIndexInteriorFrom_widePage source
                    initialDecoded.interior built]
                  have groupsExact := initialDecoded.mapM_exact
                    (fun {node} {cell} member {entries} childDecoded =>
                      exactChild (child := node) (childEntries := entries) (by
                        unfold branchChildren
                        apply List.mem_append_left
                        exact List.mem_map_of_mem member) childDecoded)
                  change (do
                    let decodedGroups ← (interiorEntries initial groups).mapM
                      (fun entry => do
                        let left ← CoreDecode.decodeIndexSubtreeFrom source
                          childFuel entry.1
                        some (left ++ [entry.2]))
                    let right ← CoreDecode.decodeIndexSubtreeFrom source
                      childFuel rightmost.rootId
                    some (decodedGroups.flatten ++ right)) =
                      some (groupEntries groups ++ rightEntries)
                  rw [groupsExact]
                  have rightExact := exactChild (child := rightmost)
                    (by simp [branchChildren]) rightDecoded
                  rw [rightExact]
                  unfold groupEntries
                  have flattened := flatten_map_eq_flatMap groups
                    (fun group => group.1 ++ [group.2])
                  have appended := congrArg (fun values =>
                    values ++ rightEntries) flattened
                  simpa using appended

theorem decodeIndexSubtreeFrom_encodePages
    (source : CoreDecode.PageSource) {node : Node}
    {pages : List CorePageCodec.NumberedPage}
    {entries : List CoreDecode.IndexEntry}
    (encoded : node.encodePages = some pages)
    (contains : CorePageCodec.PageSourceContains source pages)
    (decoded : NodeDecodes source (source.pageCount + 1) node entries)
    (fuelBound : node.pageIds.length < source.pageCount + 1) :
    CoreDecode.decodeIndexSubtreeFrom source (source.pageCount + 1)
        node.rootId = some entries := by
  exact decodeIndexSubtreeFrom_encodePagesStep source
    (node.pageIds.length + 1) node pages entries (source.pageCount + 1)
    encoded contains decoded (by omega)

end CoreWideIndex

end SQLeanite
