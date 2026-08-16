import SQLeanite.CoreWidePageState
import SQLeanite.CorePageCodec

namespace SQLeanite
namespace CoreWideIndex

/-!
# High-fanout physical index pages

SQLite index interior cells are promoted records, not synthetic separators.
This module therefore cannot reuse the table encoder verbatim: construction
starts with page-packed leaves, gives them the same 256-way physical topology,
then removes the greatest record from every non-rightmost child and stores that
record in its parent.  `Node.toCells` includes those promoted records exactly
once.
-/

abbrev Cell := List UInt8
abbrev Leaf := List Cell

/-- Child capacity for promoted-key interior pages.  Unlike table rowid
separators, index separators contain the full encoded key.  An interior cell
costs its record bytes plus a four-byte child pointer and a two-byte cell-array
pointer; the 12-byte interior header is paid once. -/
def interiorFanoutFor (cells : List Cell) : Nat :=
  let widest := cells.foldl (fun width cell => max width cell.length) 0
  max 2 (1 + (PhysicalCodec.pageSize - 12) / (widest + 6))

theorem interiorFanoutFor_pos (cells : List Cell) :
    0 < interiorFanoutFor cells := by
  simp only [interiorFanoutFor]
  omega

/-- Decoder evidence for the promoted cells of one arbitrary-fanout interior
page.  The child bound is also exactly the premise needed by SQLite's four-byte
page-number field. -/
inductive InteriorCellsDecode (source : CoreDecode.PageSource) (fuel : Nat) :
    List (Nat × Cell) → List (Nat × CoreDecode.IndexEntry) → Prop where
  | nil : InteriorCellsDecode source fuel [] []
  | cons {child : Nat} {cell : Cell} {entry : CoreDecode.IndexEntry}
      {cells : List (Nat × Cell)}
      {entries : List (Nat × CoreDecode.IndexEntry)}
      (head : ∀ suffix,
        CoreDecode.decodeIndexCellWithSuffixFrom source fuel (cell ++ suffix) =
          some (entry, suffix))
      (tail : InteriorCellsDecode source fuel cells entries) :
      InteriorCellsDecode source fuel ((child, cell) :: cells)
        ((child, entry) :: entries)

theorem decodePackedInterior_of_mapped
    {source : CoreDecode.PageSource} {fuel : Nat}
    {cells : List (Nat × Cell)} {entries : List (Nat × CoreDecode.IndexEntry)}
    (decoded : InteriorCellsDecode source fuel cells entries) :
    ∀ {physical : List Cell},
      cells.mapM (fun child => do
        let page ← RecursivePageBTree.boundedU32? child.1
        some (PhysicalTableBTree.encodeU32Nat page.val ++ child.2)) =
          some physical →
      ∀ suffix,
        CoreDecode.decodePackedIndexInteriorCellsFrom source fuel cells.length
            (physical.flatten ++ suffix) = some (entries, suffix) := by
  induction decoded with
  | nil =>
      intro physical mapped suffix
      simp only [List.mapM_nil, pure, Pure.pure, Option.some.injEq] at mapped
      subst physical
      rfl
  | @cons child cell entry cells entries head tail induction =>
      intro physical mapped suffix
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind] at mapped
      cases pageResult : RecursivePageBTree.boundedU32? child with
      | none => simp [pageResult] at mapped
      | some page =>
          simp only [pageResult] at mapped
          rcases Option.bind_eq_some.mp mapped with
            ⟨tailCells, tailResult, equal⟩
          have physicalEq : physical =
              (PhysicalTableBTree.encodeU32Nat page.val ++ cell) ::
                tailCells := by
            simpa using equal.symm
          subst physical
          simp only [List.flatten_cons, List.length_cons,
            List.append_assoc]
          unfold CoreDecode.decodePackedIndexInteriorCellsFrom
          unfold PhysicalTableBTree.encodeU32Nat
          rw [FileFormat.decodeUnsignedFixed_encode _ page.isLt]
          simp only [Option.bind_eq_bind, Option.bind]
          have pageValue := CoreDecode.boundedU32?_value pageResult
          rw [head (tailCells.flatten ++ suffix)]
          simp only [Option.bind]
          rw [induction tailResult suffix]
          simp [pageValue]

theorem decodeIndexInteriorFrom_widePage
    (source : CoreDecode.PageSource) {right : Nat}
    {cells : List (Nat × Cell)}
    {entries : List (Nat × CoreDecode.IndexEntry)} {page : CoreFile.Page}
    (decoded : InteriorCellsDecode source (source.pageCount + 1) cells entries)
    (built : RecursivePageBTree.indexInteriorPage? cells right = some page) :
    CoreDecode.decodeIndexInteriorFrom source page.bytes =
      some (entries, right) := by
  unfold RecursivePageBTree.indexInteriorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      rcases Option.bind_eq_some.mp built with
        ⟨physical, cellsResult, built⟩
      split at built
      next fits =>
        injection built with pageEqual
        subst page
        have content := CoreDecode.canonicalIndexInteriorContent_interiorPageBody
          rightmost physical fits
        have pointers :=
          CoreDecode.canonicalIndexInteriorPointers_interiorPageBody
            rightmost physical fits
        have physicalLength : physical.length = cells.length :=
          CoreDecode.mapM_length_of_eq_some _ cells physical cellsResult
        have packed :
            CoreDecode.decodePackedIndexInteriorCellsFrom source
                (source.pageCount + 1) cells.length
                (PhysicalCodec.cellBytes physical) = some (entries, []) := by
          simpa [PhysicalCodec.cellBytes] using
            decodePackedInterior_of_mapped decoded cellsResult []
        unfold CoreDecode.decodeIndexInteriorFrom
        rw [pointers, content]
        simp [CoreDecode.boundedU32?_value rightResult,
          physicalLength, packed,
          CoreFile.replaceFirst, PhysicalTableBTree.interiorPageBody,
          PhysicalTableBTree.interiorHeader]
      next => contradiction

def interleave : List (List Cell) → List Cell → List Cell
  | [], _ => []
  | child :: children, [] => child ++ children.flatten
  | child :: children, separator :: separators =>
      child ++ separator :: interleave children separators

inductive Node where
  | leaf (pageId : Nat) (cells : Leaf)
  | branch (pageId : Nat) (initial : List (Node × Cell)) (rightmost : Node)

def Node.rootId : Node → Nat
  | .leaf pageId _ | .branch pageId _ _ => pageId

mutual
  def Node.toCells : Node → List Cell
    | .leaf _ cells => cells
    | .branch _ initial rightmost =>
        pairsToCells initial ++ rightmost.toCells

  def pairsToCells : List (Node × Cell) → List Cell
    | [] => []
    | (child, separator) :: pairs =>
        child.toCells ++ separator :: pairsToCells pairs
end

mutual
  def Node.pageIds : Node → List Nat
    | .leaf pageId _ => [pageId]
    | .branch pageId initial rightmost =>
        pageId :: pairsPageIds initial ++ rightmost.pageIds

  def pairsPageIds : List (Node × Cell) → List Nat
    | [] => []
    | (child, _) :: pairs => child.pageIds ++ pairsPageIds pairs
end

theorem pairsPageIds_eq_flatMap (pairs : List (Node × Cell)) :
    pairsPageIds pairs = pairs.flatMap fun pair => pair.1.pageIds := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rcases pair with ⟨node, cell⟩
      simp only [pairsPageIds, List.flatMap_cons]
      rw [induction]

def groupEntries (groups : List (List CoreDecode.IndexEntry ×
    CoreDecode.IndexEntry)) : List CoreDecode.IndexEntry :=
  groups.flatMap fun group => group.1 ++ [group.2]

theorem flatten_map_eq_flatMap {alpha beta : Type}
    (values : List alpha) (f : alpha → List beta) :
    (values.map f).flatten = values.flatMap f := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons]
      rw [induction]

mutual
  inductive NodeDecodes (source : CoreDecode.PageSource) (fuel : Nat) :
      Node → List CoreDecode.IndexEntry → Prop where
    | leaf {pageId cells entries}
        (decoded : CoreDecode.IndexCellsDecode source fuel cells entries) :
        NodeDecodes source fuel (.leaf pageId cells) entries
    | branch {pageId initial rightmost groups rightEntries}
        (initialDecoded : PairsDecode source fuel initial groups)
        (rightDecoded : NodeDecodes source fuel rightmost rightEntries) :
        NodeDecodes source fuel (.branch pageId initial rightmost)
          (groupEntries groups ++ rightEntries)

  inductive PairsDecode (source : CoreDecode.PageSource) (fuel : Nat) :
      List (Node × Cell) →
        List (List CoreDecode.IndexEntry × CoreDecode.IndexEntry) → Prop where
    | nil : PairsDecode source fuel [] []
    | cons {child cell pairs childEntries entry groups}
        (childDecoded : NodeDecodes source fuel child childEntries)
        (separatorDecoded : ∀ suffix,
          CoreDecode.decodeIndexCellWithSuffixFrom source fuel
              (cell ++ suffix) = some (entry, suffix))
        (tailDecoded : PairsDecode source fuel pairs groups) :
        PairsDecode source fuel ((child, cell) :: pairs)
          ((childEntries, entry) :: groups)
end

theorem pairsPageIds_member_le : ∀ (pairs : List (Node × Cell))
    (child : Node) (cell : Cell), (child, cell) ∈ pairs →
      child.pageIds.length ≤ (pairsPageIds pairs).length
  | [], _, _, member => by simp at member
  | (head, separator) :: pairs, child, cell, member => by
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · injection equal with nodeEqual
        subst child
        simp [pairsPageIds]
      · have bound := pairsPageIds_member_le pairs child cell member
        simp only [pairsPageIds, List.length_append]
        omega

theorem PairsDecode.ofCells
    {source : CoreDecode.PageSource} {fuel : Nat}
    (nodeExact : ∀ (node : Node) (cell : Cell),
      (node, cell) ∈ pairs → ∀ (entries : List CoreDecode.IndexEntry),
      CoreDecode.IndexCellsDecode source fuel node.toCells entries →
        Nonempty (NodeDecodes source fuel node entries)) :
    ∀ (entries : List CoreDecode.IndexEntry),
      CoreDecode.IndexCellsDecode source fuel (pairsToCells pairs) entries →
      ∃ groups, entries = groupEntries groups ∧
        PairsDecode source fuel pairs groups
  := by
  induction pairs with
  | nil =>
      intro entries decoded
      cases decoded
      exact ⟨[], rfl, .nil⟩
  | cons pair pairs induction =>
      rcases pair with ⟨child, cell⟩
      intro entries decoded
      have split := decoded.splitAt child.toCells.length
      rcases split with
        ⟨childEntries, suffixEntries, entriesEq, childDecoded, suffixDecoded⟩
      have childCells :
          (pairsToCells ((child, cell) :: pairs)).take child.toCells.length =
            child.toCells := by
        simp [pairsToCells]
      rw [childCells] at childDecoded
      have suffixCells : (cell :: pairsToCells pairs) =
          (pairsToCells ((child, cell) :: pairs)).drop child.toCells.length := by
        simp [pairsToCells]
      rw [← suffixCells] at suffixDecoded
      cases suffixDecoded with
      | @cons _ entry _ tailEntries separatorDecoded tailDecoded =>
          rcases nodeExact child cell (by simp) childEntries childDecoded with
            ⟨childExact⟩
          have tailExact : ∀ (node : Node) (separator : Cell),
              (node, separator) ∈ pairs →
              ∀ (candidateEntries : List CoreDecode.IndexEntry),
                CoreDecode.IndexCellsDecode source fuel node.toCells
                    candidateEntries →
                  Nonempty (NodeDecodes source fuel node candidateEntries) := by
            intro node separator member
            exact nodeExact node separator (by simp [member])
          rcases induction tailExact tailEntries tailDecoded with
            ⟨groups, tailEq, groupsDecoded⟩
          subst entries
          simp only [groupEntries, List.flatMap_cons]
          refine ⟨(childEntries, entry) :: groups, ?_,
            .cons childExact separatorDecoded groupsDecoded⟩
          simp [groupEntries, tailEq, List.append_assoc]

theorem nodeDecodesOfCellsBudget {source : CoreDecode.PageSource}
    {fuel : Nat} : ∀ (budget : Nat) (node : Node)
      (entries : List CoreDecode.IndexEntry),
      node.pageIds.length < budget →
      CoreDecode.IndexCellsDecode source fuel node.toCells entries →
      NodeDecodes source fuel node entries
  | 0, _, _, bound, _ => by omega
  | _ + 1, .leaf pageId cells, entries, _, decoded => by
      exact .leaf decoded
  | budget + 1, .branch pageId initial rightmost, entries, bound, decoded => by
      have split := decoded.splitAt (pairsToCells initial).length
      rcases split with
        ⟨initialEntries, rightEntries, entriesEq, initialDecoded,
          rightDecoded⟩
      have initialCells :
          ((pairsToCells initial ++ rightmost.toCells).take
            (pairsToCells initial).length) = pairsToCells initial := by
        simp
      have rightCells :
          ((pairsToCells initial ++ rightmost.toCells).drop
            (pairsToCells initial).length) = rightmost.toCells := by
        simp
      have initialDecoded' : CoreDecode.IndexCellsDecode source fuel
          (pairsToCells initial) initialEntries := by
        simpa only [Node.toCells, initialCells] using initialDecoded
      have rightDecoded' : CoreDecode.IndexCellsDecode source fuel
          rightmost.toCells rightEntries := by
        simpa only [Node.toCells, rightCells] using rightDecoded
      have pairExact : ∀ (child : Node) (cell : Cell),
          (child, cell) ∈ initial →
          ∀ (childEntries : List CoreDecode.IndexEntry),
            CoreDecode.IndexCellsDecode source fuel child.toCells
                childEntries →
              Nonempty (NodeDecodes source fuel child childEntries) := by
        intro child cell member childEntries childDecoded
        have pairBound := pairsPageIds_member_le initial child cell member
        have childBound : child.pageIds.length < budget := by
          simp only [Node.pageIds, List.length_cons, List.length_append] at bound
          omega
        exact ⟨nodeDecodesOfCellsBudget budget child childEntries
          childBound childDecoded⟩
      rcases PairsDecode.ofCells pairExact initialEntries initialDecoded' with
        ⟨groups, initialEq, groupsDecoded⟩
      have rightBound : rightmost.pageIds.length < budget := by
        simp only [Node.pageIds, List.length_cons, List.length_append] at bound
        omega
      have rightExact := nodeDecodesOfCellsBudget budget rightmost rightEntries
        rightBound rightDecoded'
      subst entries
      rw [initialEq]
      exact .branch groupsDecoded rightExact

theorem NodeDecodes.ofCells {source : CoreDecode.PageSource} {fuel : Nat}
    {node : Node} {entries : List CoreDecode.IndexEntry}
    (decoded : CoreDecode.IndexCellsDecode source fuel node.toCells entries) :
    NodeDecodes source fuel node entries := by
  exact nodeDecodesOfCellsBudget (node.pageIds.length + 1) node entries
    (by omega) decoded

def interiorEntries (initial : List (Node × Cell))
    (groups : List (List CoreDecode.IndexEntry × CoreDecode.IndexEntry)) :
    List (Nat × CoreDecode.IndexEntry) :=
  (initial.zip groups).map fun paired =>
    (paired.1.1.rootId, paired.2.2)

theorem PairsDecode.interior {source : CoreDecode.PageSource} {fuel : Nat}
    {initial : List (Node × Cell)}
    {groups : List (List CoreDecode.IndexEntry × CoreDecode.IndexEntry)}
    (decoded : PairsDecode source fuel initial groups) :
    InteriorCellsDecode source fuel
      (initial.map fun pair => (pair.1.rootId, pair.2))
      (interiorEntries initial groups) :=
  match decoded with
  | .nil => .nil
  | .cons _ separatorDecoded tailDecoded =>
      .cons separatorDecoded (PairsDecode.interior tailDecoded)

theorem PairsDecode.mapM_exact {source : CoreDecode.PageSource} {fuel : Nat}
    {decodeFuel : Nat}
    {initial : List (Node × Cell)}
    {groups : List (List CoreDecode.IndexEntry × CoreDecode.IndexEntry)}
    (decoded : PairsDecode source fuel initial groups)
    (nodeExact : ∀ {node : Node} {cell : Cell},
      (node, cell) ∈ initial → ∀ {entries : List CoreDecode.IndexEntry},
      NodeDecodes source fuel node entries →
      CoreDecode.decodeIndexSubtreeFrom source decodeFuel node.rootId =
        some entries) :
    (interiorEntries initial groups).mapM (fun entry => do
      let left ← CoreDecode.decodeIndexSubtreeFrom source decodeFuel entry.1
      some (left ++ [entry.2])) =
        some (groups.map fun group => group.1 ++ [group.2]) :=
  match decoded with
  | .nil => rfl
  | @PairsDecode.cons _ _ child cell pairs childEntries entry groups
      childDecoded _ tailDecoded => by
      simp only [interiorEntries, List.zip_cons_cons, List.map_cons,
        List.mapM_cons]
      rw [nodeExact (cell := cell) (by simp) childDecoded]
      have tailNodeExact : ∀ {node : Node} {separator : Cell},
          (node, separator) ∈ pairs →
          ∀ {entries : List CoreDecode.IndexEntry},
            NodeDecodes source fuel node entries →
            CoreDecode.decodeIndexSubtreeFrom source decodeFuel node.rootId =
              some entries := by
        intro node separator member entries childDecoded
        exact nodeExact (cell := separator) (by
          simp only [List.mem_cons]
          exact Or.inr member)
          childDecoded
      have tailExact := PairsDecode.mapM_exact tailDecoded tailNodeExact
      unfold interiorEntries at tailExact
      rw [tailExact]
      rfl

def popLastCell? (cells : List Cell) : Option (List Cell × Cell) :=
  match cells.reverse with
  | [] => none
  | cell :: reversed => some (reversed.reverse, cell)

theorem popLastCell?_reconstruct {cells initial : List Cell} {last : Cell}
    (success : popLastCell? cells = some (initial, last)) :
    initial ++ [last] = cells := by
  unfold popLastCell? at success
  cases reversed : cells.reverse with
  | nil => simp [reversed] at success
  | cons final tail =>
      simp only [reversed, Option.some.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      have restored := congrArg List.reverse reversed
      simpa using restored.symm

/-- Remove the in-order greatest cell.  Fuel is the remaining physical height;
generated trees always provide `height + 1`. -/
def Node.popMaxStep : Nat → Node → Option (Node × Cell)
  | 0, _ => none
  | _ + 1, .leaf pageId cells => do
      let (initial, greatest) ← popLastCell? cells
      some (.leaf pageId initial, greatest)
  | fuel + 1, .branch pageId initial rightmost => do
      let (updated, greatest) ← popMaxStep fuel rightmost
      some (.branch pageId initial updated, greatest)

theorem Node.popMaxStep_toCells {fuel : Nat} {node updated : Node}
    {greatest : Cell}
    (success : node.popMaxStep fuel = some (updated, greatest)) :
    updated.toCells ++ [greatest] = node.toCells := by
  induction fuel generalizing node updated with
  | zero => simp [Node.popMaxStep] at success
  | succ fuel induction =>
      cases node with
      | leaf pageId cells =>
          simp only [Node.popMaxStep, Option.bind_eq_bind, Option.bind] at success
          cases popped : popLastCell? cells with
          | none => simp [popped] at success
          | some pair =>
              rcases pair with ⟨initial, last⟩
              simp only [popped, Option.some.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              simpa [Node.toCells] using popLastCell?_reconstruct popped
      | branch pageId initial rightmost =>
          simp only [Node.popMaxStep, Option.bind_eq_bind, Option.bind] at success
          cases recursive : rightmost.popMaxStep fuel with
          | none => simp [recursive] at success
          | some pair =>
              rcases pair with ⟨replacement, last⟩
              simp only [recursive, Option.some.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              simp only [Node.toCells]
              rw [List.append_assoc, induction recursive]

/-- Promote one greatest cell between every adjacent pair of children. -/
def promoteChildren : Nat → List Node →
    Option (List (Node × Cell) × Node)
  | _, [] => none
  | _, [last] => some ([], last)
  | fuel, child :: next :: children => do
      let (updated, separator) ← child.popMaxStep fuel
      let (remaining, rightmost) ← promoteChildren fuel (next :: children)
      some ((updated, separator) :: remaining, rightmost)

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
      rcases Option.bind_eq_some.mp success with
        ⟨headPages, headResult, success⟩
      rcases Option.bind_eq_some.mp success with
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
          rcases Option.bind_eq_some.mp success with
            ⟨page, _, equal⟩
          simp only [Option.some.injEq] at equal
          subst pages
          rfl
      | branch pageId initial rightmost =>
          simp only [Node.encodePagesStep, Option.bind_eq_bind, Option.bind]
            at success
          rcases Option.bind_eq_some.mp success with
            ⟨page, _, success⟩
          rcases Option.bind_eq_some.mp success with
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
      rcases Option.bind_eq_some.mp encoded with
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
      rcases Option.bind_eq_some.mp encoded with
        ⟨root, rootResult, encoded⟩
      rcases Option.bind_eq_some.mp encoded with
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

def indexRowsInline (table : Core.Table) (index : Core.Index) : Bool :=
  (CoreFile.sortedIndexRows table index).all fun row =>
    match CoreFile.indexRecord? index row with
    | none => false
    | some record => decide
        (record.encode.length ≤ CoreOverflow.maxLocal .index)

theorem indexRowsInline_spec {table : Core.Table} {index : Core.Index}
    (success : indexRowsInline table index = true) :
    ∀ row ∈ CoreFile.sortedIndexRows table index, ∀ record,
      CoreFile.indexRecord? index row = some record →
        record.encode.length ≤ CoreOverflow.maxLocal .index := by
  intro row member record encoded
  have rowTrue := (List.all_eq_true.mp success) row member
  simp only [indexRowsInline] at success
  rw [encoded] at rowTrue
  exact of_decide_eq_true rowTrue

theorem decodeIndexCellWithSuffixFrom_inline
    {index : Core.Index} {row : Core.Row} {cell : Cell}
    (source : CoreDecode.PageSource) (fuel : Nat)
    (inline : ∀ record, CoreFile.indexRecord? index row = some record →
      record.encode.length ≤ CoreOverflow.maxLocal .index)
    (built : CoreFile.indexCell? index row = some cell) (suffix : List UInt8) :
    CoreDecode.decodeIndexCellWithSuffixFrom source fuel (cell ++ suffix) =
      some (⟨row.value index.column, row.rowid⟩, suffix) := by
  unfold CoreFile.indexCell? at built
  cases recordResult : CoreFile.indexRecord? index row with
  | none => simp [recordResult] at built
  | some record =>
      simp only [recordResult, Option.bind_eq_bind, Option.bind] at built
      split at built
      next payloadBound =>
        injection built with cellEqual
        subst cell
        let plan : CoreOverflow.CellPlan := {
          kind := .index
          cellPrefix := FileFormat.encodeVarint
            ⟨record.encode.length, by simpa using payloadBound⟩
          payload := record.encode }
        have planned : CoreOverflow.indexCellPlan? index row = some plan := by
          unfold CoreOverflow.indexCellPlan?
          rw [recordResult]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [dif_pos payloadBound]
        have cellBuilt : plan.cellBytes? none = some
            (FileFormat.encodeVarint
                ⟨record.encode.length, by simpa using payloadBound⟩ ++
              record.encode) := by
          unfold CoreOverflow.CellPlan.cellBytes?
          rw [dif_pos (inline record recordResult)]
        exact CoreDecode.decodeIndexCellWithSuffixFrom_indexPlan_inline
          recordResult planned (inline record recordResult) source fuel none
          cellBuilt suffix
      next => contradiction

theorem indexCellsDecode_rows (source : CoreDecode.PageSource)
    (fuel : Nat) (index : Core.Index) : ∀ (rows : List Core.Row)
    {cells : List Cell},
    (∀ row ∈ rows, ∀ record,
      CoreFile.indexRecord? index row = some record →
        record.encode.length ≤ CoreOverflow.maxLocal .index) →
    rows.mapM (CoreFile.indexCell? index) = some cells →
    CoreDecode.IndexCellsDecode source fuel cells
      (rows.map fun row => ⟨row.value index.column, row.rowid⟩)
  | [], cells, _, encoded => by
      simp only [List.mapM_nil, pure, Pure.pure, Option.some.injEq] at encoded
      subst cells
      exact .nil
  | row :: rows, cells, inline, encoded => by
      simp only [List.mapM_cons] at encoded
      rcases Option.bind_eq_some.mp encoded with
        ⟨cell, headResult, encoded⟩
      rcases Option.bind_eq_some.mp encoded with
        ⟨tail, tailResult, equal⟩
      simp only [pure, Pure.pure, Option.some.injEq] at equal
      subst cells
      apply CoreDecode.IndexCellsDecode.cons
      · apply decodeIndexCellWithSuffixFrom_inline source fuel
          (inline := ?_) headResult
        intro record recordResult
        exact inline row (by simp) record recordResult
      · exact indexCellsDecode_rows source fuel index rows
          (fun candidate member => inline candidate (by simp [member])) tailResult

theorem indexCellsDecode_indexCells (source : CoreDecode.PageSource)
    (fuel : Nat) (table : Core.Table) (index : Core.Index)
    (inline : indexRowsInline table index = true) {cells : List Cell}
    (encoded : CoreFile.indexCells table index = some cells) :
    CoreDecode.IndexCellsDecode source fuel cells
      (CoreDecode.expectedIndexEntries table index) := by
  unfold CoreFile.indexCells at encoded
  unfold CoreDecode.expectedIndexEntries
  exact indexCellsDecode_rows source fuel index
    (CoreFile.sortedIndexRows table index)
    (fun row member record recordResult =>
      indexRowsInline_spec inline row member record recordResult) encoded

structure IndexEncoding where
  table : Core.Table
  index : Core.Index
  startPage : Nat
  rootPage : Nat
  nextPage : Nat
  store : Store
  numberedPages : List CorePageCodec.NumberedPage
  startExact : startPage = store.startPage
  nextExact : nextPage = store.nextPage
  rootExact : rootPage = store.root.rootId
  cellsEncoded : CoreFile.indexCells table index = some store.cells
  inline : indexRowsInline table index = true
  pagesEncoded : store.root.encodePages = some numberedPages
  numbers : (CorePageCodec.orderNumberedPages numberedPages).map
    CorePageCodec.NumberedPage.pageNumber =
      List.range' startPage (store.nextPage - startPage)

def IndexEncoding.pages (encoding : IndexEncoding) : List CoreFile.Page :=
  (CorePageCodec.orderNumberedPages encoding.numberedPages).map
    CorePageCodec.NumberedPage.page

def IndexEncoding.catalogEntry (encoding : IndexEncoding) :
    CoreFile.CatalogEntry := {
  kind := "index"
  name := encoding.index.name
  table := encoding.table.schema.name
  rootPage := encoding.rootPage
  sql := CoreFile.indexSQL encoding.table encoding.index
  sqlIsNull := encoding.index.isImplicitPrimary encoding.table.schema }

def encodeIndex (startPage : Nat) (table : Core.Table) (index : Core.Index) :
    Option IndexEncoding := do
  if inline : indexRowsInline table index then
    match cellsResult : CoreFile.indexCells table index with
    | none => none
    | some cells =>
      match storeResult : Store.build? startPage cells with
      | none => none
      | some store =>
        match pagesResult : store.root.encodePages with
        | none => none
        | some numberedPages =>
          if _numbers : (CorePageCodec.orderNumberedPages numberedPages).map
              CorePageCodec.NumberedPage.pageNumber =
                List.range' startPage (store.nextPage - startPage) then
            some {
              table
              index
              startPage
              rootPage := store.root.rootId
              nextPage := store.nextPage
              store
              numberedPages
              startExact := (Store.build?_startPage storeResult).symm
              nextExact := rfl
              rootExact := rfl
              cellsEncoded := by
                rw [Store.build?_cells storeResult]
                exact cellsResult
              inline
              pagesEncoded := pagesResult
              numbers := _numbers }
          else none
  else none

def encodeIndexes : Nat → List (Core.Table × Core.Index) →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, pair :: pairs => do
      let head ← encodeIndex nextPage pair.1 pair.2
      let tail ← encodeIndexes head.nextPage pairs
      some (head :: tail)

def indexPagesOf (encodings : List IndexEncoding) : List CoreFile.Page :=
  encodings.flatMap IndexEncoding.pages

def encodeIndexTableGroups : Nat → List Core.Table →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let current ← encodeIndexes nextPage
        (table.indexes.map fun index => (table, index))
      let after := nextPage + (indexPagesOf current).length
      let remaining ← encodeIndexTableGroups after tables
      some (current ++ remaining)

def indexEntriesOf (encodings : List IndexEncoding) :
    List CoreFile.CatalogEntry :=
  encodings.map IndexEncoding.catalogEntry

theorem IndexEncoding.numberedPages_length (encoding : IndexEncoding) :
    encoding.numberedPages.length =
      encoding.store.nextPage - encoding.startPage := by
  have lengths := congrArg List.length encoding.numbers
  simpa [CorePageCodec.orderNumberedPages] using lengths

theorem IndexEncoding.pages_length (encoding : IndexEncoding) :
    encoding.pages.length = encoding.numberedPages.length := by
  simp [IndexEncoding.pages, CorePageCodec.orderNumberedPages]

theorem IndexEncoding.next_eq (encoding : IndexEncoding) :
    encoding.nextPage = encoding.startPage + encoding.pages.length := by
  have startLe : encoding.startPage ≤ encoding.store.nextPage := by
    rw [encoding.startExact]
    exact encoding.store.startLeNext
  rw [encoding.nextExact, encoding.pages_length,
    encoding.numberedPages_length]
  omega

theorem encodeIndex_identity {startPage : Nat} {table : Core.Table}
    {index : Core.Index} {encoding : IndexEncoding}
    (success : encodeIndex startPage table index = some encoding) :
    encoding.startPage = startPage ∧
    encoding.table = table ∧ encoding.index = index := by
  simp only [encodeIndex] at success
  split at success <;> try contradiction
  all_goals split at success <;> try contradiction
  all_goals split at success <;> try contradiction
  all_goals split at success <;> try contradiction
  all_goals split at success <;> try contradiction
  all_goals
    injection success with equal
    subst encoding
    simp

theorem encodeIndexes_pairs : ∀ (nextPage : Nat)
    (pairs : List (Core.Table × Core.Index))
    (encodings : List IndexEncoding),
    encodeIndexes nextPage pairs = some encodings →
    encodings.map (fun encoding => (encoding.table, encoding.index)) = pairs
  | _, [], encodings, encoded => by
      simp only [encodeIndexes, Option.some.injEq] at encoded
      subst encodings
      rfl
  | nextPage, pair :: pairs, encodings, encoded => by
      simp only [encodeIndexes, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeIndex nextPage pair.1 pair.2 with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeIndexes head.nextPage pairs with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encodings
              have identity := encodeIndex_identity headResult
              simp only [List.map_cons]
              rw [identity.2.1, identity.2.2,
                encodeIndexes_pairs head.nextPage pairs tail tailResult]

theorem encodeIndexTableGroups_pairs : ∀ (nextPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups nextPage tables = some encodings →
    encodings.map (fun encoding => (encoding.table, encoding.index)) =
      tables.flatMap fun table =>
        table.indexes.map fun index => (table, index)
  | _, [], encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.some.injEq] at encoded
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind]
        at encoded
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
          simp only [currentResult] at encoded
          cases remainingResult : encodeIndexTableGroups
              (nextPage + (indexPagesOf current).length) tables with
          | none => simp [remainingResult] at encoded
          | some remaining =>
              simp only [remainingResult, Option.some.injEq] at encoded
              subst encodings
              simp only [List.map_append, List.flatMap_cons]
              rw [encodeIndexes_pairs nextPage _ current currentResult,
                encodeIndexTableGroups_pairs
                  (nextPage + (indexPagesOf current).length) tables remaining
                  remainingResult]

theorem encodeIndexTableGroups_tables {nextPage : Nat}
    {tables : List Core.Table} {encodings : List IndexEncoding}
    (encoded : encodeIndexTableGroups nextPage tables = some encodings) :
    ∀ encoding ∈ encodings, encoding.table ∈ tables := by
  have pairs := encodeIndexTableGroups_pairs nextPage tables encodings encoded
  intro encoding member
  have pairMember : (encoding.table, encoding.index) ∈
      encodings.map (fun candidate => (candidate.table, candidate.index)) :=
    List.mem_map_of_mem member
  rw [pairs] at pairMember
  simp only [List.mem_flatMap, List.mem_map] at pairMember
  rcases pairMember with ⟨table, tableMember, index, _, equal⟩
  injection equal with tableEqual
  simpa [tableEqual] using tableMember

def numberedPagesOf (encodings : List IndexEncoding) :
    List CorePageCodec.NumberedPage :=
  encodings.flatMap fun encoding =>
    CorePageCodec.orderNumberedPages encoding.numberedPages

theorem numberedPages_length_le_of_mem {encoding : IndexEncoding} :
    ∀ {encodings : List IndexEncoding}, encoding ∈ encodings →
      encoding.numberedPages.length ≤ (numberedPagesOf encodings).length
  | [], member => by simp at member
  | head :: tail, member => by
      simp only [List.mem_cons] at member
      unfold numberedPagesOf
      simp only [List.flatMap_cons, List.length_append]
      rcases member with rfl | member
      · have orderedLength :
            (CorePageCodec.orderNumberedPages encoding.numberedPages).length =
              encoding.numberedPages.length := by
          simp [CorePageCodec.orderNumberedPages]
        omega
      · have tailBound := numberedPages_length_le_of_mem member
        unfold numberedPagesOf at tailBound
        omega

theorem indexPagesOf_eq_map (encodings : List IndexEncoding) :
    indexPagesOf encodings =
      (numberedPagesOf encodings).map CorePageCodec.NumberedPage.page := by
  unfold indexPagesOf numberedPagesOf IndexEncoding.pages
  rw [List.map_flatMap]

theorem encodeIndexes_numbers : ∀ (startPage : Nat)
    (pairs : List (Core.Table × Core.Index))
    (encodings : List IndexEncoding),
    encodeIndexes startPage pairs = some encodings →
    (numberedPagesOf encodings).map
        CorePageCodec.NumberedPage.pageNumber =
      List.range' startPage (indexPagesOf encodings).length
  | _, [], encodings, encoded => by
      simp only [encodeIndexes, Option.some.injEq] at encoded
      subst encodings
      rfl
  | startPage, pair :: pairs, encodings, encoded => by
      simp only [encodeIndexes, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeIndex startPage pair.1 pair.2 with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeIndexes head.nextPage pairs with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encodings
              have identity := encodeIndex_identity headResult
              have headNumbers :
                  (CorePageCodec.orderNumberedPages head.numberedPages).map
                      CorePageCodec.NumberedPage.pageNumber =
                    List.range' startPage head.pages.length := by
                rw [head.numbers]
                congr 2
                · exact identity.1
                · rw [head.pages_length, head.numberedPages_length]
              have tailNumbers := encodeIndexes_numbers head.nextPage pairs
                tail tailResult
              unfold numberedPagesOf indexPagesOf at tailNumbers ⊢
              simp only [List.flatMap_cons, List.map_append,
                List.length_append]
              rw [headNumbers, tailNumbers, head.next_eq, identity.1]
              exact List.range'_append_1

theorem encodeIndexTableGroups_numbers : ∀ (startPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups startPage tables = some encodings →
    (numberedPagesOf encodings).map
        CorePageCodec.NumberedPage.pageNumber =
      List.range' startPage (indexPagesOf encodings).length
  | _, [], encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.some.injEq] at encoded
      subst encodings
      rfl
  | startPage, table :: tables, encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind]
        at encoded
      cases currentResult : encodeIndexes startPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
          simp only [currentResult] at encoded
          cases remainingResult : encodeIndexTableGroups
              (startPage + (indexPagesOf current).length) tables with
          | none => simp [remainingResult] at encoded
          | some remaining =>
              simp only [remainingResult, Option.some.injEq] at encoded
              subst encodings
              have currentNumbers := encodeIndexes_numbers startPage _ current
                currentResult
              have remainingNumbers := encodeIndexTableGroups_numbers
                (startPage + (indexPagesOf current).length) tables remaining
                  remainingResult
              unfold numberedPagesOf indexPagesOf at currentNumbers remainingNumbers ⊢
              simp only [List.flatMap_append, List.map_append,
                List.length_append]
              rw [currentNumbers, remainingNumbers]
              exact List.range'_append_1

theorem IndexEncoding.decode_exact (source : CoreDecode.PageSource)
    (encoding : IndexEncoding)
    (contains : CorePageCodec.PageSourceContains source
      encoding.numberedPages)
    (pagesBound : encoding.numberedPages.length < source.pageCount + 1) :
    CoreDecode.decodeIndexSubtreeFrom source (source.pageCount + 1)
        encoding.rootPage =
      some (CoreDecode.expectedIndexEntries encoding.table encoding.index) := by
  have cellsDecoded := indexCellsDecode_indexCells source
    (source.pageCount + 1) encoding.table encoding.index encoding.inline
      encoding.cellsEncoded
  have rootCellsDecoded : CoreDecode.IndexCellsDecode source
      (source.pageCount + 1) encoding.store.root.toCells
      (CoreDecode.expectedIndexEntries encoding.table encoding.index) := by
    rw [encoding.store.represents]
    exact cellsDecoded
  have rootDecoded := NodeDecodes.ofCells rootCellsDecoded
  have encodedLength := Node.encodePages_length encoding.pagesEncoded
  have fuelBound : encoding.store.root.pageIds.length <
      source.pageCount + 1 := by omega
  have exact := decodeIndexSubtreeFrom_encodePages source
    encoding.pagesEncoded contains rootDecoded fuelBound
  rw [encoding.rootExact]
  exact exact

theorem decodeCanonicalIndexesForTable_encodeIndexes
    (table : Core.Table) : ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List IndexEncoding)
      (suffix : List CoreDecode.CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      encodeIndexes nextPage
          (indexes.map fun index => (table, index)) = some encodings →
      CoreDecode.decodeCanonicalIndexesForTable table.schema table.schema.name
        (encodings.map (fun encoding =>
          CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (indexes, suffix)
  | _, [], encodings, suffix, _, boundary, encoded => by
      simp only [List.map_nil, encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold CoreDecode.decodeCanonicalIndexesForTable
          exact dif_neg (boundary entry (by simp))
  | nextPage, index :: indexes, encodings, suffix, members, boundary,
      encoded => by
      simp only [List.map_cons, encodeIndexes, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeIndex nextPage table index with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeIndexes head.nextPage
              (indexes.map fun candidate => (table, candidate)) with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encodings
              simp only [List.map_cons, List.cons_append]
              unfold CoreDecode.decodeCanonicalIndexesForTable
              have identity := encodeIndex_identity headResult
              have sameTable :
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry).table =
                    table.schema.name := by
                simp [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded, identity.2.1]
              rw [dif_pos sameTable]
              have decoded : CoreDecode.decodeCanonicalIndex table.schema
                  table.schema.name
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry) =
                    some index := by
                simpa [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded, identity.2.1,
                  identity.2.2] using
                    (CoreDecode.decodeCanonicalIndex_encoded table index
                      (members index (by simp)) head.rootPage)
              rw [decoded]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [decodeCanonicalIndexesForTable_encodeIndexes table
                head.nextPage indexes tail suffix
                (fun candidate member => members candidate (by simp [member]))
                boundary tailResult]

theorem restoreCanonicalIndexes_encodeIndexTableGroups :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List IndexEncoding)
      (suffix : List CoreDecode.CatalogEntry),
      Core.TablesWellFormed tables →
      (∀ entry ∈ suffix, ∀ table ∈ tables,
        entry.table ≠ table.schema.name) →
      encodeIndexTableGroups nextPage tables = some encodings →
      CoreDecode.restoreCanonicalIndexes
          (tables.map Core.Table.withoutIndexes)
          (encodings.map (fun encoding =>
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
        some (tables.map Core.Table.canonicalize, suffix)
  | _, [], encodings, suffix, _, _, encoded => by
      simp only [encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, suffix, wellFormed, boundary,
      encoded => by
      simp only [Core.TablesWellFormed, Core.namesUnique, List.map_cons,
        List.pairwise_cons] at wellFormed
      rcases wellFormed with ⟨headDistinct, tailWellFormed⟩
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind]
        at encoded
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
          simp only [currentResult] at encoded
          cases remainingResult : encodeIndexTableGroups
              (nextPage + (indexPagesOf current).length) tables with
          | none => simp [remainingResult] at encoded
          | some remaining =>
              simp only [remainingResult, Option.some.injEq] at encoded
              subst encodings
              simp only [List.map_cons, List.map_append, List.append_assoc]
              unfold CoreDecode.restoreCanonicalIndexes
              have remainingBelongs := encodeIndexTableGroups_tables
                remainingResult
              have currentBoundary : ∀ entry ∈
                  (remaining.map (fun encoding =>
                    CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++
                      suffix),
                  entry.table ≠ table.schema.name := by
                intro entry member
                simp only [List.mem_append] at member
                rcases member with encodedMember | suffixMember
                · rcases List.mem_map.mp encodedMember with
                    ⟨encoding, encodingMember, equal⟩
                  subst entry
                  have tableMember := remainingBelongs encoding encodingMember
                  have distinct := headDistinct encoding.table.schema.name
                    (List.mem_map_of_mem tableMember)
                  simpa [IndexEncoding.catalogEntry,
                    CoreDecode.CatalogEntry.ofEncoded] using distinct.symm
                · exact boundary entry suffixMember table (by simp)
              simp only [Core.Table.withoutIndexes_schema,
                Core.Table.withoutIndexes_rows]
              rw [decodeCanonicalIndexesForTable_encodeIndexes table nextPage
                table.indexes current
                (remaining.map (fun encoding =>
                  CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++
                    suffix)
                (by simp) currentBoundary currentResult]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [Core.Table.rebuild_self]
              simp only [Except.toOption]
              have tailBoundary : ∀ entry ∈ suffix,
                  ∀ candidate ∈ tables,
                    entry.table ≠ candidate.schema.name := by
                intro entry entryMember candidate candidateMember
                exact boundary entry entryMember candidate
                  (by simp [candidateMember])
              rw [restoreCanonicalIndexes_encodeIndexTableGroups
                (nextPage + (indexPagesOf current).length) tables remaining
                suffix tailWellFormed tailBoundary remainingResult]

theorem rebuildCanonicalDatabase_encoded (database : Core.Database)
    (nextPage : Nat) (encodings : List IndexEncoding)
    (encoded : encodeIndexTableGroups nextPage database.tables =
      some encodings) :
    CoreDecode.rebuildCanonicalDatabase
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry)) =
          some database.canonicalize := by
  unfold CoreDecode.rebuildCanonicalDatabase
  have restored := restoreCanonicalIndexes_encodeIndexTableGroups nextPage
    database.tables encodings [] database.tablesWellFormed (by simp) encoded
  simp only [List.append_nil] at restored
  rw [restored]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]
  have rebuilt := Core.Database.rebuild_self database.canonicalize
  change Core.Database.rebuild
      (database.tables.map Core.Table.canonicalize) =
        .ok database.canonicalize at rebuilt
  rw [rebuilt]
  rfl

theorem validateCanonicalIndexesForTableFrom_encodeIndexes
    (source : CoreDecode.PageSource) (table : Core.Table) :
    ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List IndexEncoding)
      (suffix : List CoreDecode.CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      encodeIndexes nextPage
          (indexes.map fun index => (table, index)) = some encodings →
      (∀ encoding ∈ encodings,
        CorePageCodec.PageSourceContains source encoding.numberedPages) →
      (∀ encoding ∈ encodings,
        encoding.numberedPages.length < source.pageCount + 1) →
      CoreDecode.validateCanonicalIndexesForTableFrom source
        table.withoutIndexes
        (encodings.map (fun encoding =>
          CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some suffix
  | _, [], encodings, suffix, _, boundary, encoded, _, _ => by
      simp only [List.map_nil, encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold CoreDecode.validateCanonicalIndexesForTableFrom
          rw [dif_neg (by simpa using boundary entry (by simp))]
  | nextPage, index :: indexes, encodings, suffix, members, boundary,
      encoded, contains, pagesBound => by
      simp only [List.map_cons, encodeIndexes, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeIndex nextPage table index with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeIndexes head.nextPage
              (indexes.map fun candidate => (table, candidate)) with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encodings
              simp only [List.map_cons, List.cons_append]
              unfold CoreDecode.validateCanonicalIndexesForTableFrom
              have identity := encodeIndex_identity headResult
              have sameTable :
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry).table =
                    table.withoutIndexes.schema.name := by
                simp [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded, identity.2.1]
              rw [dif_pos sameTable]
              have metadata : CoreDecode.decodeCanonicalIndex
                  table.withoutIndexes.schema table.withoutIndexes.schema.name
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry) =
                    some index := by
                simp only [Core.Table.withoutIndexes_schema]
                simpa [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded, identity.2.1,
                  identity.2.2] using
                    (CoreDecode.decodeCanonicalIndex_encoded table index
                      (members index (by simp)) head.rootPage)
              rw [metadata]
              simp only [Option.bind_eq_bind, Option.bind]
              have physical := head.decode_exact source
                (contains head (by simp)) (pagesBound head (by simp))
              have physical' :
                  CoreDecode.decodeIndexSubtreeFrom source
                      (source.pageCount + 1) head.rootPage =
                    some (CoreDecode.expectedIndexEntries table index) := by
                simpa [identity.2.1, identity.2.2] using physical
              have catalogRoot :
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry).rootPage =
                    head.rootPage := by
                simp [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded]
              rw [catalogRoot, physical']
              simp only [Option.bind_eq_bind, Option.bind]
              rw [dif_pos (by
                simpa [CoreDecode.expectedIndexEntries] using
                  (CoreDecode.expectedIndexEntries_withoutIndexes table index).symm)]
              exact validateCanonicalIndexesForTableFrom_encodeIndexes
                source table head.nextPage indexes tail suffix
                (fun candidate member => members candidate (by simp [member]))
                boundary tailResult
                (fun encoding member => contains encoding (by simp [member]))
                (fun encoding member => pagesBound encoding (by simp [member]))

theorem validateCanonicalIndexGroupsFrom_encodeIndexTableGroups
    (source : CoreDecode.PageSource) :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List IndexEncoding)
      (suffix : List CoreDecode.CatalogEntry),
      Core.TablesWellFormed tables →
      (∀ entry ∈ suffix, ∀ table ∈ tables,
        entry.table ≠ table.schema.name) →
      encodeIndexTableGroups nextPage tables = some encodings →
      (∀ encoding ∈ encodings,
        CorePageCodec.PageSourceContains source encoding.numberedPages) →
      (∀ encoding ∈ encodings,
        encoding.numberedPages.length < source.pageCount + 1) →
      CoreDecode.validateCanonicalIndexGroupsFrom source
        (tables.map Core.Table.withoutIndexes)
        (encodings.map (fun encoding =>
          CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some suffix
  | _, [], encodings, suffix, _, _, encoded, _, _ => by
      simp only [encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, suffix, wellFormed, boundary,
      encoded, contains, pagesBound => by
      simp only [Core.TablesWellFormed, Core.namesUnique, List.map_cons,
        List.pairwise_cons] at wellFormed
      rcases wellFormed with ⟨headDistinct, tailWellFormed⟩
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind]
        at encoded
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
          simp only [currentResult] at encoded
          cases remainingResult : encodeIndexTableGroups
              (nextPage + (indexPagesOf current).length) tables with
          | none => simp [remainingResult] at encoded
          | some remaining =>
              simp only [remainingResult, Option.some.injEq] at encoded
              subst encodings
              simp only [List.map_cons, List.map_append, List.append_assoc]
              unfold CoreDecode.validateCanonicalIndexGroupsFrom
              have remainingBelongs := encodeIndexTableGroups_tables
                remainingResult
              have currentBoundary : ∀ entry ∈
                  (remaining.map (fun encoding =>
                    CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++
                      suffix),
                  entry.table ≠ table.schema.name := by
                intro entry member
                simp only [List.mem_append] at member
                rcases member with encodedMember | suffixMember
                · rcases List.mem_map.mp encodedMember with
                    ⟨encoding, encodingMember, equal⟩
                  subst entry
                  have tableMember := remainingBelongs encoding encodingMember
                  have distinct := headDistinct encoding.table.schema.name
                    (List.mem_map_of_mem tableMember)
                  simpa [IndexEncoding.catalogEntry,
                    CoreDecode.CatalogEntry.ofEncoded] using distinct.symm
                · exact boundary entry suffixMember table (by simp)
              rw [validateCanonicalIndexesForTableFrom_encodeIndexes source
                table nextPage table.indexes current
                (remaining.map (fun encoding =>
                  CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++
                    suffix)
                (by simp) currentBoundary currentResult
                (fun encoding member => contains encoding (by simp [member]))
                (fun encoding member => pagesBound encoding (by simp [member]))]
              have tailBoundary : ∀ entry ∈ suffix,
                  ∀ candidate ∈ tables,
                    entry.table ≠ candidate.schema.name := by
                intro entry entryMember candidate candidateMember
                exact boundary entry entryMember candidate
                  (by simp [candidateMember])
              exact validateCanonicalIndexGroupsFrom_encodeIndexTableGroups
                source (nextPage + (indexPagesOf current).length) tables
                remaining suffix tailWellFormed tailBoundary remainingResult
                (fun encoding member => contains encoding (by simp [member]))
                (fun encoding member => pagesBound encoding (by simp [member]))

theorem applyIndexesForOpen_encoded (source : CoreDecode.PageSource)
    (database : Core.Database) (nextPage : Nat)
    (encodings : List IndexEncoding)
    (encoded : encodeIndexTableGroups nextPage database.tables =
      some encodings)
    (contains : ∀ encoding ∈ encodings,
      CorePageCodec.PageSourceContains source encoding.numberedPages)
    (pagesBound : ∀ encoding ∈ encodings,
      encoding.numberedPages.length < source.pageCount + 1) :
    CoreDecode.applyIndexesForOpen source database.withoutIndexes
      (encodings.map (fun encoding =>
        CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry)) =
          some database.canonicalize := by
  unfold CoreDecode.applyIndexesForOpen
  have validated :=
    validateCanonicalIndexGroupsFrom_encodeIndexTableGroups source nextPage
      database.tables encodings [] database.tablesWellFormed (by simp)
      encoded contains pagesBound
  simp only [List.append_nil] at validated
  have validation : CoreDecode.validateCanonicalIndexesFrom source
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry)) = some () := by
    unfold CoreDecode.validateCanonicalIndexesFrom
    rw [validated]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [dif_pos True.intro]
  simp only [Core.Database.withoutIndexes]
  rw [validation]
  exact rebuildCanonicalDatabase_encoded database nextPage encodings encoded

end CoreWideIndex
end SQLeanite
