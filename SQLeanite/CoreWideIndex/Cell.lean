import SQLeanite.CoreDecode.DecodeIndexLeafFromResolvedLeaf

namespace SQLeanite
namespace CoreWideIndex

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
          rcases Option.bind_eq_some_iff.mp mapped with
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
      rcases Option.bind_eq_some_iff.mp built with
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

end CoreWideIndex

end SQLeanite
