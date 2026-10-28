import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.AbstractIndexTreeEqualityCandidatesExact

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem leftmostIndexLeafFrom_decodeAbstract (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      leftmostIndexLeafFrom source fuel pageNumber = some tree.leftmostLeaf
  | 0, _, _, decoded => by simp [decodeAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractIndexTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeIndexLeafFrom source page with
              | none => simp [leafResult] at decoded
              | some entries =>
                  rw [leafResult] at decoded
                  change some (.leaf entries) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [leftmostIndexLeafFrom, leftmostIndexLeafWith,
                    pageResult, interiorResult, leafResult,
                    AbstractIndexTree.leftmostLeaf]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractIndexTreeFrom source fuel
                          leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractIndexTreeFrom source
                              fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftLeaf := leftmostIndexLeafFrom_decodeAbstract
                                source fuel leftPage left leftResult
                              simpa [leftmostIndexLeafFrom,
                                leftmostIndexLeafWith, pageResult,
                                interiorResult, leftLeaf,
                                AbstractIndexTree.leftmostLeaf] using leftLeaf
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractIndexTreeFrom source
                              fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractIndexTreeFrom
                                  source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult : decodeAbstractIndexTreeFrom
                                      source fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult,
                                        Option.some.injEq] at decoded
                                      subst tree
                                      have leftLeaf :=
                                        leftmostIndexLeafFrom_decodeAbstract source
                                          fuel leftPage left leftResult
                                      simpa [leftmostIndexLeafFrom,
                                        leftmostIndexLeafWith, pageResult,
                                        interiorResult, leftLeaf,
                                        AbstractIndexTree.leftmostLeaf] using
                                          leftLeaf

def lookupIndexPrefixFrom (source : PageSource) (limit fuel pageNumber : Nat) :
    Option (List IndexEntry) := do
  let leaf ← leftmostIndexLeafFrom source fuel pageNumber
  if limit ≤ leaf.length then some (leaf.take limit) else none

theorem lookupIndexPrefixFrom_decodeAbstract_exact (source : PageSource)
    (limit fuel pageNumber : Nat) (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (fits : limit ≤ tree.leftmostLeaf.length) :
    lookupIndexPrefixFrom source limit fuel pageNumber =
      some (tree.toList.take limit) := by
  unfold lookupIndexPrefixFrom
  rw [leftmostIndexLeafFrom_decodeAbstract source fuel pageNumber tree decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  simp [fits, tree.take_toList_eq_take_leftmostLeaf limit fits]

/-- Fold an arbitrary SQLite interior-page fanout into the binary promoted-key
abstraction. This changes only proof topology: in-order contents still contain
each interior record exactly once. -/
def AbstractIndexTree.branchChain
    (groups : List (AbstractIndexTree × IndexEntry))
    (right : AbstractIndexTree) : AbstractIndexTree :=
  groups.foldr (fun group suffix => .branch2 group.1 group.2 suffix) right

theorem AbstractIndexTree.branchChain_toList
    (groups : List (AbstractIndexTree × IndexEntry))
    (right : AbstractIndexTree) :
    (AbstractIndexTree.branchChain groups right).toList =
      (groups.map fun group => group.1.toList ++ [group.2]).flatten ++
        right.toList := by
  induction groups with
  | nil => rfl
  | cons group groups induction =>
      unfold AbstractIndexTree.branchChain at induction ⊢
      simp only [List.foldr, AbstractIndexTree.toList, List.map_cons,
        List.flatten_cons]
      rw [induction]
      simp [List.append_assoc]

def decodeIndexGroupWith {α : Type} (decodeChild : Nat → Option α)
    (entry : Nat × IndexEntry) : Option (α × IndexEntry) := do
  let child ← decodeChild entry.1
  some (child, entry.2)

def decodeFlatIndexGroupFrom (source : PageSource) (fuel : Nat)
    (entry : Nat × IndexEntry) : Option (List IndexEntry) := do
  let child ← decodeIndexSubtreeFrom source fuel entry.1
  some (child ++ [entry.2])

/-- General-arity proof decoder for C-produced SQLite index pages. Generated
pages continue to use `decodeAbstractIndexTreeFrom`, whose exact structural
refinement is stronger. Reopen validation compares this tree's complete
in-order contents with the decoded logical index before retaining it. -/
def decodeWideAbstractIndexTreeFrom (source : PageSource) :
    Nat → Nat → Option AbstractIndexTree
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeIndexInteriorFrom source page with
      | some ([], _) => none
      | some (entries, rightPage) => do
          let groups ← entries.mapM (decodeIndexGroupWith
            (decodeWideAbstractIndexTreeFrom source fuel))
          let right ← decodeWideAbstractIndexTreeFrom source fuel rightPage
          some (AbstractIndexTree.branchChain groups right)
      | none => .leaf <$> decodeIndexLeafFrom source page

private theorem decodeWideGroups_toList (source : PageSource) (fuel : Nat)
    (childRefines : ∀ pageNumber tree,
      decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree →
      decodeIndexSubtreeFrom source fuel pageNumber = some tree.toList) :
    ∀ (entries : List (Nat × IndexEntry))
      (groups : List (AbstractIndexTree × IndexEntry)),
      entries.mapM (decodeIndexGroupWith
        (decodeWideAbstractIndexTreeFrom source fuel)) = some groups →
      entries.mapM (decodeFlatIndexGroupFrom source fuel) =
        some (groups.map fun group => group.1.toList ++ [group.2])
  | [], groups, decoded => by
      simp only [List.mapM_nil, pure, Pure.pure, Option.some.injEq] at decoded
      subst groups
      rfl
  | entry :: entries, groups, decoded => by
      cases childResult : decodeWideAbstractIndexTreeFrom source fuel entry.1 with
      | none =>
          simp [List.mapM_cons, decodeIndexGroupWith,
            childResult] at decoded
      | some child =>
          simp only [List.mapM_cons] at decoded
          change (decodeIndexGroupWith
              (decodeWideAbstractIndexTreeFrom source fuel) entry >>=
            fun head => entries.mapM (decodeIndexGroupWith
              (decodeWideAbstractIndexTreeFrom source fuel)) >>= fun tail =>
                some (head :: tail)) = some groups at decoded
          simp only [decodeIndexGroupWith, childResult,
            Option.bind_eq_bind, Option.bind] at decoded
          cases tailResult : entries.mapM
              (decodeIndexGroupWith
                (decodeWideAbstractIndexTreeFrom source fuel)) with
          | none =>
              rw [tailResult] at decoded
              contradiction
          | some tail =>
              rw [tailResult] at decoded
              simp only [Option.bind_eq_bind, Option.bind,
                Option.some.injEq] at decoded
              subst groups
              have childDecoded := childRefines entry.1 child childResult
              have tailDecoded := decodeWideGroups_toList source fuel
                childRefines entries tail tailResult
              simp [List.mapM_cons, decodeFlatIndexGroupFrom,
                childDecoded, tailDecoded]

/-- The arbitrary-fanout abstract decoder is not merely validated against a
logical index after reopening: whenever it succeeds, its in-order abstraction
is exactly the ordinary complete physical index decode. -/
theorem decodeWideAbstractIndexTreeFrom_toList (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree →
      decodeIndexSubtreeFrom source fuel pageNumber = some tree.toList
  | 0, _, _, decoded => by
      simp [decodeWideAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeWideAbstractIndexTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeIndexLeafFrom source page with
              | none => simp [leafResult] at decoded
              | some entries =>
                  rw [leafResult] at decoded
                  change some (.leaf entries) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [decodeIndexSubtreeFrom, pageResult, interiorResult,
                    leafResult, AbstractIndexTree.toList]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  change ((first :: rest).mapM
                      (decodeIndexGroupWith
                        (decodeWideAbstractIndexTreeFrom source fuel)) >>=
                    fun groups =>
                    decodeWideAbstractIndexTreeFrom source fuel rightPage >>=
                      fun right => some
                        (AbstractIndexTree.branchChain groups right)) =
                    some tree at decoded
                  cases groupsResult : (first :: rest).mapM
                      (decodeIndexGroupWith
                        (decodeWideAbstractIndexTreeFrom source fuel)) with
                  | none =>
                      rw [groupsResult] at decoded
                      contradiction
                  | some groups =>
                      rw [groupsResult] at decoded
                      simp only [Option.bind_eq_bind, Option.bind] at decoded
                      cases rightResult : decodeWideAbstractIndexTreeFrom source
                          fuel rightPage with
                      | none =>
                          rw [rightResult] at decoded
                          contradiction
                      | some right =>
                          rw [rightResult] at decoded
                          simp only [Option.some.injEq] at decoded
                          subst tree
                          have rightDecoded :=
                            decodeWideAbstractIndexTreeFrom_toList source fuel
                              rightPage right rightResult
                          have groupsDecoded :
                              (first :: rest).mapM
                                (decodeFlatIndexGroupFrom source fuel) =
                                some (groups.map fun group =>
                                  group.1.toList ++ [group.2]) := by
                            exact decodeWideGroups_toList source fuel
                              (decodeWideAbstractIndexTreeFrom_toList source fuel)
                              (first :: rest) groups groupsResult
                          simp only [decodeIndexSubtreeFrom, pageResult,
                            Option.bind_eq_bind, Option.bind, interiorResult]
                          change ((first :: rest).mapM
                              (decodeFlatIndexGroupFrom source fuel) >>=
                            fun decodedGroups =>
                            decodeIndexSubtreeFrom source fuel rightPage >>=
                              fun decodedRight =>
                                some (decodedGroups.flatten ++ decodedRight)) =
                            some (AbstractIndexTree.branchChain groups right).toList
                          rw [groupsDecoded, rightDecoded]
                          simp [AbstractIndexTree.branchChain_toList]

end CoreDecode

end SQLeanite
