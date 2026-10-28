import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.AbstractIndexTreeIntegerOrdered

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem AbstractIndexTree.equalityCandidates_exact {tree : AbstractIndexTree}
    (valid : tree.WellRouted) (target : Core.Value) :
    (tree.equalityCandidates target).filter
        (fun entry => entry.matchesValue target) =
      tree.toList.filter (fun entry => entry.matchesValue target) := by
  induction valid with
  | leaf entries => rfl
  | branch2 left right separator leftValid rightValid leftAdmitted
      rightAdmitted leftInduction rightInduction =>
      have leftExact :
          ((if indexUpperAllows target separator then
              left.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            left.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : indexUpperAllows target separator with
        | true => simpa [allowed] using leftInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              left.toList _ allowed
              (fun entry member matched =>
                leftAdmitted target entry member matched)
            simp [allowed, empty]
      have rightExact :
          ((if indexLowerAllows (some separator) target then
              right.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            right.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : indexLowerAllows (some separator) target with
        | true => simpa [allowed] using rightInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              right.toList _ allowed
              (fun entry member matched =>
                rightAdmitted target entry member matched)
            simp [allowed, empty]
      simp only [AbstractIndexTree.equalityCandidates,
        AbstractIndexTree.toList, List.filter_append]
      rw [leftExact, rightExact]
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid leftAdmitted middleAdmitted rightAdmitted
      leftInduction middleInduction rightInduction =>
      have leftExact :
          ((if indexUpperAllows target firstSeparator then
              left.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            left.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : indexUpperAllows target firstSeparator with
        | true => simpa [allowed] using leftInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              left.toList _ allowed
              (fun entry member matched =>
                leftAdmitted target entry member matched)
            simp [allowed, empty]
      let middleAllowed := indexLowerAllows (some firstSeparator) target &&
        indexUpperAllows target secondSeparator
      have middleExact :
          ((if middleAllowed then middle.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            middle.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : middleAllowed with
        | true => simpa [middleAllowed, allowed] using middleInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              middle.toList middleAllowed allowed
              (fun entry member matched =>
                middleAdmitted target entry member matched)
            simp [middleAllowed, allowed, empty]
      have rightExact :
          ((if indexLowerAllows (some secondSeparator) target then
              right.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            right.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : indexLowerAllows (some secondSeparator) target with
        | true => simpa [allowed] using rightInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              right.toList _ allowed
              (fun entry member matched =>
                rightAdmitted target entry member matched)
            simp [allowed, empty]
      simp only [AbstractIndexTree.equalityCandidates,
        AbstractIndexTree.toList, List.filter_append]
      change _ = _
      rw [leftExact, middleExact, rightExact]

/-- Decode the exact binary 2-3 shape emitted by SQLeanite's persistent index
planner. Wider C SQLite nodes deliberately return `none` and retain the
validated fallback until the general-arity refinement is proved. -/
def decodeAbstractIndexTreeFrom (source : PageSource) :
    Nat → Nat → Option AbstractIndexTree
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeIndexInteriorFrom source page with
      | some ([(leftPage, separator)], rightPage) => do
          let left ← decodeAbstractIndexTreeFrom source fuel leftPage
          let right ← decodeAbstractIndexTreeFrom source fuel rightPage
          some (.branch2 left separator right)
      | some ([(leftPage, firstSeparator),
          (middlePage, secondSeparator)], rightPage) => do
          let left ← decodeAbstractIndexTreeFrom source fuel leftPage
          let middle ← decodeAbstractIndexTreeFrom source fuel middlePage
          let right ← decodeAbstractIndexTreeFrom source fuel rightPage
          some (.branch3 left firstSeparator middle secondSeparator right)
      | some _ => none
      | none => .leaf <$> decodeIndexLeafFrom source page

/-- Follow only the left edge of an index B-tree.  The same recursion is used
by the kernel-reducible proof target and the live pread reader. -/
def leftmostIndexLeafWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeInterior : List UInt8 →
      m (Option (List (Nat × IndexEntry) × Nat)))
    (decodeLeaf : List UInt8 → m (Option (List IndexEntry))) :
    Nat → Nat → m (Option (List IndexEntry))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      let interior ← decodeInterior page
      match interior with
      | some (first :: _, _) =>
          leftmostIndexLeafWith readPage decodeInterior decodeLeaf fuel first.1
      | some ([], _) => return none
      | none => decodeLeaf page

def leftmostIndexLeafFrom (source : PageSource) (fuel pageNumber : Nat) :
    Option (List IndexEntry) :=
  leftmostIndexLeafWith (m := Id) source.readPage
    (decodeIndexInteriorFrom source) (decodeIndexLeafFrom source)
    fuel pageNumber

/-- Read an in-order prefix across as many generated index leaves as needed.
Interior records are logical index entries in SQLite, so each separator is
emitted exactly once between the prefixes of its adjacent children. Recursion
stops as soon as `limit` entries have been obtained. -/
def indexPrefixWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeInterior : List UInt8 →
      m (Option (List (Nat × IndexEntry) × Nat)))
    (decodeLeaf : List UInt8 → m (Option (List IndexEntry))) :
    Nat → Nat → Nat → m (Option (List IndexEntry))
  | 0, _, _ => pure (some [])
  | _ + 1, 0, _ => pure none
  | limit + 1, fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      let interior ← decodeInterior page
      match interior with
      | some ([(leftPage, separator)], rightPage) => do
          let some left ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit + 1) fuel leftPage | return none
          if _leftFilled : left.length = limit + 1 then return some left
          let some right ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit - left.length) fuel rightPage | return none
          return some (left ++ [separator] ++ right)
      | some ([(leftPage, firstSeparator),
          (middlePage, secondSeparator)], rightPage) => do
          let some left ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit + 1) fuel leftPage | return none
          if _leftFilled : left.length = limit + 1 then return some left
          let some middle ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit - left.length) fuel middlePage | return none
          let beforeRight := left ++ [firstSeparator] ++ middle
          if _middleFilled : beforeRight.length = limit + 1 then
            return some beforeRight
          let some right ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit - beforeRight.length) fuel rightPage | return none
          return some (beforeRight ++ [secondSeparator] ++ right)
      | some _ => return none
      | none => return (← decodeLeaf page).map (List.take (limit + 1))

def indexPrefixFrom (source : PageSource) (limit fuel pageNumber : Nat) :
    Option (List IndexEntry) :=
  indexPrefixWith (m := Id) source.readPage
    (decodeIndexInteriorFrom source) (decodeIndexLeafFrom source)
    limit fuel pageNumber

theorem take_append_singleton_of_length_lt (left right : List α) (value : α)
    (limit : Nat) (short : left.length < limit) :
    (left ++ [value] ++ right).take limit =
      left ++ [value] ++ right.take (limit - left.length - 1) := by
  simp only [List.singleton_append, List.append_assoc]
  rw [List.take_append,
    List.take_of_length_le (Nat.le_of_lt short)]
  have remaining : 0 < limit - left.length := by omega
  cases difference : limit - left.length with
  | zero => omega
  | succ amount =>
      simp only [difference, List.take_succ_cons, List.singleton_append,
        Nat.succ_sub_one]

theorem AbstractIndexTree.cursorPrefix_eq_take (tree : AbstractIndexTree)
    (limit : Nat) :
    tree.cursorPrefix limit = tree.toList.take limit := by
  induction tree generalizing limit with
  | leaf entries =>
      cases limit <;>
        simp [AbstractIndexTree.cursorPrefix, AbstractIndexTree.toList]
  | branch2 left separator right leftInduction rightInduction =>
      cases limit with
      | zero => simp [AbstractIndexTree.cursorPrefix, AbstractIndexTree.toList]
      | succ amount =>
          simp only [AbstractIndexTree.cursorPrefix, leftInduction,
            AbstractIndexTree.toList, List.append_assoc]
          split
          next filled =>
            have long : amount + 1 ≤ left.toList.length := by
              simp only [List.length_take] at filled
              omega
            rw [List.take_append_of_le_length long]
          next notFilled =>
            have short : left.toList.length < amount + 1 := by
              simp only [List.length_take] at notFilled
              omega
            rw [List.take_of_length_le (Nat.le_of_lt short), rightInduction]
            have remaining : amount - left.toList.length =
                amount + 1 - left.toList.length - 1 := by omega
            rw [remaining]
            simpa only [List.append_assoc] using
              (take_append_singleton_of_length_lt left.toList right.toList
                separator (amount + 1) short).symm
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      cases limit with
      | zero => simp [AbstractIndexTree.cursorPrefix, AbstractIndexTree.toList]
      | succ amount =>
          simp only [AbstractIndexTree.cursorPrefix, leftInduction,
            middleInduction, AbstractIndexTree.toList, List.append_assoc]
          split
          next filled =>
            have long : amount + 1 ≤ left.toList.length := by
              simp only [List.length_take] at filled
              omega
            rw [List.take_append_of_le_length long]
          next leftNotFilled =>
            have leftShort : left.toList.length < amount + 1 := by
              simp only [List.length_take] at leftNotFilled
              omega
            rw [List.take_of_length_le (Nat.le_of_lt leftShort)]
            let remaining := amount - left.toList.length
            split
            next middleFilled =>
              have middleLong : remaining ≤ middle.toList.length := by
                simp only [List.length_append, List.length_cons,
                  List.length_nil, List.length_take] at middleFilled
                dsimp [remaining]
                omega
              have firstTake := take_append_singleton_of_length_lt
                left.toList
                (middle.toList ++ [secondSeparator] ++ right.toList)
                firstSeparator (amount + 1) leftShort
              have remainingEq : amount + 1 - left.toList.length - 1 =
                  remaining := by
                dsimp [remaining]
                omega
              rw [remainingEq] at firstTake
              simp only [List.append_assoc] at firstTake
              rw [List.take_append_of_le_length middleLong] at firstTake
              dsimp [remaining] at middleLong ⊢
              simpa [List.append_assoc] using firstTake.symm
            next middleNotFilled =>
              have middleShort : middle.toList.length < remaining := by
                simp only [List.length_append, List.length_cons,
                  List.length_nil, List.length_take] at middleNotFilled
                dsimp [remaining]
                omega
              rw [List.take_of_length_le (Nat.le_of_lt middleShort),
                rightInduction]
              let beforeRight :=
                left.toList ++ [firstSeparator] ++ middle.toList
              have beforeShort : beforeRight.length < amount + 1 := by
                dsimp [beforeRight, remaining] at ⊢
                simp only [List.length_append, List.length_cons,
                  List.length_nil]
                omega
              have finalTake := take_append_singleton_of_length_lt
                beforeRight right.toList secondSeparator (amount + 1)
                beforeShort
              have finalRemaining : amount + 1 - beforeRight.length - 1 =
                  amount - beforeRight.length := by omega
              rw [finalRemaining] at finalTake
              dsimp [beforeRight, remaining] at finalTake ⊢
              simpa [List.append_assoc] using finalTake.symm

theorem indexPrefixFrom_decodeAbstract_cursor (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree) (limit : Nat),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      indexPrefixFrom source limit fuel pageNumber =
        some (tree.cursorPrefix limit)
  | 0, _, _, _, decoded => by
      simp [decodeAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, limit, decoded => by
      cases limit with
      | zero => simp [indexPrefixFrom, indexPrefixWith,
          AbstractIndexTree.cursorPrefix]
      | succ amount =>
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
                      subst tree
                      simp [indexPrefixFrom, indexPrefixWith, pageResult,
                        interiorResult, leafResult,
                        AbstractIndexTree.cursorPrefix]
              | some interior =>
                  rcases interior with ⟨entries, rightPage⟩
                  simp only [interiorResult] at decoded
                  cases entries with
                  | nil => contradiction
                  | cons first rest =>
                      rcases first with ⟨leftPage, firstSeparator⟩
                      cases rest with
                      | nil =>
                          cases leftResult : decodeAbstractIndexTreeFrom source
                              fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases rightResult : decodeAbstractIndexTreeFrom
                                  source fuel rightPage with
                              | none => simp [rightResult] at decoded
                              | some right =>
                                  simp only [rightResult, Option.some.injEq]
                                    at decoded
                                  subst tree
                                  have leftCursor :=
                                    indexPrefixFrom_decodeAbstract_cursor source
                                      fuel leftPage left (amount + 1) leftResult
                                  simp only [indexPrefixFrom] at leftCursor
                                  have rightCursor := fun requested =>
                                    indexPrefixFrom_decodeAbstract_cursor source
                                      fuel rightPage right requested rightResult
                                  simp only [indexPrefixFrom] at rightCursor
                                  simp [indexPrefixFrom, indexPrefixWith,
                                    pageResult, interiorResult, leftCursor,
                                    rightCursor,
                                    AbstractIndexTree.cursorPrefix]
                                  split <;> simp_all
                      | cons second tail =>
                          rcases second with ⟨middlePage, secondSeparator⟩
                          cases tail with
                          | cons third remaining => contradiction
                          | nil =>
                              cases leftResult : decodeAbstractIndexTreeFrom
                                  source fuel leftPage with
                              | none => simp [leftResult] at decoded
                              | some left =>
                                  simp only [leftResult, Option.bind_eq_bind,
                                    Option.bind] at decoded
                                  cases middleResult :
                                      decodeAbstractIndexTreeFrom source fuel
                                        middlePage with
                                  | none => simp [middleResult] at decoded
                                  | some middle =>
                                      simp only [middleResult] at decoded
                                      cases rightResult :
                                          decodeAbstractIndexTreeFrom source fuel
                                            rightPage with
                                      | none => simp [rightResult] at decoded
                                      | some right =>
                                          simp only [rightResult,
                                            Option.some.injEq] at decoded
                                          subst tree
                                          have leftCursor :=
                                            indexPrefixFrom_decodeAbstract_cursor
                                              source fuel leftPage left
                                                (amount + 1) leftResult
                                          simp only [indexPrefixFrom] at leftCursor
                                          have middleCursor := fun requested =>
                                            indexPrefixFrom_decodeAbstract_cursor
                                              source fuel middlePage middle
                                                requested middleResult
                                          simp only [indexPrefixFrom] at middleCursor
                                          have rightCursor := fun requested =>
                                            indexPrefixFrom_decodeAbstract_cursor
                                              source fuel rightPage right
                                                requested rightResult
                                          simp only [indexPrefixFrom] at rightCursor
                                          simp [indexPrefixFrom, indexPrefixWith,
                                            pageResult, interiorResult,
                                            leftCursor, middleCursor,
                                            rightCursor,
                                            AbstractIndexTree.cursorPrefix]
                                          split
                                          next condition => simp [condition]
                                          next condition =>
                                            split <;> simp_all

theorem indexPrefixFrom_decodeAbstract_exact (source : PageSource)
    (limit fuel pageNumber : Nat) (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree) :
    indexPrefixFrom source limit fuel pageNumber =
      some (tree.toList.take limit) := by
  rw [indexPrefixFrom_decodeAbstract_cursor source fuel pageNumber tree limit
    decoded, tree.cursorPrefix_eq_take]

end CoreDecode

end SQLeanite
