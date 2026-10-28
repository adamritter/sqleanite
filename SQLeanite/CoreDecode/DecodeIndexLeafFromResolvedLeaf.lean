import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.IndexPlanDecodesOfCells

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem decodeIndexLeafFrom_resolvedLeaf (index : Core.Index)
    (source : PageSource) (rows : List Core.Row)
    (plans : List CoreOverflow.CellPlan) (next : Nat)
    (resolved : CoreOverflow.Resolved) (page : CoreFile.Page)
    (planned : rows.mapM (CoreOverflow.indexCellPlan? index) = some plans)
    (resolvedResult : CoreOverflow.resolvePlans next plans = some resolved)
    (built : CoreFile.indexLeafPage? resolved.cells = some page)
    (nextPositive : 0 < next)
    (pageBound : next + resolved.pages.length < 2 ^ 32)
    (fuelBound : resolved.pages.length < source.pageCount + 1)
    (reads : ReadsPagesFrom source next resolved.pages) :
    decodeIndexLeafFrom source page.bytes =
      some (rows.map fun row => ⟨row.value index.column, row.rowid⟩) := by
  unfold CoreFile.indexLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 10 0 resolved.cells with
  | none => simp [bodyResult] at built
  | some body =>
    simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
    injection built with pageEqual
    subst page
    have bodyExact : body.bytes = CoreFile.replaceFirst 10
        (PhysicalCodec.leafPageBody 0 resolved.cells) ∧
        PhysicalCodec.PageFit 0 resolved.cells := by
      unfold CoreFile.leafBody? at bodyResult
      split at bodyResult
      next typeByte =>
        split at bodyResult
        next fits =>
          injection bodyResult with bodyEqual
          subst body
          exact ⟨rfl, fits⟩
        next doesNotFit => contradiction
      next invalidType => contradiction
    rcases bodyExact with ⟨bodyBytes, fits⟩
    have content := canonicalIndexLeafContent_leafPageBody resolved.cells fits
    have pointers := canonicalIndexLeafPointers_leafPageBody resolved.cells fits
    have planLength := mapM_length_of_eq_some
      (CoreOverflow.indexCellPlan? index) rows plans planned
    have cellLength := CoreOverflow.resolvePlans_cells_length resolvedResult
    have countEqual : resolved.cells.length = rows.length := by omega
    have decoded := decodePackedIndexCellsFrom_resolvePlans index source
      (source.pageCount + 1) rows plans next resolved planned resolvedResult
      nextPositive pageBound fuelBound reads []
    simp only [List.append_nil] at decoded
    change decodeIndexLeafFrom source body.bytes = _
    rw [bodyBytes]
    unfold decodeIndexLeafFrom
    rw [pointers, content, countEqual]
    simp [decoded]

theorem decodeIndexLeafFrom_indexLeafPage
    (source : PageSource) {cells : List (List UInt8)}
    {entries : List IndexEntry} {page : CoreFile.Page}
    (decoded : IndexCellsDecode source (source.pageCount + 1) cells entries)
    (built : CoreFile.indexLeafPage? cells = some page) :
    decodeIndexLeafFrom source page.bytes = some entries := by
  unfold CoreFile.indexLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 10 0 cells with
  | none => simp [bodyResult] at built
  | some body =>
    simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
    injection built with pageEqual
    subst page
    have bodyExact : body.bytes = CoreFile.replaceFirst 10
        (PhysicalCodec.leafPageBody 0 cells) ∧
        PhysicalCodec.PageFit 0 cells := by
      unfold CoreFile.leafBody? at bodyResult
      split at bodyResult
      next typeByte =>
        split at bodyResult
        next fits =>
          injection bodyResult with bodyEqual
          subst body
          exact ⟨rfl, fits⟩
        next doesNotFit => contradiction
      next invalidType => contradiction
    rcases bodyExact with ⟨bodyBytes, fits⟩
    have content := canonicalIndexLeafContent_leafPageBody cells fits
    have pointers := canonicalIndexLeafPointers_leafPageBody cells fits
    have packed := decodePackedIndexCellsFrom_of_relation decoded []
    simp only [List.append_nil] at packed
    change decodeIndexLeafFrom source body.bytes = _
    rw [bodyBytes]
    unfold decodeIndexLeafFrom
    rw [pointers, content]
    simp [packed]

def decodeIndexInteriorByPointersFrom (source : PageSource)
    (page : List UInt8) : Option (List (Nat × IndexEntry) × Nat) := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    let (header, afterHeader) ← decodeBTreePageHeader page
    match header with
    | .interiorIndex common rightmost => do
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        let entries ← offsets.mapM fun offset => do
          if _bounded : offset < page.length then
            let (child, afterChild) ← decodeUnsignedFixed 4 (page.drop offset)
            let key ← decodeIndexCellFrom source (source.pageCount + 1) afterChild
            some (child, key)
          else none
        some (entries, rightmost.val)
    | _ => none
  else none

def decodeIndexInteriorFrom (source : PageSource) (page : List UInt8) :
    Option (List (Nat × IndexEntry) × Nat) :=
  match page with
  | 10 :: _ => none
  | _ =>
      if canonicalIndexInteriorPointersBeginAtContent page then
        match canonicalIndexInteriorContent? page with
        | some (count, rightmost, content) =>
            match decodePackedIndexInteriorCellsFrom source
                (source.pageCount + 1) count content with
            | some (entries, []) => some (entries, rightmost)
            | _ => decodeIndexInteriorByPointersFrom source page
        | none => decodeIndexInteriorByPointersFrom source page
      else
        decodeIndexInteriorByPointersFrom source page

theorem decodeIndexInteriorFrom_indexLeafPage
    (source : PageSource) {cells : List (List UInt8)} {page : CoreFile.Page}
    (built : CoreFile.indexLeafPage? cells = some page) :
    decodeIndexInteriorFrom source page.bytes = none := by
  unfold CoreFile.indexLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 10 0 cells with
  | none => simp [bodyResult] at built
  | some body =>
    simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
    injection built with pageEqual
    subst page
    have bodyBytes : body.bytes = CoreFile.replaceFirst 10
        (PhysicalCodec.leafPageBody 0 cells) := by
      unfold CoreFile.leafBody? at bodyResult
      split at bodyResult
      next typeByte =>
        split at bodyResult
        next fits =>
          injection bodyResult with bodyEqual
          subst body
          rfl
        next doesNotFit => contradiction
      next invalidType => contradiction
    change decodeIndexInteriorFrom source body.bytes = none
    rw [bodyBytes]
    unfold decodeIndexInteriorFrom
    simp [CoreFile.replaceFirst, PhysicalCodec.leafPageBody,
      PhysicalCodec.leafHeader]

theorem boundedU32?_value {value : Nat} {bounded : U32Value}
    (success : RecursivePageBTree.boundedU32? value = some bounded) :
    bounded.val = value := by
  unfold RecursivePageBTree.boundedU32? at success
  split at success
  next => injection success with equal; subst bounded; rfl
  next => contradiction

theorem decodeIndexInteriorFrom_indexInteriorPage_one
    (source : PageSource) {child right : Nat} {separator : List UInt8}
    {separatorEntry : IndexEntry} {page : CoreFile.Page}
    (separatorDecoded : ∀ suffix,
      decodeIndexCellWithSuffixFrom source (source.pageCount + 1)
          (separator ++ suffix) = some (separatorEntry, suffix))
    (built : RecursivePageBTree.indexInteriorPage?
      [(child, separator)] right = some page) :
    decodeIndexInteriorFrom source page.bytes =
      some ([(child, separatorEntry)], right) := by
  unfold RecursivePageBTree.indexInteriorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
    simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
    cases childResult : RecursivePageBTree.boundedU32? child with
    | none => simp [List.mapM_cons, childResult] at built
    | some childPage =>
      simp only [List.mapM_cons, childResult, List.mapM_nil, pure, Pure.pure,
        Option.bind_eq_bind, Option.bind] at built
      split at built
      next fits =>
        injection built with pageEqual
        subst page
        let cell := PhysicalTableBTree.encodeU32Nat childPage.val ++ separator
        have content := canonicalIndexInteriorContent_interiorPageBody
          rightmost [cell] fits
        have pointers := canonicalIndexInteriorPointers_interiorPageBody
          rightmost [cell] fits
        unfold decodeIndexInteriorFrom
        rw [pointers, content]
        simp only [if_pos rfl]
        unfold decodePackedIndexInteriorCellsFrom
        simp only [PhysicalCodec.cellBytes, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.length_cons,
          List.length_nil, cell, List.append_assoc]
        unfold PhysicalTableBTree.encodeU32Nat
        rw [decodeUnsignedFixed_encode _ childPage.isLt]
        simp only [Option.bind_eq_bind, Option.bind]
        have decodedEmpty := separatorDecoded []
        simp only [List.append_nil] at decodedEmpty
        rw [decodedEmpty]
        simp [decodePackedIndexInteriorCellsFrom,
          boundedU32?_value childResult, boundedU32?_value rightResult,
          CoreFile.replaceFirst, PhysicalTableBTree.interiorPageBody,
          PhysicalTableBTree.interiorHeader]
      next doesNotFit => contradiction

theorem decodeIndexInteriorFrom_indexInteriorPage_two
    (source : PageSource) {firstChild secondChild right : Nat}
    {firstSeparator secondSeparator : List UInt8}
    {firstEntry secondEntry : IndexEntry} {page : CoreFile.Page}
    (firstDecoded : ∀ suffix,
      decodeIndexCellWithSuffixFrom source (source.pageCount + 1)
          (firstSeparator ++ suffix) = some (firstEntry, suffix))
    (secondDecoded : ∀ suffix,
      decodeIndexCellWithSuffixFrom source (source.pageCount + 1)
          (secondSeparator ++ suffix) = some (secondEntry, suffix))
    (built : RecursivePageBTree.indexInteriorPage?
      [(firstChild, firstSeparator), (secondChild, secondSeparator)] right =
        some page) :
    decodeIndexInteriorFrom source page.bytes =
      some ([(firstChild, firstEntry), (secondChild, secondEntry)], right) := by
  unfold RecursivePageBTree.indexInteriorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
    simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
    cases firstResult : RecursivePageBTree.boundedU32? firstChild with
    | none => simp [List.mapM_cons, firstResult] at built
    | some firstPage =>
      simp only [List.mapM_cons, firstResult, Option.bind_eq_bind,
        Option.bind] at built
      cases secondResult : RecursivePageBTree.boundedU32? secondChild with
      | none => simp [List.mapM_cons, secondResult] at built
      | some secondPage =>
        simp only [List.mapM_cons, secondResult, List.mapM_nil, pure,
          Pure.pure, Option.bind_eq_bind, Option.bind] at built
        split at built
        next fits =>
          injection built with pageEqual
          subst page
          let firstCell := PhysicalTableBTree.encodeU32Nat firstPage.val ++
            firstSeparator
          let secondCell := PhysicalTableBTree.encodeU32Nat secondPage.val ++
            secondSeparator
          have content := canonicalIndexInteriorContent_interiorPageBody
            rightmost [firstCell, secondCell] fits
          have pointers := canonicalIndexInteriorPointers_interiorPageBody
            rightmost [firstCell, secondCell] fits
          unfold decodeIndexInteriorFrom
          rw [pointers, content]
          simp only [if_pos rfl]
          unfold decodePackedIndexInteriorCellsFrom
          simp only [PhysicalCodec.cellBytes, List.flatten_cons,
            List.flatten_nil, List.append_nil, List.length_cons,
            List.length_nil, firstCell, secondCell, List.append_assoc]
          unfold PhysicalTableBTree.encodeU32Nat
          rw [decodeUnsignedFixed_encode _ firstPage.isLt]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [firstDecoded
            (FileFormat.encodeUnsignedFixed 4 secondPage.val ++
              secondSeparator)]
          simp only [Option.bind_eq_bind, Option.bind]
          unfold decodePackedIndexInteriorCellsFrom
          rw [decodeUnsignedFixed_encode _ secondPage.isLt]
          simp only [Option.bind_eq_bind, Option.bind]
          have decodedEmpty := secondDecoded []
          simp only [List.append_nil] at decodedEmpty
          rw [decodedEmpty]
          simp [decodePackedIndexInteriorCellsFrom,
            boundedU32?_value firstResult,
            boundedU32?_value secondResult, boundedU32?_value rightResult,
            CoreFile.replaceFirst, PhysicalTableBTree.interiorPageBody,
            PhysicalTableBTree.interiorHeader]
        next doesNotFit => contradiction

/-- Traverse a physical SQLite index B-tree, retaining promoted interior keys
in their in-order positions. The fuel makes malformed cycles total. -/
def decodeIndexSubtreeFrom (source : PageSource) :
    Nat → Nat → Option (List IndexEntry)
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeIndexInteriorFrom source page with
      | some (entries, rightmost) => do
          let groups ← entries.mapM fun entry => do
            let left ← decodeIndexSubtreeFrom source fuel entry.1
            some (left ++ [entry.2])
          let right ← decodeIndexSubtreeFrom source fuel rightmost
          some (groups.flatten ++ right)
      | none => decodeIndexLeafFrom source page

def decodeIndexSubtree (physicalPages : List (List UInt8))
    (fuel pageNumber : Nat) : Option (List IndexEntry) :=
  decodeIndexSubtreeFrom (.ofList physicalPages) fuel pageNumber

theorem decodeIndexSubtree_ofList (physicalPages : List (List UInt8))
    (fuel pageNumber : Nat) :
    decodeIndexSubtreeFrom (.ofList physicalPages) fuel pageNumber =
      decodeIndexSubtree physicalPages fuel pageNumber := rfl

end CoreDecode

end SQLeanite
