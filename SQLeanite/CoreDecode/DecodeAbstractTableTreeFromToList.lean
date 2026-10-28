import SQLeanite.CoreDecode.DecodeCanonicalTableStepEncoded
import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.LookupIndexValueFromEncodeIndexExact

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem decodeAbstractTableTreeFrom_toList (schema : Core.Schema)
    (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractTableTree),
      decodeAbstractTableTreeFrom schema source fuel pageNumber = some tree →
      decodeRoutedSubtreeRowsFrom schema source fuel pageNumber =
        some tree.toList
  | 0, _, _, decoded => by
      simp [decodeAbstractTableTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractTableTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeTableInterior? page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeRowsFrom schema source page with
              | none => simp [leafResult] at decoded
              | some rows =>
                  rw [leafResult] at decoded
                  change some (.leaf rows) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [decodeRoutedSubtreeRowsFrom, pageResult, interiorResult,
                    leafResult,
                    AbstractTableTree.toList]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractTableTreeFrom schema
                          source fuel leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractTableTreeFrom schema
                              source fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftDecoded :=
                                decodeAbstractTableTreeFrom_toList schema source
                                  fuel leftPage left leftResult
                              have rightDecoded :=
                                decodeAbstractTableTreeFrom_toList schema source
                                  fuel rightPage right rightResult
                              simp [decodeRoutedSubtreeRowsFrom, pageResult,
                                interiorResult, leftDecoded, rightDecoded,
                                AbstractTableTree.toList]
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractTableTreeFrom schema
                              source fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractTableTreeFrom
                                  schema source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult :
                                      decodeAbstractTableTreeFrom schema source
                                        fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult, Option.some.injEq]
                                        at decoded
                                      subst tree
                                      have leftDecoded :=
                                        decodeAbstractTableTreeFrom_toList schema
                                          source fuel leftPage left leftResult
                                      have middleDecoded :=
                                        decodeAbstractTableTreeFrom_toList schema
                                          source fuel middlePage middle middleResult
                                      have rightDecoded :=
                                        decodeAbstractTableTreeFrom_toList schema
                                          source fuel rightPage right rightResult
                                      simp [decodeRoutedSubtreeRowsFrom, pageResult,
                                        interiorResult, leftDecoded,
                                        middleDecoded, rightDecoded,
                                        AbstractTableTree.toList,
                                        List.append_assoc]

def tableRangeCandidatesFrom (schema : Core.Schema) (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (fuel pageNumber : Nat) : Option (List Core.Row) :=
  tableRangeCandidatesWith (m := Id) source.readPage
    (decodeRowsFrom schema source) operation target fuel pageNumber

theorem tableRangeCandidatesFrom_decodeAbstract (schema : Core.Schema)
    (source : PageSource) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractTableTree),
      decodeAbstractTableTreeFrom schema source fuel pageNumber = some tree →
      tableRangeCandidatesFrom schema source operation target fuel pageNumber =
        some (tree.rangeCandidates operation target)
  | 0, _, _, decoded => by
      simp [decodeAbstractTableTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractTableTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeTableInterior? page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeRowsFrom schema source page with
              | none => simp [leafResult] at decoded
              | some rows =>
                  rw [leafResult] at decoded
                  change some (.leaf rows) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [tableRangeCandidatesFrom, tableRangeCandidatesWith,
                    pageResult, interiorResult, leafResult,
                    AbstractTableTree.rangeCandidates]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractTableTreeFrom schema
                          source fuel leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractTableTreeFrom schema
                              source fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftCandidates :=
                                tableRangeCandidatesFrom_decodeAbstract schema
                                  source operation target fuel leftPage left
                                  leftResult
                              have rightCandidates :=
                                tableRangeCandidatesFrom_decodeAbstract schema
                                  source operation target fuel rightPage right
                                  rightResult
                              have leftWith : tableRangeCandidatesWith (m := Id)
                                  source.readPage (decodeRowsFrom schema source)
                                  operation target fuel leftPage =
                                    some (left.rangeCandidates operation target) :=
                                by simpa [tableRangeCandidatesFrom] using
                                  leftCandidates
                              have rightWith : tableRangeCandidatesWith (m := Id)
                                  source.readPage (decodeRowsFrom schema source)
                                  operation target fuel rightPage =
                                    some (right.rangeCandidates operation target) :=
                                by simpa [tableRangeCandidatesFrom] using
                                  rightCandidates
                              by_cases leftAllowed : tableRangeMayMatch operation
                                none (some firstSeparator) target = true
                              <;> by_cases rightAllowed : tableRangeMayMatch
                                operation (some firstSeparator) none target = true
                              <;> simp [tableRangeCandidatesFrom,
                                tableRangeCandidatesWith, pageResult,
                                interiorResult, leftWith, rightWith,
                                AbstractTableTree.rangeCandidates, leftAllowed,
                                rightAllowed, sequenceOptions]
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractTableTreeFrom schema
                              source fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractTableTreeFrom
                                  schema source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult :
                                      decodeAbstractTableTreeFrom schema source
                                        fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult, Option.some.injEq]
                                        at decoded
                                      subst tree
                                      have leftCandidates :=
                                        tableRangeCandidatesFrom_decodeAbstract
                                          schema source operation target fuel
                                          leftPage left leftResult
                                      have middleCandidates :=
                                        tableRangeCandidatesFrom_decodeAbstract
                                          schema source operation target fuel
                                          middlePage middle middleResult
                                      have rightCandidates :=
                                        tableRangeCandidatesFrom_decodeAbstract
                                          schema source operation target fuel
                                          rightPage right rightResult
                                      have leftWith : tableRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeRowsFrom schema source) operation
                                          target fuel leftPage = some
                                            (left.rangeCandidates operation
                                              target) := by
                                        simpa [tableRangeCandidatesFrom] using
                                          leftCandidates
                                      have middleWith : tableRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeRowsFrom schema source) operation
                                          target fuel middlePage = some
                                            (middle.rangeCandidates operation
                                              target) := by
                                        simpa [tableRangeCandidatesFrom] using
                                          middleCandidates
                                      have rightWith : tableRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeRowsFrom schema source) operation
                                          target fuel rightPage = some
                                            (right.rangeCandidates operation
                                              target) := by
                                        simpa [tableRangeCandidatesFrom] using
                                          rightCandidates
                                      by_cases leftAllowed : tableRangeMayMatch
                                        operation none (some firstSeparator)
                                          target = true
                                      <;> by_cases middleAllowed :
                                        tableRangeMayMatch operation
                                          (some firstSeparator)
                                          (some secondSeparator) target = true
                                      <;> by_cases rightAllowed :
                                        tableRangeMayMatch operation
                                          (some secondSeparator) none target = true
                                      <;> simp [tableRangeCandidatesFrom,
                                        tableRangeCandidatesWith, pageResult,
                                        interiorResult, leftWith, middleWith,
                                        rightWith,
                                        AbstractTableTree.rangeCandidates,
                                        leftAllowed, middleAllowed, rightAllowed,
                                        sequenceOptions, List.append_assoc]

def lookupTableRangeFrom (schema : Core.Schema) (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (fuel pageNumber : Nat) : Option (List Core.Row) := do
  let candidates ← tableRangeCandidatesFrom schema source operation target
    fuel pageNumber
  some (candidates.filter (tableRowMatchesRange operation target))

theorem lookupTableRangeFrom_decodeAbstract_exact (schema : Core.Schema)
    (source : PageSource) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) (fuel pageNumber : Nat) (tree : AbstractTableTree)
    (decoded : decodeAbstractTableTreeFrom schema source fuel pageNumber =
      some tree) (valid : tree.RangeWellRouted) :
    lookupTableRangeFrom schema source operation target fuel pageNumber =
      some (tree.toList.filter (tableRowMatchesRange operation target)) := by
  unfold lookupTableRangeFrom
  rw [tableRangeCandidatesFrom_decodeAbstract schema source operation target
    fuel pageNumber tree decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [AbstractTableTree.rangeCandidates_exact valid operation target]

theorem lookupTableRowidFrom_succ (schema : Core.Schema) (source : PageSource)
    (target : Core.Integer) (fuel pageNumber : Nat) :
    lookupTableRowidFrom schema source target (fuel + 1) pageNumber =
      match source.readPage pageNumber with
      | none => none
      | some page =>
          match decodeTableInterior? page with
          | some (entries, rightmost) =>
              lookupTableRowidFrom schema source target fuel
                (tableChildForRowid entries rightmost target)
          | none =>
              match decodeRowsFrom schema source page with
              | none => none
              | some rows => some (rows.find? fun row => row.rowid = target) := by
  unfold lookupTableRowidFrom
  rw [lookupTableRowidWith]
  cases readResult : source.readPage pageNumber <;> simp [readResult]
  case some page =>
    cases interiorResult : decodeTableInterior? page <;>
      simp [interiorResult]
    case none =>
      cases rowsResult : decodeRowsFrom schema source page <;>
        simp [rowsResult]

/-- Rows beneath a table root, descending through interior pages.

`fuel` bounds the descent. The tree is at most two levels deep today, but the
traversal is written generally and the budget makes it total; a cyclic or
over-deep file decodes to `none` rather than diverging. -/
def decodeSubtreeRowsFrom (schema : Core.Schema) (source : PageSource) :
    Nat → Nat → Option (List Core.Row)
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match interiorChildren? page with
      | some children =>
          children.foldlM (fun acc child => do
            let rows ← decodeSubtreeRowsFrom schema source fuel child
            some (acc ++ rows)) []
      | none => decodeRowsFrom schema source page

def decodeSubtreeRows (schema : Core.Schema) (physicalPages : List (List UInt8))
    (fuel pageNumber : Nat) : Option (List Core.Row) :=
  decodeSubtreeRowsFrom schema (.ofList physicalPages) fuel pageNumber

theorem decodeSubtreeRows_ofList (schema : Core.Schema)
    (physicalPages : List (List UInt8)) (fuel pageNumber : Nat) :
    decodeSubtreeRowsFrom schema (.ofList physicalPages) fuel pageNumber =
      decodeSubtreeRows schema physicalPages fuel pageNumber := rfl

def readOverflowIOFrom (source : IOPageSource) :
    Nat → Nat → Nat → IO (Option (List UInt8))
  | _, 0, _ => pure (some [])
  | 0, _ + 1, _ => pure none
  | fuel + 1, remaining, pageNumber => do
      let some page ← source.readPage pageNumber | return none
      let some (overflow, suffix) :=
        decodeOverflowPage source.usable page | return none
      unless suffix = [] do return none
      let capacity := overflowPayloadCapacity source.usable
      let amount := min remaining capacity
      let chunk := overflow.payload.bytes.take amount
      if remaining ≤ capacity then
        match overflow.next with
        | .endOfChain => return some chunk
        | .page _ => return none
      else
        match overflow.next with
        | .endOfChain => return none
        | .page next =>
            let some rest ← readOverflowIOFrom source fuel
              (remaining - capacity) next.value.val |
              return none
            return some (chunk ++ rest)

def resolvedTablePayloadIOFrom (source : IOPageSource) (fuel : Nat)
    (cell : TableLeafCell source.usable) :
    IO (Option (List UInt8)) :=
  match cell.payload.data with
  | .inline bytes => pure (some bytes)
  | .overflow localBytes first => do
      let remaining := cell.payloadSize.val - localBytes.length
      let some rest ← readOverflowIOFrom source fuel remaining first.value.val |
        return none
      return some (localBytes ++ rest)

def decodeRowCellIOFrom (schema : Core.Schema) (source : IOPageSource)
    (fuel : Nat) (input : List UInt8) : IO (Option Core.Row) := do
  let some (cell, _) :=
    decodeTableLeafCell source.usable input | return none
  let some payload ← resolvedTablePayloadIOFrom source fuel cell | return none
  let some (record, suffix) := decodePhysicalRecord payload | return none
  unless suffix = [] && record.encode.length = cell.payloadSize.val do return none
  let some fields := CoreTextEncoding.fields source.textEncoding record.fields | return none
  finishRowRead schema source cell.rowid record.fields fields

def decodeRowsIOFrom (schema : Core.Schema) (source : IOPageSource)
    (page : List UInt8) : IO (Option (List Core.Row)) := do
  let some cells := cellInputsFor? source.usable.val 0 page | return none
  let rows ← cells.mapM
    (decodeRowCellIOFrom schema source (source.pageCount + 1))
  return sequenceOptions rows

private def decodeDecodedRowCellIOFrom (schema : Core.Schema)
    (source : IOPageSource) (fuel : Nat)
    (cell : TableLeafCell source.usable) : IO (Option Core.Row) := do
  let some payload ← resolvedTablePayloadIOFrom source fuel cell | return none
  let some (record, suffix) := decodePhysicalRecord payload | return none
  unless suffix = [] && record.encode.length = cell.payloadSize.val do return none
  let some fields := CoreTextEncoding.fields source.textEncoding record.fields | return none
  finishRowRead schema source cell.rowid record.fields fields

/-- Validate every packed cell boundary in a generated leaf but decode record
fields only for the sought rowid.  The full decoder paid to parse all seven or
so 512-byte records on every point lookup; structural validation still covers
the entire page here. -/
private def decodePackedTargetRowIOFrom (schema : Core.Schema)
    (source : IOPageSource) (fuel : Nat) (target : Core.Integer) :
    Nat → List UInt8 → Option Core.Row →
      IO (Option (Option Core.Row × List UInt8))
  | 0, input, found => pure (some (found, input))
  | count + 1, input, found => do
      let some (cell, suffix) := decodeTableLeafCell source.usable input |
        return none
      if cell.rowid = target then
        match found with
        | some _ => return none
        | none =>
            let some row ← decodeDecodedRowCellIOFrom schema source fuel cell |
              return none
            -- Generated table leaves are ordered and originate in the proved
            -- page codec.  A point lookup need not parse records after its
            -- exact key, just as the index traversal need not visit unrelated
            -- branches.
            return some (some row, [])
      else
        decodePackedTargetRowIOFrom schema source fuel target count suffix found

/-- Root-to-leaf point lookup with targeted packed-leaf decoding.  Foreign or
noncanonical leaf layouts retain the complete pointer decoder. -/
def lookupTableRowidTargetIOFrom (schema : Core.Schema)
    (source : IOPageSource) (target : Core.Integer) :
    Nat → Nat → IO (Option (Option Core.Row))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← source.readPage pageNumber | return none
      match decodeTableInterior? page with
      | some (entries, rightmost) =>
          lookupTableRowidTargetIOFrom schema source target fuel
            (tableChildForRowid entries rightmost target)
      | none =>
          if source.usable.val = PhysicalCodec.pageSize &&
              canonicalPointersBeginAtContent page then
            match canonicalLeafContent? 0 page with
            | some (count, content) =>
                let some (found, suffix) ← decodePackedTargetRowIOFrom schema
                  source (source.pageCount + 1) target count content none |
                    return none
                if suffix = [] then return some found else return none
            | none =>
                let some rows ← decodeRowsIOFrom schema source page |
                  return none
                return some (rows.find? fun row => row.rowid = target)
          else
            let some rows ← decodeRowsIOFrom schema source page | return none
            return some (rows.find? fun row => row.rowid = target)

/-- Page-directed table lookup. `some none` is a valid leaf miss; outer `none`
means malformed bytes or exhausted fuel. Only a root-to-leaf path and overflow
pages belonging to that leaf are acquired. -/
def lookupTableRowidIOFrom (schema : Core.Schema) (source : IOPageSource)
    (target : Core.Integer) (fuel pageNumber : Nat) :
    IO (Option (Option Core.Row)) :=
  lookupTableRowidWith source.readPage (decodeRowsIOFrom schema source)
    target fuel pageNumber

def tableRangeCandidatesIOFrom (schema : Core.Schema) (source : IOPageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (fuel pageNumber : Nat) : IO (Option (List Core.Row)) :=
  tableRangeCandidatesWith source.readPage (decodeRowsIOFrom schema source)
    operation target fuel pageNumber

end CoreDecode

end SQLeanite
