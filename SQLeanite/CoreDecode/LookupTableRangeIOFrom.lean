import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeAbstractTableTreeFromToList

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

/-- Page-directed primary-key range lookup.  The outer `none` denotes malformed
or over-deep bytes; a successful empty list is a valid range miss. -/
def lookupTableRangeIOFrom (schema : Core.Schema) (source : IOPageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (fuel pageNumber : Nat) : IO (Option (List Core.Row)) := do
  let some candidates ← tableRangeCandidatesIOFrom schema source operation
    target fuel pageNumber | return none
  return some (candidates.filter (tableRowMatchesRange operation target))

def resolvedIndexPayloadIOFrom (source : IOPageSource) (fuel : Nat)
    (cell : LeafIndexCell source.usable) :
    IO (Option (List UInt8)) :=
  match cell.payload.data with
  | .inline bytes => pure (some bytes)
  | .overflow localBytes first => do
      let remaining := cell.payloadSize.val - localBytes.length
      let some rest ← readOverflowIOFrom source fuel remaining first.value.val |
        return none
      return some (localBytes ++ rest)

def decodeIndexCellIOFrom (source : IOPageSource) (fuel : Nat)
    (input : List UInt8) : IO (Option IndexEntry) := do
  let some (cell, _) :=
    decodeLeafIndexCell source.usable input | return none
  let some payload ← resolvedIndexPayloadIOFrom source fuel cell | return none
  let some (record, suffix) := decodePhysicalRecord payload | return none
  unless suffix = [] && record.encode.length = cell.payloadSize.val do return none
  let some fields := CoreTextEncoding.fields source.textEncoding record.fields | return none
  match fields with
  | [valueField, rowidField] =>
      let some value := PhysicalCodec.decodeValueField valueField | return none
      let some rowidValue := PhysicalCodec.decodeValueField rowidField | return none
      match rowidValue with
      | .integer rowid => return some ⟨value, rowid⟩
      | _ => return none
  | _ => return none

/-- A source used only for the inline fast path below.  Canonical packed cells
which contain no overflow pointer never consult `readPage`; an overflow cell
therefore fails closed and is retried by the general effectful decoder. -/
private def inlineOnlyPageSource (pageCount : Nat) : PageSource := {
  pageCount
  readPage := fun _ => none }

/-- General pointer-array leaf decoding retained as the compatibility and
overflow fallback. -/
private def decodeIndexLeafIOByPointersFrom (source : IOPageSource)
    (page : List UInt8) : IO (Option (List IndexEntry)) := do
  let some offsets := leafIndexOffsetsFor? source.usable.val page | return none
  let entries ← offsets.mapM fun offset =>
    decodeIndexCellIOFrom source (source.pageCount + 1) (page.drop offset)
  return sequenceOptions entries

def decodeIndexLeafIOFrom (source : IOPageSource) (page : List UInt8) :
    IO (Option (List IndexEntry)) := do
  if source.textEncoding ≤ 1 && source.usable.val = PhysicalCodec.pageSize &&
      canonicalIndexLeafPointersBeginAtContent page then
    match canonicalIndexLeafContent? page with
    | some (count, content) =>
        match decodePackedIndexCellsFrom
            (inlineOnlyPageSource source.pageCount) (source.pageCount + 1)
            count content with
        | some (entries, []) => return some entries
        | _ => decodeIndexLeafIOByPointersFrom source page
    | none => decodeIndexLeafIOByPointersFrom source page
  else decodeIndexLeafIOByPointersFrom source page

/-- General pointer-array interior decoding retained for foreign layouts and
cells whose payload spills to overflow pages. -/
private def decodeIndexInteriorIOByPointersFrom (source : IOPageSource)
    (page : List UInt8) : IO (Option (List (Nat × IndexEntry) × Nat)) := do
  unless page.length = source.usable.val do return none
  let some (header, afterHeader) := decodeBTreePageHeader page | return none
  match header with
  | .interiorIndex common rightmost =>
      let some (offsets, _) := decodeOffsets common.cellCount.val afterHeader |
        return none
      let entries ← offsets.mapM fun offset => do
        unless offset < page.length do return none
        let some (child, afterChild) :=
          decodeUnsignedFixed 4 (page.drop offset) | return none
        let some key ← decodeIndexCellIOFrom source
          (source.pageCount + 1) afterChild | return none
        return some (child, key)
      return (sequenceOptions entries).map fun values => (values, rightmost.val)
  | _ => return none

def decodeIndexInteriorIOFrom (source : IOPageSource) (page : List UInt8) :
    IO (Option (List (Nat × IndexEntry) × Nat)) := do
  if source.textEncoding ≤ 1 && source.usable.val = PhysicalCodec.pageSize &&
      canonicalIndexInteriorPointersBeginAtContent page then
    match canonicalIndexInteriorContent? page with
    | some (count, rightmost, content) =>
        match decodePackedIndexInteriorCellsFrom
            (inlineOnlyPageSource source.pageCount) (source.pageCount + 1)
            count content with
        | some (entries, []) => return some (entries, rightmost)
        | _ => decodeIndexInteriorIOByPointersFrom source page
    | none => decodeIndexInteriorIOByPointersFrom source page
  else decodeIndexInteriorIOByPointersFrom source page

/-- A decoded index page suitable for statement-batch memoization.  The sum
keeps the same classification and payload consumed by
`indexValueCandidatesWith`; caching changes acquisition cost, not routing. -/
inductive DecodedIndexPage where
  | interior (entries : List (Nat × IndexEntry)) (rightmost : Nat)
  | leaf (entries : List IndexEntry)

def decodeIndexPageIOFrom (source : IOPageSource) (pageNumber : Nat) :
    IO (Option DecodedIndexPage) := do
  let some page ← source.readPage pageNumber | return none
  match ← decodeIndexInteriorIOFrom source page with
  | some (entries, rightmost) => return some (.interior entries rightmost)
  | none =>
      let some entries ← decodeIndexLeafIOFrom source page | return none
      return some (.leaf entries)

/-- Equality traversal over already-classified pages.  This is the decoded
page analogue of `indexValueCandidatesWith`: the bounds, promoted entries,
fuel, and result construction are identical. -/
def indexValueCandidatesDecodedWith [Monad m]
    (readDecoded : Nat → m (Option DecodedIndexPage))
    (target : Core.Value) : Nat → Nat → m (Option (List IndexEntry))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readDecoded pageNumber | return none
      match page with
      | .leaf entries => return some entries
      | .interior entries rightmost => do
          let lowers := none :: entries.map (fun entry => some entry.2)
          let groups ← (entries.zip lowers).mapM fun bounded => do
            let entry := bounded.1
            let lower := bounded.2
            let left ← if indexLowerAllows lower target &&
                indexUpperAllows target entry.2 then
              indexValueCandidatesDecodedWith readDecoded target fuel entry.1
            else pure (some [])
            return left.map fun values => values ++ [entry.2]
          let visitRight := match entries.getLast? with
            | none => true
            | some entry => indexLowerAllows (some entry.2) target
          let right ← if visitRight then
            indexValueCandidatesDecodedWith readDecoded target fuel rightmost
          else pure (some [])
          let some groups := sequenceOptions groups | return none
          let some right := right | return none
          return some (groups.flatten ++ right)

def lookupIndexValueDecodedWith [Monad m]
    (readDecoded : Nat → m (Option DecodedIndexPage))
    (target : Core.Value) (fuel pageNumber : Nat) :
    m (Option (List IndexEntry)) := do
  let some candidates ←
    indexValueCandidatesDecodedWith readDecoded target fuel pageNumber |
      return none
  return some (candidates.filter (fun entry => entry.matchesValue target))

def decodeIndexPageFrom (source : PageSource) (pageNumber : Nat) :
    Option DecodedIndexPage := do
  let page ← source.readPage pageNumber
  match decodeIndexInteriorFrom source page with
  | some (entries, rightmost) => some (.interior entries rightmost)
  | none => .leaf <$> decodeIndexLeafFrom source page

/-- Memoizing decoded pages is a semantics-preserving implementation
substitution: with the ordinary decoder as its provider, the decoded traversal
is exactly the original byte-page traversal. -/
theorem indexValueCandidatesDecodedWith_eq_from
    (source : PageSource) (target : Core.Value) :
    ∀ fuel pageNumber,
      indexValueCandidatesDecodedWith (m := Id)
          (decodeIndexPageFrom source) target fuel pageNumber =
        indexValueCandidatesFrom source target fuel pageNumber := by
  intro fuel
  induction fuel with
  | zero => intro pageNumber; rfl
  | succ fuel induction =>
      intro pageNumber
      cases pageResult : source.readPage pageNumber with
      | none =>
          simp [indexValueCandidatesDecodedWith, indexValueCandidatesFrom,
            indexValueCandidatesWith, decodeIndexPageFrom, pageResult]
      | some page =>
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              cases leafResult : decodeIndexLeafFrom source page with
              | none =>
                  simp [indexValueCandidatesDecodedWith,
                    indexValueCandidatesFrom, indexValueCandidatesWith,
                    decodeIndexPageFrom, pageResult, interiorResult, leafResult]
              | some entries =>
                  simp [indexValueCandidatesDecodedWith,
                    indexValueCandidatesFrom, indexValueCandidatesWith,
                    decodeIndexPageFrom, pageResult, interiorResult, leafResult]
          | some interior =>
              rcases interior with ⟨entries, rightmost⟩
              simp [indexValueCandidatesDecodedWith, indexValueCandidatesFrom,
                indexValueCandidatesWith, decodeIndexPageFrom, pageResult,
                interiorResult, induction]
              rfl

theorem lookupIndexValueDecodedWith_eq_from
    (source : PageSource) (target : Core.Value) (fuel pageNumber : Nat) :
    lookupIndexValueDecodedWith (m := Id) (decodeIndexPageFrom source)
        target fuel pageNumber =
      lookupIndexValueFrom source target fuel pageNumber := by
  have candidates := indexValueCandidatesDecodedWith_eq_from source target
    fuel pageNumber
  cases result : indexValueCandidatesFrom source target fuel pageNumber with
  | none => simp [lookupIndexValueDecodedWith, lookupIndexValueFrom,
      candidates, result]
  | some entries => simp [lookupIndexValueDecodedWith, lookupIndexValueFrom,
      candidates, result]

def decodeIndexSubtreeIOFrom (source : IOPageSource) :
    Nat → Nat → IO (Option (List IndexEntry))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← source.readPage pageNumber | return none
      let interior ← decodeIndexInteriorIOFrom source page
      match interior with
      | some (entries, rightmost) => do
          let groups ← entries.mapM fun entry => do
            let left ← decodeIndexSubtreeIOFrom source fuel entry.1
            return left.map fun values => values ++ [entry.2]
          let some groups := sequenceOptions groups | return none
          let some right ← decodeIndexSubtreeIOFrom source fuel rightmost |
            return none
          return some (groups.flatten ++ right)
      | none => decodeIndexLeafIOFrom source page

def leftmostIndexLeafIOFrom (source : IOPageSource)
    (fuel pageNumber : Nat) : IO (Option (List IndexEntry)) :=
  leftmostIndexLeafWith source.readPage (decodeIndexInteriorIOFrom source)
    (decodeIndexLeafIOFrom source) fuel pageNumber

/-- Effectful multi-leaf in-order cursor. It shares all traversal decisions
with `indexPrefixFrom`, whose exactness theorem includes promoted interior
entries and arbitrary generated tree height. -/
def lookupIndexPrefixIOFrom (source : IOPageSource)
    (limit fuel pageNumber : Nat) : IO (Option (List IndexEntry)) :=
  indexPrefixWith source.readPage (decodeIndexInteriorIOFrom source)
    (decodeIndexLeafIOFrom source) limit fuel pageNumber

/-- Effectful counterpart of `indexValueCandidatesFrom`; it preserves the same
page-directed branch selection while acquiring only visited pages. -/
def indexValueCandidatesIOFrom (source : IOPageSource) (target : Core.Value)
    (fuel pageNumber : Nat) : IO (Option (List IndexEntry)) :=
  indexValueCandidatesWith source.readPage
    (decodeIndexInteriorIOFrom source) (decodeIndexLeafIOFrom source)
    target fuel pageNumber

def lookupIndexValueIOFrom (source : IOPageSource) (target : Core.Value)
    (fuel pageNumber : Nat) : IO (Option (List IndexEntry)) := do
  let some candidates ←
    indexValueCandidatesIOFrom source target fuel pageNumber | return none
  return some (candidates.filter (fun entry => entry.matchesValue target))

def indexRangeCandidatesIOFrom (source : IOPageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    Nat → Nat → IO (Option (List IndexEntry)) :=
  indexRangeCandidatesWith source.readPage
    (decodeIndexInteriorIOFrom source) (decodeIndexLeafIOFrom source)
    operation target

def lookupIndexRangeIOFrom (source : IOPageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) : IO (Option (List IndexEntry)) := do
  let some candidates ← indexRangeCandidatesIOFrom source operation target
    fuel pageNumber | return none
  return some (candidates.filter
    (fun entry => entry.matchesRange operation target))

def decodeSubtreeRowsIOFrom (schema : Core.Schema) (source : IOPageSource) :
    Nat → Nat → IO (Option (List Core.Row))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← source.readPage pageNumber | return none
      match interiorChildrenFor? source.usable.val page with
      | some children => do
          let groups ← children.mapM fun child =>
            decodeSubtreeRowsIOFrom schema source fuel child
          let some groups := sequenceOptions groups | return none
          return some groups.flatten
      | none => decodeRowsIOFrom schema source page

def decodeTableFrom (source : PageSource) (entry : CatalogEntry) :
    Option Core.Table := do
  if _isTable : entry.kind = "table" then
    let sql ← entry.sql
    let schema ← parseTableSchema sql
    if _nameMatches : schema.name = entry.name then
      let rows ← decodeSubtreeRowsFrom schema source
        (source.pageCount + 1) entry.rootPage
      (Core.Table.rebuildFromCatalog schema [] rows sql).toOption
    else none
  else none

def decodeTable (pages : List (List UInt8)) (entry : CatalogEntry) :
    Option Core.Table :=
  decodeTableFrom (.ofList pages) entry

theorem decodeTable_ofList (pages : List (List UInt8)) (entry : CatalogEntry) :
    decodeTableFrom (.ofList pages) entry = decodeTable pages entry := rfl

def decodeTableIOFrom (source : IOPageSource) (entry : CatalogEntry) :
    IO (Option Core.Table) := do
  if _isTable : entry.kind = "table" then
    let some sql := entry.sql | return none
    let some schema := parseTableSchema sql | return none
    if _nameMatches : schema.name = entry.name then
      let some rows ← decodeSubtreeRowsIOFrom schema source
        (source.pageCount + 1) entry.rootPage | return none
      return (Core.Table.rebuildFromCatalog schema [] rows sql).toOption
    else return none
  else return none

/-- Validate the contiguous canonical index run belonging to one table.
Unlike `applyIndexesFrom`, this operation has no metadata side effects: it
checks the physical promoted-key tree exactly and returns the unconsumed
catalog suffix.  Generated images use this path; arbitrary SQLite images keep
the general compatibility path below. -/
def validateCanonicalIndexesForTableFrom (source : PageSource)
    (table : Core.Table) : List CatalogEntry → Option (List CatalogEntry)
  | [] => some []
  | entry :: entries =>
      if _sameTable : entry.table = table.schema.name then do
        let index ← decodeCanonicalIndex table.schema table.schema.name entry
        let physical ← decodeIndexSubtreeFrom source
          (source.pageCount + 1) entry.rootPage
        if _contentsMatch : physical = expectedIndexEntries table index then
          validateCanonicalIndexesForTableFrom source table entries
        else none
      else some (entry :: entries)

def validateCanonicalIndexGroupsFrom (source : PageSource) :
    List Core.Table → List CatalogEntry → Option (List CatalogEntry)
  | [], entries => some entries
  | table :: tables, entries => do
      let remaining ← validateCanonicalIndexesForTableFrom source table entries
      validateCanonicalIndexGroupsFrom source tables remaining

def validateCanonicalIndexesFrom (source : PageSource)
    (tables : List Core.Table) (entries : List CatalogEntry) : Option Unit := do
  let suffix ← validateCanonicalIndexGroupsFrom source tables entries
  if _consumed : suffix = [] then some () else none

theorem validateCanonicalIndexesForTableFrom_encodeOverflowIndexes
    (source : PageSource) (table : Core.Table) :
    ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List CoreOverflow.IndexEncoding)
      (suffix : List CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      CoreOverflow.encodeIndexes nextPage
          (indexes.map fun index => (table, index)) = some encodings →
      (∀ encoding ∈ encodings,
        ReadsPagesFrom source encoding.rootPage encoding.pages) →
      (∀ encoding ∈ encodings, 0 < encoding.rootPage) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length < 2 ^ 32) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length ≤ source.pageCount + 1) →
      validateCanonicalIndexesForTableFrom source table.withoutIndexes
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some suffix
  | _, [], encodings, suffix, _, boundary, encoded, _, _, _, _ => by
      simp only [List.map_nil, CoreOverflow.encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold validateCanonicalIndexesForTableFrom
          rw [dif_neg (by simpa using boundary entry (by simp))]
  | nextPage, index :: indexes, encodings, suffix, members, boundary,
      encoded, reads, positive, pageBound, sourceBound => by
      simp only [List.map_cons, CoreOverflow.encodeIndexes,
        Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : CoreOverflow.encodeIndex nextPage table index with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : CoreOverflow.encodeIndexes
            (nextPage + head.pages.length)
            (indexes.map fun candidate => (table, candidate)) with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          simp only [List.map_cons, List.cons_append]
          unfold validateCanonicalIndexesForTableFrom
          have identity := CoreOverflow.encodeIndex_identity headResult
          have sameTable :
              (CatalogEntry.ofEncoded head.catalogEntry).table =
                table.withoutIndexes.schema.name := by
            simp [CoreOverflow.IndexEncoding.catalogEntry,
              CatalogEntry.ofEncoded, identity.1]
          rw [dif_pos sameTable]
          have metadata : decodeCanonicalIndex table.withoutIndexes.schema
              table.withoutIndexes.schema.name
              (CatalogEntry.ofEncoded head.catalogEntry) = some index := by
            simp only [Core.Table.withoutIndexes_schema]
            rw [show head = {
              table := table
              index := index
              rootPage := nextPage
              topology := head.topology
              treePages := head.treePages
              overflowPages := head.overflowPages
            } from by cases head; simp_all]
            change decodeCanonicalIndex table.schema table.schema.name
              (CatalogEntry.ofEncoded ({
                kind := "index"
                name := index.name
                table := table.schema.name
                rootPage := nextPage
                sql := CoreFile.indexSQL table index
                sqlIsNull := index.isImplicitPrimary table.schema
              } : CoreFile.CatalogEntry)) = some index
            exact decodeCanonicalIndex_encoded table index
              (members index (by simp)) nextPage
          rw [metadata]
          simp only [Option.bind_eq_bind, Option.bind]
          have headReads : ReadsPagesFrom source nextPage head.pages := by
            simpa [identity.2.2] using reads head (by simp)
          have physical := decodeIndexSubtreeFrom_encodeIndex source headResult
            headReads (by simpa [identity.2.2] using positive head (by simp))
            (by simpa [identity.2.2] using pageBound head (by simp))
            (by simpa [identity.2.2] using sourceBound head (by simp))
          have catalogRoot :
              (CatalogEntry.ofEncoded head.catalogEntry).rootPage =
                nextPage := by
            simp [CoreOverflow.IndexEncoding.catalogEntry,
              CatalogEntry.ofEncoded, identity.2.2]
          rw [catalogRoot, physical]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [dif_pos (by
            simpa [expectedIndexEntries] using
              (expectedIndexEntries_withoutIndexes table index).symm)]
          exact validateCanonicalIndexesForTableFrom_encodeOverflowIndexes
            source table (nextPage + head.pages.length) indexes tail suffix
            (fun candidate member => members candidate (by simp [member]))
            boundary tailResult
            (fun encoding member => reads encoding (by simp [member]))
            (fun encoding member => positive encoding (by simp [member]))
            (fun encoding member => pageBound encoding (by simp [member]))
            (fun encoding member => sourceBound encoding (by simp [member]))

end CoreDecode

end SQLeanite
