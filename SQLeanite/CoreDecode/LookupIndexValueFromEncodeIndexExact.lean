import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.ExistsCertifiedIntegerIndexOfEncodeIndex

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

/-- A directed equality lookup over generated INTEGER-index pages is exact
without running the linear certificate checker. -/
theorem lookupIndexValueFrom_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (integers : CoreFile.indexValuesInteger table index = true)
    (target : Core.Value) :
    lookupIndexValueFrom source target (source.pageCount + 1) rootPage =
      some ((expectedIndexEntries table index).filter
        (fun entry => entry.matchesValue target)) := by
  rcases existsCertifiedIntegerIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource integers with ⟨certificate⟩
  exact lookupIndexValueFrom_certified_exact certificate target

/-- The analogous exactness result for half-bounded range traversal. -/
theorem lookupIndexRangeFrom_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (integers : CoreFile.indexValuesInteger table index = true)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    lookupIndexRangeFrom source operation target (source.pageCount + 1)
        rootPage =
      some ((expectedIndexEntries table index).filter
        (fun entry => entry.matchesRange operation target)) := by
  rcases existsCertifiedIntegerIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource integers with ⟨certificate⟩
  exact lookupIndexRangeFrom_certified_exact certificate operation target

/-- Child page numbers of an interior table page: one per cell, then the
rightmost pointer. `none` when the page is not an interior table page. -/
def interiorChildren? (page : List UInt8) : Option (List Nat) := do
  if page.length == PhysicalCodec.pageSize then
    match page with
    | 5 :: _ :: _ :: countHigh :: countLow :: _ :: _ :: _ ::
        first :: second :: third :: fourth :: afterHeader => do
        let cellCount := decodeU16 countHigh countLow
        let rightmost := decodeU32 ⟨first, second, third, fourth⟩
        let offsets ← decodeOffsetList cellCount afterHeader
        let children ← offsets.mapM fun offset => do
          match (page.drop offset).take 4 with
          | [first, second, third, fourth] =>
              some (decodeU32 ⟨first, second, third, fourth⟩)
          | _ => none
        some (children ++ [rightmost])
    | _ => none
  else none

def interiorChildrenFor? (pageSize : Nat) (page : List UInt8) :
    Option (List Nat) := do
  if page.length == pageSize then
    match page with
    | 5 :: _ :: _ :: countHigh :: countLow :: _ :: _ :: _ ::
        first :: second :: third :: fourth :: afterHeader => do
        let cellCount := decodeU16 countHigh countLow
        let rightmost := decodeU32 ⟨first, second, third, fourth⟩
        let offsets ← decodeOffsetList cellCount afterHeader
        let children ← offsets.mapM fun offset => do
          match (page.drop offset).take 4 with
          | [first, second, third, fourth] =>
              some (decodeU32 ⟨first, second, third, fourth⟩)
          | _ => none
        some (children ++ [rightmost])
    | _ => none
  else none

/-- Decode table-interior routing cells as `(left child, greatest rowid in
that child)`, plus the rightmost child. Unlike index interiors, these keys are
separators rather than stored logical rows. -/
def decodeTableInterior? (page : List UInt8) :
    Option (List (Nat × Core.Integer) × Nat) := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    let (header, afterHeader) ← decodeBTreePageHeader page
    match header with
    | .interiorTable common rightmost => do
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        let entries ← offsets.mapM fun offset => do
          if _bounded : offset < page.length then
            let (cell, _) ← decodeInteriorTableCell (page.drop offset)
            some (cell.leftChildPage.value.val, cell.key)
          else none
        some (entries, rightmost.val)
    | _ => none
  else none

def tableChildForRowid (entries : List (Nat × Core.Integer))
    (rightmost : Nat) (rowid : Core.Integer) : Nat :=
  match entries.find? (fun entry => decide (rowid.value ≤ entry.2.value)) with
  | some entry => entry.1
  | none => rightmost

/-- One traversal shared by the pure proof target and the live `IO` reader.
Only page acquisition and leaf/overflow decoding vary; interior classification,
separator comparison, fuel accounting, and row selection are identical. -/
def lookupTableRowidWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeLeaf : List UInt8 → m (Option (List Core.Row)))
    (target : Core.Integer) : Nat → Nat → m (Option (Option Core.Row))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      match decodeTableInterior? page with
      | some (entries, rightmost) =>
          lookupTableRowidWith readPage decodeLeaf target fuel
            (tableChildForRowid entries rightmost target)
      | none => do
          let some rows ← decodeLeaf page | return none
          return some (rows.find? fun row => row.rowid = target)

/-- Kernel-reducible pure specialization used by the encoder completeness
proof. -/
def lookupTableRowidFrom (schema : Core.Schema) (source : PageSource)
    (target : Core.Integer) (fuel pageNumber : Nat) : Option (Option Core.Row) :=
  lookupTableRowidWith (m := Id) source.readPage
    (decodeRowsFrom schema source) target fuel pageNumber

/-- Whether a table-child rowid interval can contain a primary-key match.
Table interior keys are inclusive upper bounds for the child on their left;
the preceding key is an exclusive lower bound.  The non-strict lower test for
`lessEqual` is intentionally conservative and can visit one boundary child,
but can never omit a matching row. -/
def tableRangeMayMatch (operation : PhysicalQuery.Comparison)
    (lower upper : Option Core.Integer) (target : Core.Integer) : Bool :=
  match operation with
  | .less => match lower with
      | none => true
      | some bound => decide (bound.value < target.value)
  | .lessEqual => match lower with
      | none => true
      | some bound => decide (bound.value ≤ target.value)
  | .greater => match upper with
      | none => true
      | some bound => decide (target.value < bound.value)
  | .greaterEqual => match upper with
      | none => true
      | some bound => decide (target.value ≤ bound.value)

/-- One separator-directed table range traversal shared by the pure proof
target and the live IO reader.  Interior separator records are routing data,
not logical table rows, so unlike index traversal they are not emitted. -/
def tableRangeCandidatesWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeLeaf : List UInt8 → m (Option (List Core.Row)))
    (operation : PhysicalQuery.Comparison) (target : Core.Integer) :
    Nat → Nat → m (Option (List Core.Row))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      match decodeTableInterior? page with
      | some (entries, rightmost) => do
          let lowers := none :: entries.map (fun entry => some entry.2)
          let groups ← (entries.zip lowers).mapM fun bounded => do
            let entry := bounded.1
            let lower := bounded.2
            if tableRangeMayMatch operation lower (some entry.2) target then
              tableRangeCandidatesWith readPage decodeLeaf operation target
                fuel entry.1
            else pure (some [])
          let lower := entries.getLast?.map (fun entry => entry.2)
          let right ← if tableRangeMayMatch operation lower none target then
            tableRangeCandidatesWith readPage decodeLeaf operation target
              fuel rightmost
          else pure (some [])
          let some groups := sequenceOptions groups | return none
          let some right := right | return none
          return some (groups.flatten ++ right)
      | none => decodeLeaf page

def tableRowMatchesRange (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) (row : Core.Row) : Bool :=
  PhysicalQuery.sqlCompare operation (.integer row.rowid) (.integer target) =
    .true

/-- Proof abstraction of the binary/ternary table topology emitted by the
persistent page store.  Table separator keys are not logical rows, so `toList`
contains only leaf contents. -/
inductive AbstractTableTree where
  | leaf (rows : List Core.Row)
  | branch2 (left : AbstractTableTree) (separator : Core.Integer)
      (right : AbstractTableTree)
  | branch3 (left : AbstractTableTree) (firstSeparator : Core.Integer)
      (middle : AbstractTableTree) (secondSeparator : Core.Integer)
      (right : AbstractTableTree)

def AbstractTableTree.toList : AbstractTableTree → List Core.Row
  | .leaf rows => rows
  | .branch2 left _ right => left.toList ++ right.toList
  | .branch3 left _ middle _ right =>
      left.toList ++ middle.toList ++ right.toList

def AbstractTableTree.rangeCandidates
    (operation : PhysicalQuery.Comparison) (target : Core.Integer) :
    AbstractTableTree → List Core.Row
  | .leaf rows => rows
  | .branch2 left separator right =>
      (if tableRangeMayMatch operation none (some separator) target then
        left.rangeCandidates operation target else []) ++
      (if tableRangeMayMatch operation (some separator) none target then
        right.rangeCandidates operation target else [])
  | .branch3 left firstSeparator middle secondSeparator right =>
      (if tableRangeMayMatch operation none (some firstSeparator) target then
        left.rangeCandidates operation target else []) ++
      (if tableRangeMayMatch operation (some firstSeparator)
          (some secondSeparator) target then
        middle.rangeCandidates operation target else []) ++
      (if tableRangeMayMatch operation (some secondSeparator) none target then
        right.rangeCandidates operation target else [])

/-- Every child containing a matching row is admitted by the executable
separator test.  This is a semantic routing invariant, not a claim that a
particular query happened to return the expected answer. -/
inductive AbstractTableTree.RangeWellRouted : AbstractTableTree → Prop where
  | leaf (rows : List Core.Row) : RangeWellRouted (.leaf rows)
  | branch2 (left right : AbstractTableTree) (separator : Core.Integer)
      (leftValid : left.RangeWellRouted) (rightValid : right.RangeWellRouted)
      (leftAdmitted : ∀ operation target row, row ∈ left.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation none (some separator) target = true)
      (rightAdmitted : ∀ operation target row, row ∈ right.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation (some separator) none target = true) :
      RangeWellRouted (.branch2 left separator right)
  | branch3 (left middle right : AbstractTableTree)
      (firstSeparator secondSeparator : Core.Integer)
      (leftValid : left.RangeWellRouted)
      (middleValid : middle.RangeWellRouted)
      (rightValid : right.RangeWellRouted)
      (leftAdmitted : ∀ operation target row, row ∈ left.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation none (some firstSeparator) target = true)
      (middleAdmitted : ∀ operation target row, row ∈ middle.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation (some firstSeparator)
          (some secondSeparator) target = true)
      (rightAdmitted : ∀ operation target row, row ∈ right.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation (some secondSeparator) none target = true) :
      RangeWellRouted
        (.branch3 left firstSeparator middle secondSeparator right)

private theorem filter_table_range_eq_nil_of_not_admitted
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (rows : List Core.Row) (allowed : Bool) (notAllowed : allowed = false)
    (admitted : ∀ row, row ∈ rows →
      tableRowMatchesRange operation target row = true → allowed = true) :
    rows.filter (tableRowMatchesRange operation target) = [] := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      have tailAdmitted : ∀ candidate, candidate ∈ rows →
          tableRowMatchesRange operation target candidate = true →
          allowed = true := by
        intro candidate member matched
        exact admitted candidate (by simp [member]) matched
      have tailEmpty := induction tailAdmitted
      by_cases matched : tableRowMatchesRange operation target row = true
      · have contradiction := admitted row (by simp) matched
        rw [notAllowed] at contradiction
        contradiction
      · simp [matched, tailEmpty]

theorem AbstractTableTree.rangeCandidates_exact {tree : AbstractTableTree}
    (valid : tree.RangeWellRouted) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) :
    (tree.rangeCandidates operation target).filter
        (tableRowMatchesRange operation target) =
      tree.toList.filter (tableRowMatchesRange operation target) := by
  induction valid with
  | leaf rows => rfl
  | branch2 left right separator leftValid rightValid leftAdmitted
      rightAdmitted leftInduction rightInduction =>
      have leftExact :
          ((if tableRangeMayMatch operation none (some separator) target then
              left.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            left.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation none (some separator) target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target left.toList _ allowed (fun row member matched =>
                leftAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using leftInduction
      have rightExact :
          ((if tableRangeMayMatch operation (some separator) none target then
              right.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            right.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation (some separator) none target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target right.toList _ allowed (fun row member matched =>
                rightAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using rightInduction
      simp only [AbstractTableTree.rangeCandidates, AbstractTableTree.toList,
        List.filter_append]
      rw [leftExact, rightExact]
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid leftAdmitted middleAdmitted rightAdmitted
      leftInduction middleInduction rightInduction =>
      have leftExact :
          ((if tableRangeMayMatch operation none (some firstSeparator) target then
              left.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            left.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation none
            (some firstSeparator) target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target left.toList _ allowed (fun row member matched =>
                leftAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using leftInduction
      have middleExact :
          ((if tableRangeMayMatch operation (some firstSeparator)
              (some secondSeparator) target then
              middle.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            middle.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation (some firstSeparator)
            (some secondSeparator) target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target middle.toList _ allowed (fun row member matched =>
                middleAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using middleInduction
      have rightExact :
          ((if tableRangeMayMatch operation (some secondSeparator) none target then
              right.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            right.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation (some secondSeparator) none
            target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target right.toList _ allowed (fun row member matched =>
                rightAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using rightInduction
      simp only [AbstractTableTree.rangeCandidates, AbstractTableTree.toList,
        List.filter_append]
      rw [leftExact, middleExact, rightExact]

theorem table_range_upper_admitted (row : Core.Row) (upper : Core.Integer)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (before : row.rowid.value ≤ upper.value)
    (matched : tableRowMatchesRange operation target row = true) :
    tableRangeMayMatch operation none (some upper) target = true := by
  cases operation <;>
    simp [tableRangeMayMatch, tableRowMatchesRange,
      PhysicalQuery.sqlCompare, PhysicalQuery.Comparison.holds,
      PhysicalQuery.compareValue, Int.compare_eq_lt,
      Int.compare_eq_gt] at matched ⊢
  all_goals omega

theorem table_range_lower_admitted (lower : Core.Integer) (row : Core.Row)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (after : lower.value < row.rowid.value)
    (matched : tableRowMatchesRange operation target row = true) :
    tableRangeMayMatch operation (some lower) none target = true := by
  cases operation <;>
    simp [tableRangeMayMatch, tableRowMatchesRange,
      PhysicalQuery.sqlCompare, PhysicalQuery.Comparison.holds,
      PhysicalQuery.compareValue, Int.compare_eq_lt,
      Int.compare_eq_gt] at matched ⊢
  all_goals omega

theorem table_range_middle_admitted (lower : Core.Integer) (row : Core.Row)
    (upper : Core.Integer) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) (after : lower.value < row.rowid.value)
    (before : row.rowid.value ≤ upper.value)
    (matched : tableRowMatchesRange operation target row = true) :
    tableRangeMayMatch operation (some lower) (some upper) target = true := by
  cases operation with
  | less => exact table_range_lower_admitted lower row .less target after matched
  | lessEqual =>
      exact table_range_lower_admitted lower row .lessEqual target after matched
  | greater =>
      exact table_range_upper_admitted row upper .greater target before matched
  | greaterEqual =>
      exact table_range_upper_admitted row upper .greaterEqual target before
        matched

/-- Decode precisely the binary/ternary table topology produced by the
persistent store. Wider arbitrary SQLite fanout remains on the validating
general-file path. -/
def decodeAbstractTableTreeFrom (schema : Core.Schema) (source : PageSource) :
    Nat → Nat → Option AbstractTableTree
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeTableInterior? page with
      | some ([(leftPage, separator)], rightPage) => do
          let left ← decodeAbstractTableTreeFrom schema source fuel leftPage
          let right ← decodeAbstractTableTreeFrom schema source fuel rightPage
          some (.branch2 left separator right)
      | some ([(leftPage, firstSeparator),
          (middlePage, secondSeparator)], rightPage) => do
          let left ← decodeAbstractTableTreeFrom schema source fuel leftPage
          let middle ← decodeAbstractTableTreeFrom schema source fuel middlePage
          let right ← decodeAbstractTableTreeFrom schema source fuel rightPage
          some (.branch3 left firstSeparator middle secondSeparator right)
      | some _ => none
      | none => .leaf <$> decodeRowsFrom schema source page

/-- Complete table decode using the same interior parser as the directed
reader.  This proof reference avoids silently relating two independent byte
classifiers. -/
def decodeRoutedSubtreeRowsFrom (schema : Core.Schema) (source : PageSource) :
    Nat → Nat → Option (List Core.Row)
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeTableInterior? page with
      | some (entries, rightmost) =>
          let children := entries.map (fun entry => entry.1) ++ [rightmost]
          children.foldlM (fun rows child => do
            let childRows ← decodeRoutedSubtreeRowsFrom schema source fuel child
            some (rows ++ childRows)) []
      | none => decodeRowsFrom schema source page

end CoreDecode

end SQLeanite
