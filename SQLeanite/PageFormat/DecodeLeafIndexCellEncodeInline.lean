import SQLeanite.PageFormat.SignedInteger64Bits

namespace SQLeanite
namespace FileFormat

theorem decodeLeafIndexCell_encode_inline {usable : UsablePageSize}
    (payloadSize : U64Value) (bytes : List UInt8)
    (wellFormed : (BTreePayloadData.inline bytes).IndexWellFormed
      usable payloadSize.val) (suffix : List UInt8) :
    let payload : IndexPayload usable payloadSize.val := ⟨.inline bytes, wellFormed⟩
    let cell : LeafIndexCell usable := ⟨payloadSize, payload⟩
    decodeLeafIndexCell usable (cell.encode ++ suffix) = some (cell, suffix) := by
  dsimp only
  unfold LeafIndexCell.encode decodeLeafIndexCell
  rw [List.append_assoc, decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeIndexPayload_encode_inline]

structure InteriorIndexCell (usable : UsablePageSize) where
  leftChildPage : PageNumber
  payloadSize : U64Value
  payload : IndexPayload usable payloadSize.val
  deriving DecidableEq

def InteriorIndexCell.encode {usable : UsablePageSize}
    (cell : InteriorIndexCell usable) : List UInt8 :=
  cell.leftChildPage.encode ++ encodeVarint cell.payloadSize ++ cell.payload.encode

def decodeInteriorIndexCell (usable : UsablePageSize) (input : List UInt8) :
    Option (InteriorIndexCell usable × List UInt8) := do
  let (leftChildPage, afterChild) ← decodePageNumber input
  let (payloadSize, afterSize) ← decodeVarint afterChild
  let (payload, suffix) ← decodeIndexPayload usable payloadSize.val afterSize
  some (⟨leftChildPage, payloadSize, payload⟩, suffix)

theorem InteriorIndexCell.encode_length {usable : UsablePageSize}
    (cell : InteriorIndexCell usable) :
    cell.encode.length = 4 + sqliteVarintSize cell.payloadSize.val +
      cell.payload.encode.length := by
  simp [InteriorIndexCell.encode, PageNumber.encode, encodeU32Bytes,
    encodeVarint_length]
  omega

theorem decodeInteriorIndexCell_encode_inline {usable : UsablePageSize}
    (leftChildPage : PageNumber) (payloadSize : U64Value) (bytes : List UInt8)
    (wellFormed : (BTreePayloadData.inline bytes).IndexWellFormed
      usable payloadSize.val) (suffix : List UInt8) :
    let payload : IndexPayload usable payloadSize.val := ⟨.inline bytes, wellFormed⟩
    let cell : InteriorIndexCell usable :=
      ⟨leftChildPage, payloadSize, payload⟩
    decodeInteriorIndexCell usable (cell.encode ++ suffix) =
      some (cell, suffix) := by
  dsimp only
  unfold InteriorIndexCell.encode decodeInteriorIndexCell
  simp only [List.append_assoc]
  rw [decodePageNumber_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeIndexPayload_encode_inline]

/-- The first word of an overflow page is either zero, terminating the chain,
or a positive 32-bit database page number. -/
inductive OverflowNext where
  | endOfChain
  | page (number : PageNumber)
  deriving Repr, DecidableEq

def OverflowNext.encode : OverflowNext → List UInt8
  | .endOfChain => encodeU32Bytes ⟨0, by omega⟩
  | .page number => number.encode

def decodeOverflowNext (input : List UInt8) :
    Option (OverflowNext × List UInt8) := do
  let (value, suffix) ← decodeU32Bytes input
  if zero : value.val = 0 then
    some (.endOfChain, suffix)
  else
    have positive : 0 < value.val := Nat.pos_of_ne_zero zero
    some (.page ⟨value, positive⟩, suffix)

theorem decodeOverflowNext_encode (next : OverflowNext) (suffix : List UInt8) :
    decodeOverflowNext (next.encode ++ suffix) = some (next, suffix) := by
  cases next with
  | endOfChain =>
      unfold OverflowNext.encode decodeOverflowNext
      rw [decodeU32Bytes_encode]
      simp
  | page number =>
      unfold OverflowNext.encode decodeOverflowNext PageNumber.encode
      rw [decodeU32Bytes_encode]
      simp only [bind, Option.bind]
      rw [dif_neg (Nat.ne_of_gt number.positive)]

theorem OverflowNext.encode_length (next : OverflowNext) :
    next.encode.length = 4 := by
  cases next <;> simp [OverflowNext.encode, PageNumber.encode, encodeU32Bytes]

/-- A raw SQLite overflow page over its usable bytes. The final page's unused
payload tail is retained physically; a higher-level chain supplies the logical
payload length. -/
structure OverflowPage (usable : UsablePageSize) where
  next : OverflowNext
  payload : SizedBytes (overflowPayloadCapacity usable)
  deriving DecidableEq

def OverflowPage.encode {usable : UsablePageSize}
    (page : OverflowPage usable) : List UInt8 :=
  page.next.encode ++ page.payload.bytes

def decodeOverflowPage (usable : UsablePageSize) (input : List UInt8) :
    Option (OverflowPage usable × List UInt8) := do
  let (next, afterNext) ← decodeOverflowNext input
  let (payload, suffix) ←
    decodeSizedBytes (overflowPayloadCapacity usable) afterNext
  some (⟨next, payload⟩, suffix)

theorem decodeOverflowPage_encode {usable : UsablePageSize}
    (page : OverflowPage usable) (suffix : List UInt8) :
    decodeOverflowPage usable (page.encode ++ suffix) = some (page, suffix) := by
  unfold OverflowPage.encode decodeOverflowPage
  rw [List.append_assoc, decodeOverflowNext_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeSizedBytes_append]

theorem OverflowPage.encode_length {usable : UsablePageSize}
    (page : OverflowPage usable) :
    page.encode.length = usable.val := by
  simp [OverflowPage.encode, page.next.encode_length, page.payload.length_eq,
    overflowPayloadCapacity]
  have minimum := usable.atLeastMinimum
  omega

/-- Logical overflow-chain data. Every non-final page contributes its complete
payload capacity; the final page records how many of its physical payload bytes
belong to the logical record. -/
inductive OverflowChainData (usable : UsablePageSize) where
  | last (number : PageNumber)
      (payload : SizedBytes (overflowPayloadCapacity usable))
      (used : Nat) (used_le : used ≤ overflowPayloadCapacity usable)
  | link (number : PageNumber)
      (payload : SizedBytes (overflowPayloadCapacity usable))
      (tail : OverflowChainData usable)
  deriving DecidableEq

def OverflowChainData.firstPage {usable : UsablePageSize} :
    OverflowChainData usable → PageNumber
  | .last number _ _ _ | .link number _ _ => number

def OverflowChainData.pageNumbers {usable : UsablePageSize} :
    OverflowChainData usable → List PageNumber
  | .last number _ _ _ => [number]
  | .link number _ tail => number :: tail.pageNumbers

def OverflowChainData.pageCount {usable : UsablePageSize} :
    OverflowChainData usable → Nat
  | .last _ _ _ _ => 1
  | .link _ _ tail => tail.pageCount + 1

/-- Reconstruct the physical pages, deriving every next pointer from the
following page rather than trusting separately supplied linkage metadata. -/
def OverflowChainData.toPages {usable : UsablePageSize} :
    OverflowChainData usable → List (PageNumber × OverflowPage usable)
  | .last number payload _ _ => [(number, ⟨.endOfChain, payload⟩)]
  | .link number payload tail =>
    (number, ⟨.page tail.firstPage, payload⟩) :: tail.toPages

def OverflowChainData.logicalPayload {usable : UsablePageSize} :
    OverflowChainData usable → List UInt8
  | .last _ payload used _ => payload.bytes.take used
  | .link _ payload tail => payload.bytes ++ tail.logicalPayload

def OverflowChainData.logicalPayloadSize {usable : UsablePageSize} :
    OverflowChainData usable → Nat
  | .last _ _ used _ => used
  | .link _ _ tail => overflowPayloadCapacity usable + tail.logicalPayloadSize

/-- Adjacent physical overflow pages point to one another and the last page
uses the zero end-of-chain sentinel. -/
def OverflowPagesLinked {usable : UsablePageSize} :
    List (PageNumber × OverflowPage usable) → Prop
  | [] => False
  | [(_, page)] => page.next = .endOfChain
  | (_, page) :: (nextNumber, nextPage) :: tail =>
    page.next = .page nextNumber ∧
      OverflowPagesLinked ((nextNumber, nextPage) :: tail)

theorem OverflowChainData.pageCount_pos {usable : UsablePageSize}
    (chain : OverflowChainData usable) : 0 < chain.pageCount := by
  cases chain <;> simp [OverflowChainData.pageCount]

theorem OverflowChainData.toPages_length {usable : UsablePageSize}
    (chain : OverflowChainData usable) :
    chain.toPages.length = chain.pageCount := by
  induction chain with
  | last => rfl
  | link number payload tail induction =>
      simp [OverflowChainData.toPages, OverflowChainData.pageCount, induction]

theorem OverflowChainData.toPages_pageNumbers {usable : UsablePageSize}
    (chain : OverflowChainData usable) :
    chain.toPages.map Prod.fst = chain.pageNumbers := by
  induction chain with
  | last => rfl
  | link number payload tail induction =>
      simp [OverflowChainData.toPages, OverflowChainData.pageNumbers, induction]

theorem OverflowChainData.logicalPayload_length {usable : UsablePageSize}
    (chain : OverflowChainData usable) :
    chain.logicalPayload.length = chain.logicalPayloadSize := by
  induction chain with
  | last number payload used used_le =>
      simp [OverflowChainData.logicalPayload,
        OverflowChainData.logicalPayloadSize, payload.length_eq, used_le]
  | link number payload tail induction =>
      simp [OverflowChainData.logicalPayload,
        OverflowChainData.logicalPayloadSize, payload.length_eq, induction]

theorem OverflowChainData.toPages_linked {usable : UsablePageSize}
    (chain : OverflowChainData usable) : OverflowPagesLinked chain.toPages := by
  induction chain with
  | last => rfl
  | link number payload tail induction =>
      cases tail <;>
        simp [OverflowChainData.toPages, OverflowChainData.firstPage,
          OverflowPagesLinked] at induction ⊢ <;>
        assumption

/-- An overflow chain with no repeated page number. Together with `toPages`,
this excludes cycles and makes all linkage correct by construction. -/
structure OverflowChain (usable : UsablePageSize) where
  data : OverflowChainData usable
  acyclic : data.pageNumbers.Nodup
  deriving DecidableEq

def OverflowChain.firstPage {usable : UsablePageSize}
    (chain : OverflowChain usable) : PageNumber := chain.data.firstPage

def OverflowChain.toPages {usable : UsablePageSize}
    (chain : OverflowChain usable) : List (PageNumber × OverflowPage usable) :=
  chain.data.toPages

def OverflowChain.logicalPayload {usable : UsablePageSize}
    (chain : OverflowChain usable) : List UInt8 := chain.data.logicalPayload

theorem OverflowChain.pageNumbers_nodup {usable : UsablePageSize}
    (chain : OverflowChain usable) : chain.data.pageNumbers.Nodup :=
  chain.acyclic

theorem OverflowChain.pages_linked {usable : UsablePageSize}
    (chain : OverflowChain usable) : OverflowPagesLinked chain.toPages :=
  chain.data.toPages_linked

theorem OverflowChain.toPages_nonempty {usable : UsablePageSize}
    (chain : OverflowChain usable) : chain.toPages ≠ [] := by
  intro empty
  have lengthPositive := chain.data.pageCount_pos
  have lengthEquality := chain.data.toPages_length
  unfold OverflowChain.toPages at empty
  rw [empty] at lengthEquality
  simp at lengthEquality
  omega

theorem OverflowChain.logicalPayload_length {usable : UsablePageSize}
    (chain : OverflowChain usable) :
    chain.logicalPayload.length = chain.data.logicalPayloadSize :=
  chain.data.logicalPayload_length

/-- Connect a table leaf cell to its overflow storage. Inline cells must have
no chain. Overflowing cells must point at the chain's first page, and local plus
overflow bytes must equal the payload size announced by the cell. -/
def TableLeafCell.ChainResolved {usable : UsablePageSize}
    (cell : TableLeafCell usable) (chain : Option (OverflowChain usable)) : Prop :=
  match cell.payload.data, chain with
  | .inline _, none => True
  | .overflow localBytes firstOverflowPage, some chain =>
    chain.firstPage = firstOverflowPage ∧
      localBytes.length + chain.logicalPayload.length = cell.payloadSize.val
  | _, _ => False

instance {usable : UsablePageSize} (cell : TableLeafCell usable)
    (chain : Option (OverflowChain usable)) :
    Decidable (cell.ChainResolved chain) := by
  unfold TableLeafCell.ChainResolved
  split <;> infer_instance

structure ResolvedTableLeafCell (usable : UsablePageSize) where
  cell : TableLeafCell usable
  chain : Option (OverflowChain usable)
  resolved : cell.ChainResolved chain
  deriving DecidableEq

def ResolvedTableLeafCell.logicalPayload {usable : UsablePageSize}
    (resolvedCell : ResolvedTableLeafCell usable) : List UInt8 :=
  match resolvedCell.cell.payload.data, resolvedCell.chain with
  | .inline bytes, none => bytes
  | .overflow localBytes _, some chain => localBytes ++ chain.logicalPayload
  | _, _ => []

theorem ResolvedTableLeafCell.logicalPayload_length {usable : UsablePageSize}
    (resolvedCell : ResolvedTableLeafCell usable) :
    resolvedCell.logicalPayload.length = resolvedCell.cell.payloadSize.val := by
  rcases resolvedCell with ⟨cell, chain, resolved⟩
  rcases cell with ⟨payloadSize, rowid, payload⟩
  rcases payload with ⟨data, payloadWellFormed⟩
  cases data <;> cases chain <;>
    simp [ResolvedTableLeafCell.logicalPayload,
      TableLeafCell.ChainResolved] at resolved ⊢
  · exact payloadWellFormed.2
  · omega

/-- A physical cell byte interval placed within one database page. -/
structure PlacedCell (pageSize : Nat) where
  offset : U16Value
  bytes : List UInt8
  nonempty : bytes ≠ []
  endWithinPage : offset.val + bytes.length ≤ pageSize
  deriving DecidableEq

def PlacedCell.endOffset {pageSize : Nat} (cell : PlacedCell pageSize) : Nat :=
  cell.offset.val + cell.bytes.length

def PlacedCell.Contains {pageSize : Nat} (cell : PlacedCell pageSize)
    (byteOffset : Nat) : Prop :=
  cell.offset.val ≤ byteOffset ∧ byteOffset < cell.endOffset

instance {pageSize : Nat} (cell : PlacedCell pageSize) (byteOffset : Nat) :
    Decidable (cell.Contains byteOffset) := by
  unfold PlacedCell.Contains PlacedCell.endOffset
  infer_instance

def PlacedCell.Disjoint {pageSize : Nat}
    (left right : PlacedCell pageSize) : Prop :=
  left.endOffset ≤ right.offset.val ∨ right.endOffset ≤ left.offset.val

instance {pageSize : Nat} (left right : PlacedCell pageSize) :
    Decidable (left.Disjoint right) := by
  unfold PlacedCell.Disjoint PlacedCell.endOffset
  infer_instance

theorem PlacedCell.Disjoint.symm {pageSize : Nat}
    {left right : PlacedCell pageSize} (disjoint : left.Disjoint right) :
    right.Disjoint left := by
  unfold PlacedCell.Disjoint at disjoint ⊢
  exact disjoint.elim Or.inr Or.inl

theorem PlacedCell.Disjoint.not_both_contains {pageSize byteOffset : Nat}
    {left right : PlacedCell pageSize} (disjoint : left.Disjoint right) :
    ¬(left.Contains byteOffset ∧ right.Contains byteOffset) := by
  unfold PlacedCell.Disjoint PlacedCell.endOffset at disjoint
  unfold PlacedCell.Contains PlacedCell.endOffset
  omega

/-- A page prefix connected to concrete cell intervals. Pointer agreement
ensures every encoded pointer selects the corresponding cell; the remaining
fields exclude prefix overlap and cell-to-cell overlap. -/
structure BTreeCellLayout (pageSize : Nat) where
  pagePrefix : BTreePagePrefix pageSize
  cells : List (PlacedCell pageSize)
  pointerAgreement : cells.map (fun cell => cell.offset) = pagePrefix.pointers.values
  afterPrefix : ∀ cell ∈ cells, pagePrefix.encode.length ≤ cell.offset.val
  pairwiseDisjoint : cells.Pairwise PlacedCell.Disjoint
  deriving DecidableEq

theorem BTreeCellLayout.cellCount_eq {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) :
    layout.cells.length = layout.pagePrefix.header.header.common.cellCount.val := by
  have lengths := congrArg List.length layout.pointerAgreement
  simpa [layout.pagePrefix.pointers.length_eq] using lengths

theorem BTreeCellLayout.every_cell_within_page {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (cell : PlacedCell pageSize)
    (_member : cell ∈ layout.cells) : cell.endOffset ≤ pageSize := by
  exact cell.endWithinPage

theorem BTreeCellLayout.every_cell_after_prefix {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (cell : PlacedCell pageSize)
    (member : cell ∈ layout.cells) :
    layout.pagePrefix.encode.length ≤ cell.offset.val :=
  layout.afterPrefix cell member

def cellByteAt? {pageSize : Nat} :
    List (PlacedCell pageSize) → Nat → Option UInt8
  | [], _ => none
  | cell :: cells, byteOffset =>
    if cell.Contains byteOffset then
      cell.bytes[byteOffset - cell.offset.val]?
    else
      cellByteAt? cells byteOffset

theorem PlacedCell.Contains.relative_lt {pageSize byteOffset : Nat}
    {cell : PlacedCell pageSize} (contains : cell.Contains byteOffset) :
    byteOffset - cell.offset.val < cell.bytes.length := by
  unfold PlacedCell.Contains PlacedCell.endOffset at contains
  omega

private theorem cellByteAt?_eq_of_mem {pageSize byteOffset : Nat}
    {cells : List (PlacedCell pageSize)} (pairwise : cells.Pairwise PlacedCell.Disjoint)
    {cell : PlacedCell pageSize} (member : cell ∈ cells)
    (contains : cell.Contains byteOffset) :
    cellByteAt? cells byteOffset =
      some (cell.bytes.get
        ⟨byteOffset - cell.offset.val, contains.relative_lt⟩) := by
  induction cells with
  | nil => simp at member
  | cons head tail induction =>
      have headRelations := (List.pairwise_cons.mp pairwise).1
      have tailPairwise := (List.pairwise_cons.mp pairwise).2
      rcases List.mem_cons.mp member with same | inTail
      · subst head
        unfold cellByteAt?
        rw [if_pos contains]
        simp [getElem?_def, contains.relative_lt]
      · have disjoint := headRelations cell inTail
        have headDoesNotContain : ¬ head.Contains byteOffset := by
          intro headContains
          exact disjoint.not_both_contains ⟨headContains, contains⟩
        unfold cellByteAt?
        rw [if_neg headDoesNotContain]
        exact induction tailPairwise inTail

def BTreeCellLayout.byteAt {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (byteOffset : Nat) : UInt8 :=
  match layout.pagePrefix.encode[byteOffset]? with
  | some byte => byte
  | none => (cellByteAt? layout.cells byteOffset).getD 0

/-- Materialize a validated layout as an exact-size storage page. Bytes not
occupied by the prefix or a cell are deterministically zero-filled. -/
def BTreeCellLayout.encodePage {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) : Storage.Page pageSize := {
  bytes := Array.ofFn (fun offset : Fin pageSize => layout.byteAt offset.val)
  sizeInvariant := by simp }

theorem BTreeCellLayout.encodePage_size {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) :
    layout.encodePage.bytes.size = pageSize :=
  layout.encodePage.sizeInvariant

theorem BTreeCellLayout.byteAt_prefix {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (byteOffset : Nat)
    (withinPrefix : byteOffset < layout.pagePrefix.encode.length) :
    layout.byteAt byteOffset =
      layout.pagePrefix.encode.get ⟨byteOffset, withinPrefix⟩ := by
  unfold BTreeCellLayout.byteAt
  simp [getElem?_def, withinPrefix]

theorem BTreeCellLayout.byteAt_cell {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (cell : PlacedCell pageSize)
    (member : cell ∈ layout.cells) (byteOffset : Nat)
    (contains : cell.Contains byteOffset) :
    layout.byteAt byteOffset =
      cell.bytes.get ⟨byteOffset - cell.offset.val, contains.relative_lt⟩ := by
  have prefixBeforeCell := layout.afterPrefix cell member
  have prefixBeforeOffset : layout.pagePrefix.encode.length ≤ byteOffset := by
    exact Nat.le_trans prefixBeforeCell contains.1
  unfold BTreeCellLayout.byteAt
  simp only [getElem?_def, Nat.not_lt_of_ge prefixBeforeOffset, ↓reduceDIte]
  rw [cellByteAt?_eq_of_mem layout.pairwiseDisjoint member contains]
  rfl

inductive BTreeCellBody (usable : UsablePageSize) where
  | interiorTable (cell : InteriorTableCell)
  | leafTable (cell : TableLeafCell usable)
  | interiorIndex (cell : InteriorIndexCell usable)
  | leafIndex (cell : LeafIndexCell usable)
  deriving DecidableEq

end FileFormat

end SQLeanite
