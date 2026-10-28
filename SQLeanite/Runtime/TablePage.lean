import SQLeanite.FileFormat.DecodeUnsignedFixedEncode
import SQLeanite.Runtime.LowerBound

namespace SQLeanite.Runtime.TablePage

abbrev Key := FileFormat.SignedInteger .eight

structure Entry where
  key : Key
  offset : Nat
  child : Nat

def keyAt (entries : Array Entry) (index : Nat) : Int :=
  ((entries[index]?).map (·.key.value)).getD 0

/-- Like SQLite's initialized MemPage, this view is built once per retained
page. The shared list is a compatibility view for the existing proved codec;
record reads no longer allocate a copy of the rest of the physical page. -/
structure View where
  bytes : ByteArray
  input : List UInt8
  input_eq : input = bytes.toList
  entries : Array Entry
  ordered : CheckedOrder.adjacent (keyAt entries) (entries.size - 1) 0 = true
  leaf : Bool
  rightmost : Nat

def View.lowerBound (view : View) (target : Key) : Nat :=
  LowerBound.search (fun i => decide (target.value ≤ keyAt view.entries i))
    view.entries.size 0 view.entries.size

theorem View.lowerBound_eq_linear (view : View) (target : Key) :
    view.lowerBound target = (List.range view.entries.size).findIdx
      (fun i => decide (target.value ≤ keyAt view.entries i)) := by
  apply LowerBound.search_eq_findIdx
  intro i j ij js hi
  have sorted := CheckedOrder.monotone_of_checked (keyAt view.entries)
    view.entries.size view.ordered i j ij js
  simpa only [decide_eq_true_eq] using
    Int.le_trans (of_decide_eq_true hi) sorted

/-- Any present key is found at the first admissible index. In particular,
binary search cannot turn a present key into a successful empty result. -/
theorem View.lowerBound_present (view : View) (target : Key) (j : Nat)
    (inside : j < view.entries.size) (present : keyAt view.entries j = target.value) :
    view.lowerBound target ≤ j ∧
      keyAt view.entries (view.lowerBound target) = target.value := by
  let p := fun i => decide (target.value ≤ keyAt view.entries i)
  have sorted := CheckedOrder.monotone_of_checked (keyAt view.entries)
    view.entries.size view.ordered
  have mono : ∀ i j, i ≤ j → j < view.entries.size → p i = true → p j = true := by
    intro i j ij js hi
    exact decide_eq_true (Int.le_trans (of_decide_eq_true hi) (sorted i j ij js))
  have part := LowerBound.search_partition p view.entries.size mono
    view.entries.size 0 view.entries.size ⟨by omega, by omega⟩ (by omega)
    (by intro i hi; omega) (by intro i hi hn; omega)
  change 0 ≤ view.lowerBound target ∧ view.lowerBound target ≤ view.entries.size ∧
    (∀ i, i < view.lowerBound target → p i = false) ∧
    (∀ i, view.lowerBound target ≤ i → i < view.entries.size → p i = true) at part
  have le : view.lowerBound target ≤ j := by
    by_cases h : view.lowerBound target ≤ j
    · exact h
    · have no := part.2.2.1 j (by omega)
      simp [p, present] at no
  have lbInside : view.lowerBound target < view.entries.size := by omega
  have above := of_decide_eq_true (part.2.2.2 _ (by omega) lbInside)
  have below := sorted _ j le inside
  exact ⟨le, by omega⟩

def decodeUnsignedAt? (width offset : Nat) (bytes : ByteArray) : Option Nat := do
  if offset + width ≤ bytes.size then
    let window := (bytes.extract offset (offset + width)).toList
    let (value, suffix) ← FileFormat.decodeUnsignedFixed width window
    if suffix = [] then some value else none
  else none

def decodeVarintAt? (offset : Nat) (bytes : ByteArray) :
    Option (FileFormat.U64Value × Nat) := do
  if offset < bytes.size then
    let stop := min bytes.size (offset + 9)
    let window := (bytes.extract offset stop).toList
    let (value, suffix) ← FileFormat.decodeVarint window
    some (value, offset + (window.length - suffix.length))
  else none

private def readEntries (bytes : ByteArray) (leaf : Bool) (headerEnd : Nat) :
    Nat → Nat → Array Entry → Option (Array Entry)
  | 0, _, entries => some entries
  | count + 1, index, entries => do
      let headerSize := if leaf then 8 else 12
      let offset ← decodeUnsignedAt? 2 (headerSize + 2 * index) bytes
      if offset < headerEnd then none else do
        let (child, keyOffset) ← if leaf then do
          let (_, afterSize) ← decodeVarintAt? offset bytes
          some (0, afterSize)
        else do
          let child ← decodeUnsignedAt? 4 offset bytes
          some (child, offset + 4)
        let (keyBits, _) ← decodeVarintAt? keyOffset bytes
        let key := FileFormat.signedIntegerFromUnsigned .eight keyBits
        readEntries bytes leaf headerEnd count (index + 1)
          (entries.push ⟨key, offset, child⟩)

/-- Reject malformed pointers and unordered keys before enabling binary
search. The orderedness proof is carried by the view and erased at runtime. -/
def decode? (bytes : ByteArray) : Option View := do
  let leaf ← if bytes[0]? = some 13 then some true
    else if bytes[0]? = some 5 then some false else none
  let count ← decodeUnsignedAt? 2 3 bytes
  let headerEnd := (if leaf then 8 else 12) + 2 * count
  if headerEnd > bytes.size then none else do
    let rightmost ← if leaf then some 0 else decodeUnsignedAt? 4 8 bytes
    let entries ← readEntries bytes leaf headerEnd count 0 #[]
    if ordered : CheckedOrder.adjacent (keyAt entries) (entries.size - 1) 0 = true then
      some ⟨bytes, bytes.toList, rfl, entries, ordered, leaf, rightmost⟩
    else none

end SQLeanite.Runtime.TablePage
