import SQLeanite.Runtime.ReadPager
import SQLeanite.Runtime.TablePage

namespace SQLeanite.Runtime.TableCursor

abbrev Key := TablePage.Key

/-- A cell points into shared page storage; record decoding remains a
separate operation. The list view shares its tail instead of copying bytes. -/
structure Cell where
  pageNumber : Nat
  bytes : ByteArray
  offset : Nat
  key : Key
  input : List UInt8
  input_eq : input = bytes.toList.drop offset

structure Cursor where
  pager : ReadPager.Pager
  rootPage : Nat
  position : IO.Ref (Option (Key × Nat × Option Cell))
  views : IO.Ref (Std.HashMap Nat TablePage.View)

/-- An executor shares one view cache across all table cursors in the read
batch, so the memory bound does not multiply by the number of open tables. -/
def create (pager : ReadPager.Pager) (rootPage : Nat)
    (sharedViews : Option (IO.Ref (Std.HashMap Nat TablePage.View)) := none) : IO Cursor := do
  let views ← match sharedViews with
    | some shared => pure shared
    | none => IO.mkRef {}
  return ⟨pager, rootPage, ← IO.mkRef none, views⟩

private def pageView (cursor : Cursor) (pageNumber : Nat) :
    IO (Option TablePage.View) := do
  let views ← cursor.views.get
  if let some view := views.get? pageNumber then return some view
  let some page ← cursor.pager.get pageNumber | return none
  let some view := TablePage.decode? page | return none
  if views.size < cursor.pager.capacity then
    cursor.views.set (views.insert pageNumber view)
  return some view

/-- Route with the checked page's binary lower bound, exactly as the table
cursor in SQLite chooses a separator/leaf position. A corrupt or unordered
page is an optimization miss, never evidence that a requested row is absent. -/
private def locate (cursor : Cursor) (target : Key) :
    Nat → Nat → IO (Option (Option Cell))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some view ← pageView cursor pageNumber | return none
      let index := view.lowerBound target
      if view.leaf then
        let some entry := view.entries[index]? | return some none
        unless entry.key = target do return some none
        let cell : Cell := {
          pageNumber, bytes := view.bytes, offset := entry.offset, key := entry.key
          input := view.input.drop entry.offset
          input_eq := by rw [view.input_eq] }
        return some (some cell)
      else
        let child := match view.entries[index]? with
          | some entry => entry.child
          | none => view.rightmost
        locate cursor target fuel child

/-- Repeated seeks to the same key reuse the current cursor position. Both
hits and valid misses may be retained, but malformed-page results are not. -/
def Cursor.seek (cursor : Cursor) (target : Key) (fuel : Nat) :
    IO (Option (Option Cell)) := do
  if fuel = 0 then return none
  if let some (key, cachedFuel, cell) ← cursor.position.get then
    if key = target && cachedFuel = fuel then return some cell
  let result ← locate cursor target fuel cursor.rootPage
  if let some cell := result then cursor.position.set (some (target, fuel, cell))
  return result

end SQLeanite.Runtime.TableCursor
