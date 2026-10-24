import SQLeanite.PersistentPageTree

namespace SQLeanite.SingletonPageTree

open RecursiveBPlusTree

/-- The first key of a nonempty child supplies its B+ tree separator. Empty
children are handled by the existing structural validity checker. -/
def firstKey (node : Node α) : Nat :=
  (node.toList.head?).map Prod.fst |>.getD 0

/-- Group equal-height children in twos, with a final three when necessary.
No child is discarded or copied. -/
def pack : List (Node α) → List (Node α)
  | [] => []
  | [a] => [a]
  | [a, b] => [.branch2 a (firstKey b) b]
  | [a, b, c] => [.branch3 a (firstKey b) b (firstKey c) c]
  | a :: b :: c :: d :: rest =>
      .branch2 a (firstKey b) b :: pack (c :: d :: rest)

theorem pack_entries (nodes : List (Node α)) :
    (pack nodes).flatMap Node.toList = nodes.flatMap Node.toList := by
  induction nodes using pack.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 => simp [pack, Node.toList, List.append_assoc]
  | case4 => simp [pack, Node.toList, List.append_assoc]
  | case5 a b c d rest ih =>
      simp only [pack, List.flatMap_cons, Node.toList, ih]
      simp [List.append_assoc]

/-- Every round reduces the forest until a single root remains. The finite
fallback retains all entries; it is never allowed to bypass root validation. -/
def buildFuel : Nat → List (Node α) → Node α
  | 0, nodes => .leaf (nodes.flatMap Node.toList)
  | _ + 1, [] => .leaf []
  | _ + 1, [node] => node
  | fuel + 1, a :: b :: rest => buildFuel fuel (pack (a :: b :: rest))

theorem buildFuel_entries (fuel : Nat) (nodes : List (Node α)) :
    (buildFuel fuel nodes).toList = nodes.flatMap Node.toList := by
  induction fuel generalizing nodes with
  | zero => rfl
  | succ fuel ih =>
      cases nodes with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => simp [buildFuel]
          | cons b rest =>
              rw [buildFuel, ih, pack_entries]

def build (entries : List (PagedBTree.Entry α)) : Node α :=
  buildFuel (entries.length + 1) (entries.map fun entry => .leaf [entry])

theorem build_entries (entries : List (PagedBTree.Entry α)) :
    (build entries).toList = entries := by
  rw [build, buildFuel_entries]
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp [Node.toList, ih]

/-- Large physical cells require a single entry in each leaf. The checked
balanced shape retains the original entries by theorem, then receives fresh
preorder page identities. No SQL values are compared or repaired here. -/
def store (rootPage : Nat) (entries : List (PagedBTree.Entry α)) :
    PersistentPageTree.Store α :=
  let node := build entries
  if valid : node.checkRootValid = true then
    PersistentPageTree.Store.ofTree rootPage node
      ((Node.checkRootValid_iff node).mp valid)
  else PersistentPageTree.Store.build rootPage entries

theorem store_represents (rootPage : Nat) (entries : List (PagedBTree.Entry α))
    (sorted : PagedBTree.KeysStrictlySorted entries) :
    (store rootPage entries).Represents entries := by
  unfold store
  dsimp only
  split
  next valid =>
    exact (PersistentPageTree.Store.ofTree_represents rootPage (build entries) _).trans
      (build_entries entries)
  next invalid => exact PersistentPageTree.Store.build_represents rootPage entries sorted

end SQLeanite.SingletonPageTree
