import SQLeanite.CoreWidePageState
import SQLeanite.CorePageCodec
import SQLeanite.CoreWideIndex

namespace SQLeanite
namespace CoreWidePageCodec

/-!
# SQLite bytes for the high-fanout Core state

There is one topology owner: `CoreWidePageState.TableState.tree`.  This codec
serializes that topology directly; it never flattens cells and asks a second
planner to paginate them.  The first executable slice covers inline table
records.  Overflow rows continue through the established codec until the
overflow allocator is threaded through this traversal.
-/

def maximumChunkRowid? (node : WidePageTree.Node
    CoreWidePageState.Chunk) : Option Nat :=
  node.lastEntry?.bind fun entry =>
    entry.2.getLast?.map fun row => row.rowid.toUnsigned

def interiorCells? (children : List (WidePageTree.Node
    CoreWidePageState.Chunk)) : Option
    (List (Nat × Nat) × WidePageTree.Node CoreWidePageState.Chunk) := do
  let (initial, last) ← WidePageTree.splitLast? children
  let cells ← initial.mapM fun child => do
    let key ← maximumChunkRowid? child
    some (child.rootId, key)
  some (cells, last)

/-- Serialize exactly the pages owned by one wide tree.  Recursive calls use
strictly smaller height fuel; malformed empty branches reject rather than
silently inventing a rightmost child. -/
def encodeChunkNode : Nat → Core.Schema →
    WidePageTree.Node CoreWidePageState.Chunk →
      Option (List CorePageCodec.NumberedPage)
  | 0, _, _ => none
  | _ + 1, schema, .leaf pageId entries => do
      let page ← CorePageCodec.encodeChunkLeaf schema entries
      some [⟨pageId, page⟩]
  | fuel + 1, schema, .branch pageId children => do
      let (cells, rightmost) ← interiorCells? children
      let page ← RecursivePageBTree.interiorPage? cells rightmost.rootId
      let childPages ← children.mapM (encodeChunkNode fuel schema)
      some (⟨pageId, page⟩ :: childPages.flatten)

def encodeTable (state : CoreWidePageState.TableState) :
    Option (List CorePageCodec.NumberedPage) :=
  encodeChunkNode (state.tree.root.height + 1) state.table.schema
    state.tree.root

/-- Encode one identified node without descending into its children. -/
def encodeChunkRoot (schema : Core.Schema) :
    WidePageTree.Node CoreWidePageState.Chunk →
      Option CorePageCodec.NumberedPage
  | .leaf pageId entries => do
      let page ← CorePageCodec.encodeChunkLeaf schema entries
      some ⟨pageId, page⟩
  | .branch pageId children => do
      let (cells, rightmost) ← interiorCells? children
      let page ← RecursivePageBTree.interiorPage? cells rightmost.rootId
      some ⟨pageId, page⟩

theorem encodeChunkRoot_pageNumber {schema : Core.Schema}
    {node : WidePageTree.Node CoreWidePageState.Chunk}
    {page : CorePageCodec.NumberedPage}
    (success : encodeChunkRoot schema node = some page) :
    page.pageNumber = node.rootId := by
  cases node with
  | leaf pageId entries =>
      simp only [encodeChunkRoot] at success
      rcases Option.bind_eq_some.mp success with ⟨built, _, success⟩
      exact congrArg CorePageCodec.NumberedPage.pageNumber
        (Option.some.inj success).symm
  | branch pageId children =>
      simp only [encodeChunkRoot] at success
      rcases Option.bind_eq_some.mp success with ⟨parts, _, success⟩
      rcases parts with ⟨cells, rightmost⟩
      rcases Option.bind_eq_some.mp success with ⟨built, _, success⟩
      exact congrArg CorePageCodec.NumberedPage.pageNumber
        (Option.some.inj success).symm

def rightSpineStep : Nat → WidePageTree.Node CoreWidePageState.Chunk →
    List (WidePageTree.Node CoreWidePageState.Chunk)
  | 0, _ => []
  | _ + 1, node@(.leaf _ _) => [node]
  | fuel + 1, node@(.branch _ children) =>
      node :: match children.getLast? with
        | none => []
        | some last => rightSpineStep fuel last

def rightSpine (node : WidePageTree.Node CoreWidePageState.Chunk) :
    List (WidePageTree.Node CoreWidePageState.Chunk) :=
  rightSpineStep (node.height + 1) node

def rightSpineIds (node : WidePageTree.Node CoreWidePageState.Chunk) :
    List Nat := (rightSpine node).map WidePageTree.Node.rootId

/-- Nodes changed by terminal append.  Existing nodes are selected precisely
when they belonged to the old right spine; every freshly allocated node is
selected by its allocator watermark.  At most one interior page's child list
is inspected per selected level, so this is independent of table size. -/
def appendChangedNodesStep (oldRightIds : List Nat) (firstFresh : Nat) :
    Nat → WidePageTree.Node CoreWidePageState.Chunk →
      List (WidePageTree.Node CoreWidePageState.Chunk)
  | 0, _ => []
  | _ + 1, node@(.leaf _ _) => [node]
  | fuel + 1, node@(.branch _ children) =>
      node :: children.flatMap fun child =>
        if oldRightIds.contains child.rootId || firstFresh ≤ child.rootId then
          appendChangedNodesStep oldRightIds firstFresh fuel child
        else []

def appendChangedNodes (oldRightIds : List Nat) (firstFresh : Nat)
    (node : WidePageTree.Node CoreWidePageState.Chunk) :
    List (WidePageTree.Node CoreWidePageState.Chunk) :=
  appendChangedNodesStep oldRightIds firstFresh (node.height + 1) node

def encodeNodes (schema : Core.Schema)
    (nodes : List (WidePageTree.Node CoreWidePageState.Chunk)) :
    Option (List CorePageCodec.NumberedPage) :=
  nodes.mapM (encodeChunkRoot schema)

def encodeTerminalReplacement (schema : Core.Schema)
    (after : WidePageTree.Store CoreWidePageState.Chunk) :
    Option (List CorePageCodec.NumberedPage) :=
  encodeNodes schema (rightSpine after.root)

def encodeTerminalAppend (schema : Core.Schema)
    (before after : WidePageTree.Store CoreWidePageState.Chunk) :
    Option (List CorePageCodec.NumberedPage) :=
  encodeNodes schema
    (appendChangedNodes (rightSpineIds before.root) before.nextPage after.root)

def tableCatalogEntry (state : CoreWidePageState.TableState) :
    CoreFile.CatalogEntry := {
  kind := "table"
  name := state.table.schema.name
  table := state.table.schema.name
  rootPage := state.rootPage
  sql := CoreFile.tableSQL state.table.schema }

def encodeTables (tables : List CoreWidePageState.TableState) :
    Option (List CorePageCodec.NumberedPage) := do
  let pages ← tables.mapM encodeTable
  some pages.flatten

/-- SQLite reserves its pending-byte lock page inside the ordinary page-number
space.  It is intentionally materialized as an all-zero page in a bulk image:
the topology allocator proves that no logical page owns the number, while the
placeholder keeps the file image and database-header page count contiguous. -/
def pendingBytePlaceholder : CorePageCodec.NumberedPage := {
  pageNumber := WidePageTree.pendingBytePage
  page := {
    bytes := List.replicate PhysicalCodec.pageSize 0
    length_eq := by simp } }

def includePendingBytePlaceholder (nextPage : Nat)
    (pages : List CorePageCodec.NumberedPage) :
    List CorePageCodec.NumberedPage :=
  if WidePageTree.pendingBytePage < nextPage then
    pendingBytePlaceholder :: pages
  else pages

@[simp] theorem pendingBytePlaceholder_pageNumber :
    pendingBytePlaceholder.pageNumber = WidePageTree.pendingBytePage := rfl

/-- Executable, linear check for the first high-fanout codec slice.  Keeping
this as a Boolean fold avoids constructing a quadratic membership decider for
the logically equivalent nested universal proposition. -/
def tableRowsInline (state : CoreWidePageState.TableState) : Bool :=
  state.table.rows.all fun row => decide
    (CoreOverflow.RowInline state.table.schema row)

def rowsInline (tables : List CoreWidePageState.TableState) : Bool :=
  tables.all tableRowsInline

theorem rowsInline_spec {tables : List CoreWidePageState.TableState}
    (success : rowsInline tables = true) :
    ∀ state ∈ tables, ∀ row ∈ state.table.rows,
      CoreOverflow.RowInline state.table.schema row := by
  intro state stateMember row rowMember
  have tableTrue : tableRowsInline state = true :=
    (List.all_eq_true.mp success) state stateMember
  have rowTrue : decide (CoreOverflow.RowInline state.table.schema row) =
      true := (List.all_eq_true.mp tableTrue) row rowMember
  exact of_decide_eq_true rowTrue

/-- Bulk inline image used to validate the new representation before live
cutover.  Numbered tree pages are ordered by their already-assigned identities;
secondary indexes remain in the established packed index codec and begin
after the wide table allocation interval. -/
def encodeBulkInlineWithState (database : Core.Database) :
    Option (CoreFile.Image × CoreWidePageState.State) := do
  let state ← CoreWidePageState.State.build? database
  if _inline : rowsInline state.tables then
    let numbered ← encodeTables state.tables
    let ordered := CorePageCodec.orderNumberedPages
      (includePendingBytePlaceholder state.nextPage numbered)
    if _numbers : ordered.map CorePageCodec.NumberedPage.pageNumber =
        List.range' 2 (state.nextPage - 2) then
      let indexEncodings ← CoreWideIndex.encodeIndexTableGroups
        state.nextPage database.tables
      let entries := state.tables.map tableCatalogEntry ++
        CoreWideIndex.indexEntriesOf indexEncodings
      let remaining := ordered.map CorePageCodec.NumberedPage.page ++
        CoreWideIndex.indexPagesOf indexEncodings
      let total := 1 + remaining.length
      if countBound : total + 1 < 2 ^ 32 then
        let count : FileFormat.U32Value := ⟨total, by omega⟩
        let schema ← CoreFile.schemaPageForEntries? entries count
        some (⟨database, schema :: remaining⟩, state)
      else none
    else none
  else none

def encodeBulkInline (database : Core.Database) : Option CoreFile.Image :=
  (encodeBulkInlineWithState database).map Prod.fst

theorem encodeBulkInlineWithState_image {database : Core.Database}
    {result : CoreFile.Image × CoreWidePageState.State}
    (encoded : encodeBulkInlineWithState database = some result) :
    encodeBulkInline database = some result.1 := by
  unfold encodeBulkInline
  rw [encoded]
  rfl

theorem encodeBulkInlineWithState_represents {database : Core.Database}
    {result : CoreFile.Image × CoreWidePageState.State}
    (encoded : encodeBulkInlineWithState database = some result) :
    result.2.Represents database := by
  unfold encodeBulkInlineWithState at encoded
  rcases Option.bind_eq_some.mp encoded with ⟨state, stateResult, encoded⟩
  split at encoded
  next =>
    rcases Option.bind_eq_some.mp encoded with
      ⟨numbered, numberedResult, encoded⟩
    dsimp only at encoded
    split at encoded
    next =>
      rcases Option.bind_eq_some.mp encoded with
        ⟨indexEncodings, indexResult, encoded⟩
      split at encoded
      next =>
        rcases Option.bind_eq_some.mp encoded with
          ⟨schema, schemaResult, encoded⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at encoded
        subst result
        exact CoreWidePageState.State.build?_represents stateResult
      next => contradiction
    next => contradiction
  next => contradiction

end CoreWidePageCodec
end SQLeanite
