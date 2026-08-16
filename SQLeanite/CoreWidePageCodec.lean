import SQLeanite.CoreWidePageState
import SQLeanite.CorePageCodec

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
  node.toList.getLast?.bind fun entry =>
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

/-- Bulk inline image used to validate the new representation before live
cutover.  Numbered tree pages are ordered by their already-assigned identities;
secondary indexes remain in the established packed index codec and begin
after the wide table allocation interval. -/
def encodeBulkInlineWithState (database : Core.Database) :
    Option (CoreFile.Image × CoreWidePageState.State) := do
  let state ← CoreWidePageState.State.build? database
  let numbered ← encodeTables state.tables
  let ordered := CorePageCodec.orderNumberedPages numbered
  if _numbers : ordered.map CorePageCodec.NumberedPage.pageNumber =
      List.range' 2 (state.nextPage - 2) then
    let indexEncodings ← CoreOverflow.encodeIndexTableGroups
      state.nextPage database.tables
    let entries := state.tables.map tableCatalogEntry ++
      CoreOverflow.indexEntriesOf indexEncodings
    let remaining := ordered.map CorePageCodec.NumberedPage.page ++
      CoreOverflow.indexPagesOf indexEncodings
    let total := 1 + remaining.length
    if countBound : total + 1 < 2 ^ 32 then
      let count : FileFormat.U32Value := ⟨total, by omega⟩
      let schema ← CoreFile.schemaPageForEntries? entries count
      some (⟨database, schema :: remaining⟩, state)
    else none
  else none

def encodeBulkInline (database : Core.Database) : Option CoreFile.Image :=
  (encodeBulkInlineWithState database).map Prod.fst

theorem encodeBulkInlineWithState_represents {database : Core.Database}
    {result : CoreFile.Image × CoreWidePageState.State}
    (encoded : encodeBulkInlineWithState database = some result) :
    result.2.Represents database := by
  unfold encodeBulkInlineWithState at encoded
  rcases Option.bind_eq_some.mp encoded with ⟨state, stateResult, encoded⟩
  rcases Option.bind_eq_some.mp encoded with ⟨numbered, numberedResult, encoded⟩
  dsimp only at encoded
  split at encoded
  next =>
    rcases Option.bind_eq_some.mp encoded with
      ⟨indexEncodings, indexResult, encoded⟩
    split at encoded
    next =>
      rcases Option.bind_eq_some.mp encoded with ⟨schema, schemaResult, encoded⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at encoded
      subst result
      exact CoreWidePageState.State.build?_represents stateResult
    next => contradiction
  next => contradiction

end CoreWidePageCodec
end SQLeanite
