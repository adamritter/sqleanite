import SQLeanite.CoreFile.IntegerIndexRowLeTrans

namespace SQLeanite
namespace CoreFile
attribute [local instance] lexOrd
open FileFormat

theorem encodeIndexTableGroups_canonicalize : ∀ (nextPage : Nat)
    (tables : List Core.Table),
    encodeIndexTableGroups nextPage (tables.map Core.Table.canonicalize) =
      (encodeIndexTableGroups nextPage tables).map
        (List.map IndexEncoding.canonicalize)
  | _, [] => rfl
  | nextPage, table :: tables => by
      simp only [List.map_cons, encodeIndexTableGroups,
        Core.Table.canonicalize_indexes]
      rw [encodeIndexes_canonicalize]
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => rfl
      | some current =>
          rw [show Option.map (List.map IndexEncoding.canonicalize)
              (some current) =
                some (current.map IndexEncoding.canonicalize) by rfl]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [indexEndPage_canonicalize, encodeIndexTableGroups_canonicalize]
          cases remainingResult : encodeIndexTableGroups
              (indexEndPage nextPage current) tables with
          | none => rfl
          | some remaining => simp

@[simp] theorem indexPagesOf_canonicalize
    (encodings : List IndexEncoding) :
    indexPagesOf (encodings.map IndexEncoding.canonicalize) =
      indexPagesOf encodings := by
  unfold indexPagesOf
  simp only [List.flatMap, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro encoding member
  rfl

@[simp] theorem indexEntriesOf_canonicalize
    (encodings : List IndexEncoding) :
    indexEntriesOf (encodings.map IndexEncoding.canonicalize) =
      indexEntriesOf encodings := by
  simp [indexEntriesOf, List.map_map, Function.comp_def]

theorem tableEntriesFor_canonicalize : ∀ (tables : List Core.Table)
    (layouts : List TableLayout),
    tableEntriesFor (tables.map Core.Table.canonicalize) layouts =
      tableEntriesFor tables layouts
  | [], _ => rfl
  | _ :: _, [] => rfl
  | table :: tables, _ :: layouts => by
      simp only [List.map_cons, tableEntriesFor,
        Core.Table.canonicalize_schema, tableSQL, Core.Table.catalogSQL, Core.Table.canonicalize]
      rw [tableEntriesFor_canonicalize]

theorem tableEntries_canonicalize (database : Core.Database)
    (layouts : List TableLayout) :
    tableEntries database.canonicalize layouts = tableEntries database layouts := by
  unfold tableEntries Core.Database.canonicalize
  exact tableEntriesFor_canonicalize database.tables layouts

theorem encodeIndexes_pairs : ∀ (nextPage : Nat)
    (indexes : List (Core.Table × Core.Index)) (encodings : List IndexEncoding),
    encodeIndexes nextPage indexes = some encodings →
      encodings.map (fun encoding => (encoding.table, encoding.index)) = indexes
  | _, [], encodings, encoded => by
      simp only [encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, indexed :: indexes, encodings, encoded => by
      simp only [encodeIndexes, Option.bind_eq_bind, Option.bind] at encoded
      cases leavesResult : indexLeaves indexed.1 indexed.2 with
      | none => simp [leavesResult] at encoded
      | some leaves =>
        simp only [leavesResult] at encoded
        let layout : IndexLayout := ⟨nextPage, leaves⟩
        cases pagesResult : indexPages? layout.rootPage layout.leaves with
        | none => simp [layout, pagesResult] at encoded
        | some physicalPages =>
          simp only [layout, pagesResult] at encoded
          cases remainingResult : encodeIndexes
              (nextPage + tableFootprint leaves) indexes with
          | none => simp [remainingResult] at encoded
          | some remaining =>
            simp only [remainingResult] at encoded
            injection encoded with equal
            subst encodings
            simp only [List.map_cons, Prod.mk.injEq, true_and]
            simpa using encodeIndexes_pairs
              (nextPage + tableFootprint leaves) indexes remaining
              remainingResult

theorem encodeIndexTableGroups_tables : ∀ (nextPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups nextPage tables = some encodings →
      ∀ encoding ∈ encodings, encoding.table ∈ tables
  | _, [], encodings, encoded => by
      simp only [encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      simp
  | nextPage, table :: tables, encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind] at encoded
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : encodeIndexTableGroups
            (indexEndPage nextPage current) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult] at encoded
          injection encoded with equal
          subst encodings
          intro encoding member
          simp only [List.mem_append] at member
          rcases member with currentMember | remainingMember
          ·
            have aligned := encodeIndexes_pairs nextPage
              (table.indexes.map fun index => (table, index)) current currentResult
            have mapped : (encoding.table, encoding.index) ∈
                current.map (fun candidate => (candidate.table, candidate.index)) :=
              List.mem_map_of_mem currentMember
            rw [aligned] at mapped
            rcases List.mem_map.mp mapped with ⟨index, _, pairEqual⟩
            have tableEqual : encoding.table = table := by
              exact (Prod.mk.inj pairEqual.symm).1
            simp [tableEqual]
          · right
            exact encodeIndexTableGroups_tables
              (indexEndPage nextPage current) tables remaining remainingResult
              encoding remainingMember

structure Image where
  database : Core.Database
  pages : List Page

/-- Number of pages actually emitted. With multi-leaf tables this is no longer
a closed formula over table and index counts, so it is read off the layout. -/
def Image.pageCount (image : Image) : Nat := image.pages.length

def encode (database : Core.Database) : Option Image := do
  let tableEncodings ← encodeTables 2 database.tables
  let layouts := tableLayoutsOf tableEncodings
  let indexEncodings ← encodeIndexTableGroups (indexRootBase layouts)
    database.tables
  let entries := tableEntries database layouts ++ indexEntriesOf indexEncodings
  let remaining := tablePagesOf tableEncodings ++ indexPagesOf indexEncodings
  let total := 1 + remaining.length
  if countFits : total < 2 ^ 32 then
    let count : U32Value := ⟨total, by simpa using countFits⟩
    let schema ← schemaPageForEntries? entries count
    some { database, pages := schema :: remaining }
  else none

/-- Canonicalizing the in-memory persistent tree may change its split shape,
but cannot change a single emitted SQLite page.  This is the serialization
boundary needed when physical topology is intentionally absent from logical
database equivalence. -/
theorem encode_canonicalize_pages (database : Core.Database) :
    (encode database.canonicalize).map (fun image => image.pages) =
      (encode database).map (fun image => image.pages) := by
  unfold encode Core.Database.canonicalize
  simp only
  rw [encodeTables_canonicalize]
  cases tableResult : encodeTables 2 database.tables with
  | none => rfl
  | some tableEncodings =>
      simp only [Option.bind_eq_bind, Option.bind]
      let layouts := tableLayoutsOf tableEncodings
      rw [encodeIndexTableGroups_canonicalize]
      cases indexResult : encodeIndexTableGroups (indexRootBase layouts)
          database.tables with
      | none => rfl
      | some indexEncodings =>
          rw [show Option.map (List.map IndexEncoding.canonicalize)
              (some indexEncodings) =
                some (indexEncodings.map IndexEncoding.canonicalize) by rfl]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [indexEntriesOf_canonicalize, indexPagesOf_canonicalize]
          have entriesEqual := tableEntries_canonicalize database layouts
          unfold Core.Database.canonicalize at entriesEqual
          rw [entriesEqual]
          dsimp only [layouts]
          split
          next =>
            cases schemaResult : schemaPageForEntries?
                (tableEntries database (tableLayoutsOf tableEncodings) ++
                  indexEntriesOf indexEncodings)
                ⟨1 + (tablePagesOf tableEncodings ++
                  indexPagesOf indexEncodings).length, by assumption⟩ <;> rfl
          next => rfl

theorem encode_header {database : Core.Database} {image : Image}
    (encoded : encode database = some image) :
    ∃ (count : U32Value) (schema : Page) (remaining : List Page)
      (body : List UInt8),
      image.pages = schema :: remaining ∧
      image.pageCount = count.val ∧
      schema.bytes = encodeDatabaseHeader (databaseHeader count) ++ body := by
  unfold encode at encoded
  cases tableResult : encodeTables 2 database.tables with
  | none => simp [tableResult] at encoded
  | some tableEncodings =>
    simp only [tableResult, Option.bind_eq_bind, Option.bind] at encoded
    let layouts := tableLayoutsOf tableEncodings
    cases indexResult : encodeIndexTableGroups
        (indexRootBase layouts) database.tables with
    | none => simp [layouts, indexResult] at encoded
    | some indexEncodings =>
      simp only [layouts, indexResult] at encoded
      split at encoded
      next countFits =>
        let remaining := tablePagesOf tableEncodings ++ indexPagesOf indexEncodings
        let count : U32Value :=
          ⟨1 + (tablePagesOf tableEncodings ++
            indexPagesOf indexEncodings).length, countFits⟩
        cases schemaResult : schemaPageForEntries?
            (tableEntries database layouts ++ indexEntriesOf indexEncodings) count with
        | none =>
          simp only [count, layouts] at schemaResult
          rw [schemaResult] at encoded
          contradiction
        | some schema =>
          have headerBuilt := schemaResult
          simp only [count, layouts] at schemaResult
          rw [schemaResult] at encoded
          simp only [Option.bind_eq_bind, Option.bind] at encoded
          injection encoded with equal
          subst image
          rcases schemaPageForEntries_header headerBuilt with ⟨body, bytes⟩
          refine ⟨count, schema, remaining, body, rfl, ?_, bytes⟩
          simp [Image.pageCount, count, remaining, Nat.add_comm]
      next countTooLarge => contradiction

def Image.fileBytes (image : Image) : List UInt8 :=
  image.pages.flatMap Page.bytes

theorem Image.fileBytes_length (image : Image) :
    image.fileBytes.length = PhysicalCodec.pageSize * image.pageCount := by
  unfold Image.fileBytes Image.pageCount
  induction image.pages with
  | nil => rfl
  | cons page pages induction =>
      simp [page.length_eq, induction, Nat.mul_add, Nat.add_comm]

end CoreFile

end SQLeanite
