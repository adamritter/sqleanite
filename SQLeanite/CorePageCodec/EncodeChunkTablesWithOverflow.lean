import SQLeanite.CorePageCodec.TableCellPlansNoOverflowEncodeCells

namespace SQLeanite
namespace CorePageCodec

def encodeChunkTablesWithOverflow : Nat →
    List CoreChunkPageState.TableState → Option OverflowEncoding
  | nextOverflow, [] => some ⟨[], [], nextOverflow⟩
  | nextOverflow, table :: tables => do
      let head ← encodeChunkNodeWithOverflow table.table.schema table.tree.root
        nextOverflow
      let tail ← encodeChunkTablesWithOverflow head.nextPage tables
      some {
        treePages := head.treePages ++ tail.treePages
        overflowPages := head.overflowPages ++ tail.overflowPages
        nextPage := tail.nextPage }

theorem encodeChunkNodeWithOverflow_pageNumbers (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (nextOverflow : Nat) (encoding : OverflowEncoding)
    (encoded : encodeChunkNodeWithOverflow schema node nextOverflow =
      some encoding) :
    encoding.treePages.map NumberedPage.pageNumber = node.pageIds := by
  induction node generalizing nextOverflow encoding with
  | leaf pageId entries =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases plansResult :
          (entries.flatMap fun entry => entry.2).mapM
            (CoreOverflow.tableCellPlan? schema) with
      | none => simp [plansResult] at encoded
      | some plans =>
          simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
          cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
          | none => simp [resolvedResult] at encoded
          | some resolved =>
              simp only [resolvedResult] at encoded
              cases pageResult : CoreFile.tableLeafPage? resolved.cells with
              | none => simp [pageResult] at encoded
              | some page =>
                  simp only [pageResult, Option.some.injEq] at encoded
                  subst encoding
                  rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left
              nextOverflow with
          | none => simp [leftResult] at encoded
          | some leftEncoding =>
              simp only [leftResult] at encoded
              cases rightResult : encodeChunkNodeWithOverflow schema right
                  leftEncoding.nextPage with
              | none => simp [rightResult] at encoded
              | some rightEncoding =>
                  simp only [rightResult, Option.some.injEq] at encoded
                  subst encoding
                  simp only [List.map_cons, List.map_append,
                    PersistentPageTree.Node.pageIds]
                  rw [encodeChunkRoot_pageNumber schema _ root rootResult,
                    leftInduction nextOverflow leftEncoding leftResult,
                    rightInduction leftEncoding.nextPage rightEncoding
                      rightResult]
                  rfl
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left
              nextOverflow with
          | none => simp [leftResult] at encoded
          | some leftEncoding =>
              simp only [leftResult] at encoded
              cases middleResult : encodeChunkNodeWithOverflow schema middle
                  leftEncoding.nextPage with
              | none => simp [middleResult] at encoded
              | some middleEncoding =>
                  simp only [middleResult] at encoded
                  cases rightResult : encodeChunkNodeWithOverflow schema right
                      middleEncoding.nextPage with
                  | none => simp [rightResult] at encoded
                  | some rightEncoding =>
                      simp only [rightResult, Option.some.injEq] at encoded
                      subst encoding
                      simp only [List.map_cons, List.map_append,
                        PersistentPageTree.Node.pageIds]
                      rw [encodeChunkRoot_pageNumber schema _ root rootResult,
                        leftInduction nextOverflow leftEncoding leftResult,
                        middleInduction leftEncoding.nextPage middleEncoding
                          middleResult,
                        rightInduction middleEncoding.nextPage rightEncoding
                          rightResult]
                      rfl

theorem encodeChunkNodeWithOverflow_nextPage (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (nextOverflow : Nat) (encoding : OverflowEncoding)
    (encoded : encodeChunkNodeWithOverflow schema node nextOverflow =
      some encoding) :
    encoding.nextPage = nextOverflow + encoding.overflowPages.length := by
  induction node generalizing nextOverflow encoding with
  | leaf pageId entries =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases plansResult :
          (entries.flatMap fun entry => entry.2).mapM
            (CoreOverflow.tableCellPlan? schema) with
      | none => simp [plansResult] at encoded
      | some plans =>
          simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
          cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
          | none => simp [resolvedResult] at encoded
          | some resolved =>
              simp only [resolvedResult] at encoded
              cases pageResult : CoreFile.tableLeafPage? resolved.cells with
              | none => simp [pageResult] at encoded
              | some page =>
                  simp only [pageResult, Option.some.injEq] at encoded
                  subst encoding
                  exact CoreOverflow.resolvePlans_nextPage resolvedResult
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left
              nextOverflow with
          | none => simp [leftResult] at encoded
          | some leftEncoding =>
              simp only [leftResult] at encoded
              cases rightResult : encodeChunkNodeWithOverflow schema right
                  leftEncoding.nextPage with
              | none => simp [rightResult] at encoded
              | some rightEncoding =>
                  simp only [rightResult, Option.some.injEq] at encoded
                  subst encoding
                  simp only [List.length_append]
                  rw [rightInduction leftEncoding.nextPage rightEncoding
                    rightResult,
                    leftInduction nextOverflow leftEncoding leftResult]
                  omega
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left
              nextOverflow with
          | none => simp [leftResult] at encoded
          | some leftEncoding =>
              simp only [leftResult] at encoded
              cases middleResult : encodeChunkNodeWithOverflow schema middle
                  leftEncoding.nextPage with
              | none => simp [middleResult] at encoded
              | some middleEncoding =>
                  simp only [middleResult] at encoded
                  cases rightResult : encodeChunkNodeWithOverflow schema right
                      middleEncoding.nextPage with
                  | none => simp [rightResult] at encoded
                  | some rightEncoding =>
                      simp only [rightResult, Option.some.injEq] at encoded
                      subst encoding
                      simp only [List.length_append]
                      rw [rightInduction middleEncoding.nextPage rightEncoding
                        rightResult,
                        middleInduction leftEncoding.nextPage middleEncoding
                          middleResult,
                        leftInduction nextOverflow leftEncoding leftResult]
                      omega

end CorePageCodec

end SQLeanite
