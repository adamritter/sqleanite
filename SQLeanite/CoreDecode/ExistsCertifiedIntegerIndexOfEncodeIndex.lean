import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.AbstractIndexTreeIntegerOrderedRangeWellRouted

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

/-- The generated-page refinement constructs the same certificate that the
linear reopen validator checks, without requiring that scan. The hypotheses
are physical provenance and page-availability facts established by the bulk
encoder; `integers` is exactly the catalog marker condition. -/
theorem existsCertifiedIntegerIndex_of_encodeIndex (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (integers : CoreFile.indexValuesInteger table index = true) :
    Nonempty (CertifiedIntegerIndex source (source.pageCount + 1)
      rootPage (expectedIndexEntries table index)) := by
  unfold CoreOverflow.encodeIndex at encoded
  cases plansResult : CoreOverflow.indexPlans table index with
  | none => simp [plansResult] at encoded
  | some plans =>
    simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
    cases provisionalResult : CoreOverflow.provisionalIndexStore? plans with
    | none => simp [provisionalResult] at encoded
    | some provisional =>
      simp only [provisionalResult] at encoded
      cases resolvedResult : CoreOverflow.resolvePlans
          (rootPage + provisional.plan.pageCount) plans with
      | none => simp [resolvedResult] at encoded
      | some resolved =>
        simp only [resolvedResult] at encoded
        cases updatedResult : provisional.retarget? resolved.cells with
        | none => simp [updatedResult] at encoded
        | some topology =>
          simp only [updatedResult] at encoded
          cases treeResult : topology.plan.encodePagesFrom rootPage with
          | none => simp [treeResult] at encoded
          | some treePages =>
            simp only [treeResult, Option.some.injEq] at encoded
            subst encoding
            have treeReads : ReadsPagesFrom source rootPage treePages :=
              ReadsPagesFrom.left reads
            have treeLength :=
              RecursivePageBTree.IndexPlan.encodePagesFrom_length treeResult
            have pageCountEqual :=
              RecursivePageBTree.IndexStore.retarget?_pageCount updatedResult
            have overflowReads : ReadsPagesFrom source
                (rootPage + provisional.plan.pageCount) resolved.pages := by
              have remaining := ReadsPagesFrom.right reads
              simpa [CoreOverflow.IndexEncoding.pages, treeLength,
                pageCountEqual] using remaining
            have planned : (CoreFile.sortedIndexRows table index).mapM
                (CoreOverflow.indexCellPlan? index) = some plans := by
              simpa [CoreOverflow.indexPlans] using plansResult
            have cellsDecoded := indexCellsDecode_resolvePlans index source
              (source.pageCount + 1) (CoreFile.sortedIndexRows table index)
              plans (rootPage + provisional.plan.pageCount) resolved planned
              resolvedResult (by omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at pageBound
                omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at withinSource
                omega)
              overflowReads
            have cellsEqual :=
              RecursivePageBTree.IndexStore.retarget?_represents updatedResult
            have planCells : IndexCellsDecode source (source.pageCount + 1)
                topology.plan.toCells (expectedIndexEntries table index) := by
              rw [cellsEqual]
              simpa [expectedIndexEntries] using cellsDecoded
            have planDecoded := IndexPlanDecodes.of_cells topology.plan _ planCells
            have balanced := topology.balanced
            have heightBound : topology.plan.height < source.pageCount + 1 := by
              have heightPageCount := topology.plan.height_lt_pageCount
              simp only [CoreOverflow.IndexEncoding.pages,
                List.length_append] at withinSource
              omega
            rcases decodeAbstractIndexTreeFrom_encodePagesFrom source topology.plan
                rootPage treePages _ (source.pageCount + 1) treeResult treeReads
                balanced planDecoded heightBound with
              ⟨tree, decoded, contents⟩
            have allInteger : ∀ entry ∈ tree.toList,
                entry.IntegerValued := by
              intro entry member
              exact expectedIndexEntries_all_integer table index integers entry
                (by simpa [contents] using member)
            have ordered : tree.toList.Pairwise IndexEntry.ValueLe := by
              rw [contents]
              exact expectedIndexEntries_pairwise_valueLe table index integers
            exact ⟨⟨tree, decoded,
              AbstractIndexTree.IntegerOrdered.of_pairwise tree allInteger
                ordered,
              contents⟩⟩

/-- Generated TEXT pages carry the same no-scan equality certificate.  Their
ordering proof is lexicographic over the exact stored UTF-8 bytes. -/
theorem existsCertifiedTextIndex_of_encodeIndex (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (texts : CoreFile.indexValuesText table index = true) :
    Nonempty (CertifiedTextIndex source (source.pageCount + 1)
      rootPage (expectedIndexEntries table index)) := by
  unfold CoreOverflow.encodeIndex at encoded
  cases plansResult : CoreOverflow.indexPlans table index with
  | none => simp [plansResult] at encoded
  | some plans =>
    simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
    cases provisionalResult : CoreOverflow.provisionalIndexStore? plans with
    | none => simp [provisionalResult] at encoded
    | some provisional =>
      simp only [provisionalResult] at encoded
      cases resolvedResult : CoreOverflow.resolvePlans
          (rootPage + provisional.plan.pageCount) plans with
      | none => simp [resolvedResult] at encoded
      | some resolved =>
        simp only [resolvedResult] at encoded
        cases updatedResult : provisional.retarget? resolved.cells with
        | none => simp [updatedResult] at encoded
        | some topology =>
          simp only [updatedResult] at encoded
          cases treeResult : topology.plan.encodePagesFrom rootPage with
          | none => simp [treeResult] at encoded
          | some treePages =>
            simp only [treeResult, Option.some.injEq] at encoded
            subst encoding
            have treeReads : ReadsPagesFrom source rootPage treePages :=
              ReadsPagesFrom.left reads
            have treeLength :=
              RecursivePageBTree.IndexPlan.encodePagesFrom_length treeResult
            have pageCountEqual :=
              RecursivePageBTree.IndexStore.retarget?_pageCount updatedResult
            have overflowReads : ReadsPagesFrom source
                (rootPage + provisional.plan.pageCount) resolved.pages := by
              have remaining := ReadsPagesFrom.right reads
              simpa [CoreOverflow.IndexEncoding.pages, treeLength,
                pageCountEqual] using remaining
            have planned : (CoreFile.sortedIndexRows table index).mapM
                (CoreOverflow.indexCellPlan? index) = some plans := by
              simpa [CoreOverflow.indexPlans] using plansResult
            have cellsDecoded := indexCellsDecode_resolvePlans index source
              (source.pageCount + 1) (CoreFile.sortedIndexRows table index)
              plans (rootPage + provisional.plan.pageCount) resolved planned
              resolvedResult (by omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at pageBound
                omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at withinSource
                omega)
              overflowReads
            have cellsEqual :=
              RecursivePageBTree.IndexStore.retarget?_represents updatedResult
            have planCells : IndexCellsDecode source (source.pageCount + 1)
                topology.plan.toCells (expectedIndexEntries table index) := by
              rw [cellsEqual]
              simpa [expectedIndexEntries] using cellsDecoded
            have planDecoded := IndexPlanDecodes.of_cells topology.plan _ planCells
            have heightBound : topology.plan.height < source.pageCount + 1 := by
              have heightPageCount := topology.plan.height_lt_pageCount
              simp only [CoreOverflow.IndexEncoding.pages,
                List.length_append] at withinSource
              omega
            rcases decodeAbstractIndexTreeFrom_encodePagesFrom source topology.plan
                rootPage treePages _ (source.pageCount + 1) treeResult treeReads
                topology.balanced planDecoded heightBound with
              ⟨tree, decoded, contents⟩
            have allText : ∀ entry ∈ tree.toList, entry.TextValued := by
              intro entry member
              exact expectedIndexEntries_all_text table index texts entry
                (by simpa [contents] using member)
            have ordered : tree.toList.Pairwise IndexEntry.ValueLe := by
              rw [contents]
              exact expectedIndexEntries_pairwise_valueLe_text table index texts
            exact ⟨⟨tree, decoded,
              AbstractIndexTree.wellRouted_of_pairwise_text tree allText ordered,
              contents⟩⟩

theorem lookupIndexValueFrom_text_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (texts : CoreFile.indexValuesText table index = true)
    (target : Core.Value) :
    lookupIndexValueFrom source target (source.pageCount + 1) rootPage =
      some ((expectedIndexEntries table index).filter
        (fun entry => entry.matchesValue target)) := by
  rcases existsCertifiedTextIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource texts with ⟨certificate⟩
  rw [lookupIndexValueFrom_decodeAbstract_exact source target
    (source.pageCount + 1) rootPage certificate.tree certificate.decoded
    certificate.routed]
  rw [certificate.contents]

theorem lookupIndexPrefixFrom_certified_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedIntegerIndex source fuel pageNumber expected)
    (limit : Nat) (result : List IndexEntry)
    (success : lookupIndexPrefixFrom source limit fuel pageNumber = some result) :
    result = expected.take limit := by
  unfold lookupIndexPrefixFrom at success
  rw [leftmostIndexLeafFrom_decodeAbstract source fuel pageNumber
    certificate.tree certificate.decoded] at success
  simp only [Option.bind_eq_bind, Option.bind] at success
  split at success
  next fits =>
    injection success with equal
    calc
      result = certificate.tree.leftmostLeaf.take limit := equal.symm
      _ = certificate.tree.toList.take limit :=
        (certificate.tree.take_toList_eq_take_leftmostLeaf limit fits).symm
      _ = expected.take limit := congrArg (List.take limit) certificate.contents
  next doesNotFit => contradiction

theorem lookupIndexPrefixFrom_text_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (texts : CoreFile.indexValuesText table index = true)
    (limit : Nat) (result : List IndexEntry)
    (success : lookupIndexPrefixFrom source limit (source.pageCount + 1)
      rootPage = some result) :
    result = (expectedIndexEntries table index).take limit := by
  rcases existsCertifiedTextIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource texts with ⟨certificate⟩
  unfold lookupIndexPrefixFrom at success
  rw [leftmostIndexLeafFrom_decodeAbstract source (source.pageCount + 1)
    rootPage certificate.tree certificate.decoded] at success
  simp only [Option.bind_eq_bind, Option.bind] at success
  split at success
  next fits =>
    injection success with equal
    calc
      result = certificate.tree.leftmostLeaf.take limit := equal.symm
      _ = certificate.tree.toList.take limit :=
        (certificate.tree.take_toList_eq_take_leftmostLeaf limit fits).symm
      _ = (expectedIndexEntries table index).take limit :=
        congrArg (List.take limit) certificate.contents
  next doesNotFit => contradiction

/-- The multi-leaf cursor has no first-leaf precondition: it stops after the
requested number of promoted-key entries across arbitrary generated height. -/
theorem indexPrefixFrom_text_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (texts : CoreFile.indexValuesText table index = true) (limit : Nat) :
    indexPrefixFrom source limit (source.pageCount + 1) rootPage =
      some ((expectedIndexEntries table index).take limit) := by
  rcases existsCertifiedTextIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource texts with ⟨certificate⟩
  rw [indexPrefixFrom_decodeAbstract_exact source limit
    (source.pageCount + 1) rootPage certificate.tree certificate.decoded]
  rw [certificate.contents]

def certifyIntegerIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) :
    Option (CertifiedIntegerIndex source fuel pageNumber expected) :=
  match decoded : decodeAbstractIndexTreeFrom source fuel pageNumber with
  | none => none
  | some tree =>
      match tree.certifyIntegerOrdered with
      | none => none
      | some certificate =>
          if contents : tree.toList = expected then
            some ⟨tree, decoded, certificate.valid, contents⟩
          else none

def certifyWideIntegerIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) :
    Option (CertifiedWideIntegerIndex source fuel pageNumber expected) :=
  match decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber with
  | none => none
  | some tree =>
      match tree.certifyIntegerOrdered with
      | none => none
      | some certificate =>
          if contents : tree.toList = expected then
            some ⟨tree, decoded, certificate.valid, contents⟩
          else none

def certifyWideTextIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) :
    Option (CertifiedWideTextIndex source fuel pageNumber expected) :=
  match decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber with
  | none => none
  | some tree =>
      if textsBool : tree.toList.all
          (fun entry => CoreFile.valueIsText entry.value) then
        have texts : ∀ entry ∈ tree.toList, entry.TextValued := by
          intro entry member
          have isText := (List.all_eq_true.mp textsBool) entry member
          cases valueEq : entry.value <;>
            simp [CoreFile.valueIsText, IndexEntry.TextValued, valueEq] at isText ⊢
        if ordered : tree.toList.Pairwise IndexEntry.ValueLe then
          if contents : tree.toList = expected then
            some ⟨tree, decoded,
              tree.wellRouted_of_pairwise_text texts ordered, contents⟩
          else none
        else none
      else none

def certifyAllValueIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) :
    Option (CertifiedAllValueIndex source fuel pageNumber expected) :=
  match decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber with
  | none => none
  | some tree =>
      if contents : tree.toList = expected then
        some ⟨tree, decoded, contents⟩
      else none

theorem lookupIndexValueFrom_certified_exact
    {source : PageSource} {fuel pageNumber : Nat}
    {expected : List IndexEntry}
    (certificate : CertifiedIntegerIndex source fuel pageNumber expected)
    (target : Core.Value) :
    lookupIndexValueFrom source target fuel pageNumber =
      some (expected.filter (fun entry => entry.matchesValue target)) := by
  rw [lookupIndexValueFrom_decodeAbstract_exact source target fuel pageNumber
    certificate.tree certificate.decoded certificate.ordered.wellRouted]
  rw [certificate.contents]

theorem lookupIndexRangeFrom_certified_exact
    {source : PageSource} {fuel pageNumber : Nat}
    {expected : List IndexEntry}
    (certificate : CertifiedIntegerIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    lookupIndexRangeFrom source operation target fuel pageNumber =
      some (expected.filter
        (fun entry => entry.matchesRange operation target)) := by
  rw [lookupIndexRangeFrom_decodeAbstract_exact source operation target fuel
    pageNumber certificate.tree certificate.decoded
    certificate.ordered.rangeWellRouted]
  rw [certificate.contents]

def CertifiedWideIntegerIndex.valueEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideIntegerIndex source fuel pageNumber expected)
    (target : Core.Value) : List IndexEntry :=
  (certificate.tree.equalityCandidates target).filter
    (fun entry => entry.matchesValue target)

theorem CertifiedWideIntegerIndex.valueEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideIntegerIndex source fuel pageNumber expected)
    (target : Core.Value) :
    certificate.valueEntries target =
      expected.filter (fun entry => entry.matchesValue target) := by
  unfold CertifiedWideIntegerIndex.valueEntries
  rw [AbstractIndexTree.equalityCandidates_exact
    certificate.ordered.wellRouted target, certificate.contents]

def CertifiedWideIntegerIndex.rangeEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideIntegerIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    List IndexEntry :=
  (certificate.tree.rangeCandidates operation target).filter
    (fun entry => entry.matchesRange operation target)

theorem CertifiedWideIntegerIndex.rangeEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideIntegerIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    certificate.rangeEntries operation target =
      expected.filter (fun entry => entry.matchesRange operation target) := by
  unfold CertifiedWideIntegerIndex.rangeEntries
  rw [AbstractIndexTree.rangeCandidates_exact
    certificate.ordered.rangeWellRouted operation target,
    certificate.contents]

def CertifiedWideTextIndex.valueEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideTextIndex source fuel pageNumber expected)
    (target : Core.Value) : List IndexEntry :=
  (certificate.tree.equalityCandidates target).filter
    (fun entry => entry.matchesValue target)

theorem CertifiedWideTextIndex.valueEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideTextIndex source fuel pageNumber expected)
    (target : Core.Value) :
    certificate.valueEntries target =
      expected.filter (fun entry => entry.matchesValue target) := by
  unfold CertifiedWideTextIndex.valueEntries
  rw [AbstractIndexTree.equalityCandidates_exact certificate.routed target,
    certificate.contents]

/-- Mixed range comparisons need the stronger range-routing relation.  Keep
the exact full-abstraction behavior for them; the TEXT equality fast path does
not weaken or assume that separate obligation. -/
def CertifiedWideTextIndex.rangeEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideTextIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    List IndexEntry :=
  certificate.tree.toList.filter
    (fun entry => entry.matchesRange operation target)

theorem CertifiedWideTextIndex.rangeEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideTextIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    certificate.rangeEntries operation target =
      expected.filter (fun entry => entry.matchesRange operation target) := by
  unfold CertifiedWideTextIndex.rangeEntries
  rw [certificate.contents]

def CertifiedAllValueIndex.valueEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedAllValueIndex source fuel pageNumber expected)
    (target : Core.Value) : List IndexEntry :=
  certificate.tree.toList.filter (fun entry => entry.matchesValue target)

theorem CertifiedAllValueIndex.valueEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedAllValueIndex source fuel pageNumber expected)
    (target : Core.Value) :
    certificate.valueEntries target =
      expected.filter (fun entry => entry.matchesValue target) := by
  unfold CertifiedAllValueIndex.valueEntries
  rw [certificate.contents]

def CertifiedAllValueIndex.rangeEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedAllValueIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    List IndexEntry :=
  certificate.tree.toList.filter
    (fun entry => entry.matchesRange operation target)

theorem CertifiedAllValueIndex.rangeEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedAllValueIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    certificate.rangeEntries operation target =
      expected.filter (fun entry => entry.matchesRange operation target) := by
  unfold CertifiedAllValueIndex.rangeEntries
  rw [certificate.contents]

end CoreDecode

end SQLeanite
