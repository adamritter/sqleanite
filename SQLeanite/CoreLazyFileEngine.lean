import SQLeanite.CoreFileAdapter
import SQLeanite.CoreOptimizerBridge

namespace SQLeanite
namespace CoreLazyFileEngine

/-!
# Cold page-directed reads

This is a narrow fast path for a single, non-aggregate primary-key or certified
secondary-index SELECT. It reads the catalog and only routed tree paths before
constructing the normal Core query result. A missing key in a stamped
Lean-generated image is complete; malformed bytes, general SQLite files, and
unsupported shapes return `none` and use `CoreFileEngine`'s full-file
validation.
-/

private def selectSource? (select : Select) : Option String := do
  if select.compounds.isEmpty && select.sources.size = 1 &&
      select.groupBy.isEmpty && select.having.isNone && select.offset = 0 then
    let source ← select.sources[0]?
    if source.subquerySql.isNone && source.joinOn.isNone then
      some (CoreSQL.canonical source.name)
    else none
  else none

private def joinSourceNames? (select : Select) : Option (String × String) := do
  if select.compounds.isEmpty && select.sources.size = 2 then
    let left ← select.sources[0]?
    let right ← select.sources[1]?
    some (CoreSQL.canonical left.name, CoreSQL.canonical right.name)
  else none

private def coldQuery? (schema : Core.Schema) (select : Select) :
    Option Core.Query := do
  let source ← select.sources[0]?
  unless CoreSQL.selectNamesBound schema source select do none
  let predicate ← (select.where_.mapM (CoreSQL.predicate schema)).toOption
  let count ← (CoreSQL.countTarget? schema select.columns.toList).toOption
  let sum ← (CoreSQL.sumColumn? schema select.columns.toList).toOption
  let extreme ← (CoreSQL.extremeColumn? schema select.columns.toList).toOption
  unless count.isNone && sum.isNone && extreme.isNone do none
  let columns ← (CoreSQL.projection schema select.columns.toList).toOption
  let ordering ← (CoreSQL.directOrdering schema source select).toOption
  let query : Core.Query := {
    columns
    predicate
    orderBy := ordering
    limit := select.limit
    distinct := select.distinct }
  some query

/-- Execute one read-only SELECT entirely through certified page traversal.
`none` is an optimization miss, never a partial result. -/
private def executeSelect? (paths : CoreFileAdapter.Paths)
    (geometry : Option CoreFileAdapter.GeneratedFileGeometry)
    (cache : CoreFileAdapter.PageReadCache) (select : Select) :
    IO (Option Core.Result) := do
  if let some (leftName, rightName) := joinSourceNames? select then
    let some lookup ← CoreFileAdapter.lookupGeneratedPrimaryJoin paths
        leftName rightName | return none
    let some query := (CoreSQL.joinQuery select leftName rightName
        lookup.leftSchema lookup.rightSchema).toOption | return none
    let optimized := CoreOptimizerBridge.optimizeJoin leftName rightName query
    unless optimized.on = some (CoreJoin.rowidOn
          lookup.leftSchema.primaryKey lookup.rightSchema.primaryKey) &&
        optimized.where_.isNone && optimized.kind = .inner do return none
    return some ({ rows := (optimized.evalPrimaryKeyCandidates
      lookup.leftCandidates lookup.rightRows) } : Core.Result)
  let some tableName := selectSource? select | return none
  let schema? ← match geometry with
    | some generated => pure (generated.tableSchema? tableName)
    | none => CoreFileAdapter.readTableSchema paths tableName
  let some schema := schema? | return none
  let some query := coldQuery? schema select | return none
  let optimized := CoreOptimizerBridge.optimize tableName query
  match query.predicate with
  | some (.equal column (.integer rowid)) =>
      if column = schema.primaryKey then
        let resolved : Option (Option Core.Row) ← match geometry with
          | some generated =>
              CoreFileAdapter.lookupGeneratedPrimaryRowWith generated paths
                tableName schema cache rowid
          | none => do
              match ← CoreFileAdapter.lookupPrimaryRowDecision paths tableName rowid with
              | none => pure none
              | some lookup =>
                  pure (if lookup.schema = schema then some (match lookup.outcome with
                    | .found row => some row
                    | .generatedMissing => none) else none)
        let some row := resolved | return none
        let physicalRows := row.toList
        return some ({ rows := optimized.eval physicalRows } : Core.Result)
      else
        let some geometry := geometry | return none
        let some lookup ← CoreFileAdapter.lookupGeneratedIndexCandidatesWith
            geometry paths tableName schema query (some cache) | return none
        return some ({ rows := optimized.eval lookup.candidates } : Core.Result)
  | some (.equal ..) | some (.compare ..) =>
      match query.predicate with
      | some (.compare operation column (.integer target)) =>
          if column = schema.primaryKey then
            let some lookup ← CoreFileAdapter.lookupGeneratedPrimaryRange
                paths tableName schema operation target | return none
            return some ({ rows := optimized.eval lookup.candidates } : Core.Result)
          else
            let some geometry := geometry | return none
            let some lookup ← CoreFileAdapter.lookupGeneratedIndexCandidatesWith
                geometry paths tableName schema query (some cache) | return none
            return some ({ rows := optimized.eval lookup.candidates } : Core.Result)
      | _ =>
          let some geometry := geometry | return none
          let some lookup ← CoreFileAdapter.lookupGeneratedIndexCandidatesWith
              geometry paths tableName schema query (some cache) | return none
          return some ({ rows := optimized.eval lookup.candidates } : Core.Result)
  | none =>
      let some lookup ← CoreFileAdapter.lookupGeneratedOrderedPrefix paths
          tableName schema query | return none
      return some ({ rows := optimized.eval lookup.candidates } : Core.Result)
  | _ => return none

private def executeReadStatementsGo? (paths : CoreFileAdapter.Paths)
    (geometry : Option CoreFileAdapter.GeneratedFileGeometry)
    (cache : CoreFileAdapter.PageReadCache) :
    List Statement → List Core.Result → IO (Option (List Core.Result))
  | [], reversed => pure (some reversed.reverse)
  | .select select :: statements, reversed => do
      let some result ← executeSelect? paths geometry cache select | return none
      executeReadStatementsGo? paths geometry cache statements (result :: reversed)
  | _, _ => pure none

/-- Stack-safe execution of a page-directed read batch. -/
private def executeReadStatements? (paths : CoreFileAdapter.Paths)
    (statements : List Statement) : IO (Option (List Core.Result)) :=
  do
    CoreFileAdapter.requireReadable paths.main
    let geometry ← CoreFileAdapter.readGeneratedFileGeometry paths
    let cache ← CoreFileAdapter.PageReadCache.create
    executeReadStatementsGo? paths geometry cache statements []

/-- `some result` means the cold path handled the complete SQL input. `none`
is an optimization miss and must be followed by ordinary execution.  A batch
of read-only statements stays page-directed statement by statement instead of
materializing the complete database merely because the input contains more
than one SELECT. -/
def execute? (paths : CoreFileAdapter.Paths) (sql : String) :
    IO (Option (Except String (List Core.Result))) := do
  let .ok statements := CoreTokenGrammar.parseStatements sql | return none
  let statementList := statements.toList
  if statementList.isEmpty then return none
  let some results ← executeReadStatements? paths statementList |
    return none
  return some (.ok results)

end CoreLazyFileEngine
end SQLeanite
