import SQLeanite.CoreConnectionSQL
import SQLeanite.CorePragmaTable
import SQLeanite.CoreJsonTable
import SQLeanite.CoreWindow
import SQLeanite.CoreScalarQuery

namespace SQLeanite.CoreDerivedSQL

structure Binding where
  name : String
  table : String

/-- Private materializations cannot collide with any user table. -/
def freshName (state : Core.State) : Except String String := do
  let candidates := (List.range (state.database.tables.length + 1)).map fun i => s!"__sqlean_derived_{i}"
  let some name := candidates.find? (fun name => (CoreNames.table? state.database name).isNone)
    | throw "cannot allocate a derived-table name"
  return name

/-- Raw insertion preserves selected values and uses Core's ordinary row
well-formedness checks. Internal rowids are never exposed by visibleQuery. -/
def materializeRows (state : Core.State) (definitions : Array ColumnDef)
    (rows : List (List Core.Value)) (zeroRowid : Bool := false) : Except String (Core.State × String) := do
  let name ← freshName state
  let schema ← CoreSQL.schema name definitions #[]
  let inputs ← rows.zipIdx.mapM fun (row,index) => do
    let rowid ← if zeroRowid then SQLSurface.value (.integer index) else pure (.null : Core.Value)
    return row ++ [rowid]
  let (next, _) ← CoreSQL.runCoreCommands state
    (.createTable schema :: inputs.map (Core.Command.insert name))
  return ({ next with lastInsertRowid := state.lastInsertRowid }, name)

def resultDefinitions (state : Core.State) (query : Select) (aliases : Array String) :
    Except String (Array ColumnDef) := do
  let definitions ← CoreCreateTableAs.columns state.database query
  unless aliases.isEmpty || aliases.size == definitions.size do
    throw s!"table has {definitions.size} values for {aliases.size} columns"
  return if aliases.isEmpty then definitions else
    definitions.mapIdx fun i column => { column with name := aliases[i]! }

/-- The intermediate row values are inserted directly into Core, without the
storage-affinity conversions of CREATE TABLE AS SELECT. Result affinity is
metadata for later comparisons; it must not change the selected value types. -/
def materialize (state : Core.State) (query : Select) (aliases : Array String) :
    Except String (Core.State × String) := do
  let query := CoreConnectionSQL.select state query.compoundHeight query
  let collations ← CoreSQL.resultCollationsFuel query.compoundHeight state query
  unless collations.all (fun name => (name.getD "binary").toLower == "binary") do
    throw "unsupported derived-table result collation"
  let result ← if CoreScalarQuery.has query.compoundHeight query then
      (·.result) <$> CoreScalarQuery.execute 256 state [] query
    else if CoreWindow.has query then CoreWindow.execute state query
    else (·.result) <$> CoreSQL.executeSelect state query
  let definitions ← resultDefinitions state query aliases
  materializeRows state definitions result.rows

def valuesQuery (rows : Array (Array Expr)) : Select := {
  columns := (rows[0]?.getD #[]).mapIdx fun i expr =>
    { expr, alias := some s!"column{i+1}", sourceSql := some expr.sql }
  valueRows := some rows }

/-- Intermediate storage rowids are not SQL columns of a derived table.
Resolve pseudocolumns against the original visible sources, including joins. -/
def rowidExpr (database : Core.Database) (sources : Array TableRef) (derived : List String)
    (aliases : Array ResultColumn) : Nat → Expr → Except String Expr
  | 0, _ => .error "derived expression nesting limit exceeded"
  | fuel + 1, expr => do
      let visit := rowidExpr database sources derived aliases fuel
      match expr with
      | .column qualifier name =>
          unless ["rowid", "oid", "_rowid_"].contains name.toLower do return expr
          let context ← CoreCreateTableAs.contexts database { columns := #[], sources }
          let candidates := CoreJoinUsing.nameCandidates context.sources qualifier name
          let visible := candidates.filter fun (i, position) =>
            match context.sources[i]? with
            | none => false
            | some ctx => !(derived.contains ctx.schema.name &&
                ctx.schema.hasHiddenRowid && position == ctx.schema.primaryKey)
          if candidates.length == visible.length then return expr
          match visible with
          | [] =>
              if qualifier.isNone then
                if let some column := aliases.find? (fun col => col.alias.any (fun alias => alias.toLower == name.toLower)) then
                  return ← visit column.expr
              throw s!"no such column: {(qualifier.map (· ++ ".")).getD ""}{name}"
          | [(i, _)] =>
              let some ctx := context.sources[i]? | throw "invalid derived source index"
              return .column (some ctx.sourceName) name
          | _ => throw s!"ambiguous column name: {name}"
      | .unary op arg => return .unary op (← visit arg)
      | .binary op a b => return .binary op (← visit a) (← visit b)
      | .call name args star => return .call name (← args.mapM visit) star
      | .isNull arg negated => return .isNull (← visit arg) negated
      | .inList arg values negated affinity => return .inList (← visit arg) (← values.mapM visit) negated affinity
      | .collate arg name => return .collate (← visit arg) name
      | .case_ base branches other =>
          return .case_ (← base.mapM visit) (← branches.mapM fun (a,b) => return (← visit a, ← visit b)) (← other.mapM visit)
      | .inSubquery arg sql negated => return .inSubquery (← visit arg) sql negated
      | other => return other

def visibleQuery (database : Core.Database) (derived : List String) (query : Select) : Except String Select := do
  let bind := fun aliases expr => rowidExpr database query.sources derived aliases
    (expr.height + (aliases.foldl (fun depth col => max depth col.expr.height) 0) + 2) expr
  return { query with
    columns := ← query.columns.mapM fun col => return { col with expr := ← bind #[] col.expr }
    where_ := ← query.where_.mapM (bind query.columns)
    groupBy := ← query.groupBy.mapM (bind query.columns)
    having := ← query.having.mapM (bind query.columns)
    orderBy := ← query.orderBy.mapM fun term => return { term with expr := ← bind query.columns term.expr }
    sources := ← query.sources.mapM fun source => return { source with joinOn := ← source.joinOn.mapM (bind #[]) } }

/-- Every captured subquery is independently certified; a SELECT result is
scoped to this evaluation and never becomes an on-disk table. -/
def prepare : Nat → Core.State → List Binding → Select → Except String (Core.State × Select)
  | 0, _, _, _ => .error "derived-table nesting limit exceeded"
  | fuel + 1, state, bindings, query => do
      let mut current := state
      let mut sources := #[]
      let mut derived := []
      let mut hidden := []
      for source in query.sources do
        match source.subquerySql with
        | some sql =>
            let parsed ← CoreTokenGrammar.parseCertified sql
            let inner ← match parsed.statements.toList with
              | [.select inner] => pure inner
              | [.values rows] => pure (valuesQuery rows)
              | _ => throw "a derived table requires one SELECT or VALUES query"
            let flatten := query.sources.size == 1 && source.columnAliases.isEmpty &&
              CoreJsonTable.flattenable inner
            let original := inner
            let (nested, inner) ← prepare fuel current bindings inner
            if flatten then
              let flattened ← CoreJsonTable.inlineProjection nested query inner source original
              let mut next := nested
              let mut arms := #[]
              for (op,arm) in flattened.compounds do
                let (prepared,arm) ← prepare fuel next bindings arm
                next := prepared
                arms := arms.push (op,arm)
              return (next, { flattened with compounds := arms })
            let (next, name) ← materialize nested inner source.columnAliases
            current := next
            derived := name :: derived
            sources := sources.push { source with
              name := name
              subquerySql := none
              alias := source.alias.orElse (fun _ => some source.name)
              columnAliases := #[] }
        | none =>
            if let some arguments := source.functionArgs then
              let name := match source.schema with
                | none => source.name
                | some schema => String.ofList (source.name.toList.drop (schema.length + 1))
              if source.schema.any (fun schema => !["main", "temp"].contains schema.toLower) then
                throw s!"no such table: {source.name}"
              if (CoreNames.table? state.database name).isSome then throw s!"'{name}' is not a function"
              let result ← if CoreJsonTable.supported name then CoreJsonTable.execute current name arguments
                else CorePragmaTable.execute current name arguments
              let (next, table) ← materializeRows current result.columns result.rows result.zeroRowid
              current := next
              hidden := { alias := source.alias.getD name, values := result.hidden, jsonValues := result.jsonValues } :: hidden
              sources := sources.push { source with
                name := table
                schema := none
                functionArgs := none
                alias := source.alias.orElse (fun _ => some name) }
            else if let some schema := source.schema then
              unless schema.toLower == "main" do throw s!"no such table: {source.name}"
              let name := String.ofList (source.name.toList.drop (schema.length + 1))
              sources := sources.push { source with
                name := name
                schema := none
                alias := source.alias.orElse (fun _ => some name) }
            else
              match bindings.find? (fun binding => binding.name.toLower == source.name.toLower) with
              | none => sources := sources.push source
              | some binding =>
                  derived := binding.table :: derived
                  sources := sources.push { source with
                    name := binding.table
                    alias := source.alias.orElse (fun _ => some source.name) }
      let mut compounds := #[]
      for (op, arm) in query.compounds do
        let (next, arm) ← prepare fuel current bindings arm
        current := next
        compounds := compounds.push (op, arm)
      let query ← CorePragmaTable.bindHidden current.database hidden { query with sources, compounds }
      let query ← visibleQuery current.database derived query
      return (current, query)

/-- Recursive UNION uses a FIFO work queue and remembers all enqueued keys,
not only previously emitted rows. NULLs compare equal for UNION membership. -/
def enqueue (all : Bool) (seen : List (List Core.Value))
    (rows : List (List Core.Value)) : List (List Core.Value) × List (List Core.Value) :=
  rows.foldl (fun (seen, fresh) row =>
    let key := Core.distinctRowKey row
    if !all && seen.contains key then (seen, fresh)
    else (key :: seen, fresh ++ [row])) (seen, [])

def recursiveRows (base : Core.State) (bindings : List Binding) (name : String)
    (definitions : Array ColumnDef) (step : Select) (all : Bool) :
    Nat → List (List Core.Value) → List (List Core.Value) → List (List Core.Value) →
      Except String (List (List Core.Value))
  | _, [], _, reversed => .ok reversed.reverse
  | 0, _ :: _, _, _ => .error "recursive CTE work limit exceeded"
  | fuel + 1, row :: pending, seen, reversed => do
      let (temporary, table) ← materializeRows base definitions [row]
      let (temporary, query) ← prepare 256 temporary ({name, table} :: bindings) step
      let (_, results) ← CoreConnectionSQL.executeStatement temporary (.select query) ""
      let (seen, fresh) := enqueue all seen (results.flatMap (·.rows))
      recursiveRows base bindings name definitions step all fuel (pending ++ fresh) seen (row :: reversed)

theorem enqueue_all_keeps_rows (seen : List (List Core.Value)) (rows : List (List Core.Value)) :
    (enqueue true seen rows).2 = rows := by
  unfold enqueue
  have fold (remaining : List (List Core.Value)) (seen fresh : List (List Core.Value)) :
      (remaining.foldl (fun (seen, fresh) row =>
        (Core.distinctRowKey row :: seen, fresh ++ [row])) (seen, fresh)).2 = fresh ++ remaining := by
    induction remaining generalizing seen fresh with
    | nil => simp
    | cons row rest ih => simp [List.foldl_cons, ih, List.append_assoc]
  simpa using fold rows seen []

/-- An unused CTE is not evaluated, including its runtime expressions. Schema
qualification bypasses the local CTE name. -/
def references : Nat → String → Select → Except String Bool
  | 0, _, _ => .error "CTE reference nesting limit exceeded"
  | fuel + 1, name, query => do
      for source in query.sources do
        if source.schema.isNone && source.subquerySql.isNone &&
            source.name.toLower == name.toLower then return true
        if let some sql := source.subquerySql then
          let parsed ← CoreTokenGrammar.parseCertified sql
          for statement in parsed.statements do
            if let .select query := statement then
              if ← references fuel name query then return true
      for (_, arm) in query.compounds do
        if ← references fuel name arm then return true
      return false


def read : Nat → Core.State → List Binding → Statement → Except String (List Core.Result)
  | 0, _, _, _ => .error "derived-query nesting limit exceeded"
  | fuel + 1, state, bindings, sql => do
      match sql with
      | .select query =>
          let (temporary, query) ← prepare fuel state bindings query
          if CoreScalarQuery.has query.compoundHeight query then
            return [(← CoreScalarQuery.execute fuel temporary [] query).result]
          if CoreWindow.has query then return [← CoreWindow.execute temporary query]
          let (_, results) ← CoreConnectionSQL.executeStatement temporary (.select query) ""
          return results
      | .values rows =>
          let (_, results) ← CoreConnectionSQL.executeStatement state (.select (valuesQuery rows)) ""
          return results
      | .withRecursive name aliases seed step all body _ =>
          if let .select query := body then
            unless ← references fuel name query do return ← read fuel state bindings body
          unless step.groupBy.isEmpty && step.having.isNone &&
              !(step.columns.any fun col => CoreAggregate.containsAggregate col.expr) do
            throw "recursive aggregate queries not supported"
          unless step.orderBy.isEmpty && step.limit.isNone && step.offset == 0 &&
              step.compounds.isEmpty do throw "unsupported recursive CTE queue ordering or limit"
          unless (step.sources.toList.filter (fun source => source.schema.isNone &&
              source.subquerySql.isNone && source.name.toLower == name.toLower)).length == 1 do
            throw "recursive CTE requires one recursive table reference"
          let (temporary, seed) ← prepare fuel state bindings seed
          let seed := CoreConnectionSQL.select temporary seed.compoundHeight seed
          let definitions ← resultDefinitions temporary seed aliases
          let selection ← CoreSQL.executeSelect temporary seed
          let (seen, initial) := enqueue all [] selection.result.rows
          let rows ← recursiveRows temporary bindings name definitions step all 100000 initial seen []
          let (temporary, table) ← materializeRows temporary definitions rows
          read fuel temporary ({name, table} :: bindings) body
      | .withCte name aliases source body materialization =>
          if let .select query := body then
            unless ← references fuel name query do return ← read fuel state bindings body
          let query ← match source with
            | .select query => pure query
            | .values rows => pure (valuesQuery rows)
            | _ => throw "unsupported CTE source"
          if query.sources.any (fun source => source.name.toLower == name.toLower) then
            throw s!"circular reference: {name}"
          let flatten := materialization != .materialized && CoreJsonTable.flattenable query
          let original := query
          let (temporary, query) ← prepare fuel state bindings query
          if flatten then
            if let .select outer := body then
              if outer.sources.size == 1 && outer.compounds.isEmpty then
                if let some source := outer.sources[0]? then
                  if source.name.toLower == name.toLower && source.schema.isNone &&
                      source.subquerySql.isNone && source.functionArgs.isNone then
                    let definitions ← resultDefinitions temporary query aliases
                    let query := if aliases.isEmpty then query else { query with
                      columns := query.columns.mapIdx fun i col =>
                        { col with alias := definitions[i]?.map (·.name) } }
                    let flattened ← CoreJsonTable.inlineProjection temporary outer query source original
                    let (_, results) ← CoreConnectionSQL.executeStatement temporary (.select flattened) ""
                    return results
          let (temporary, table) ← materialize temporary query aliases
          read fuel temporary ({name, table} :: bindings) body
      | _ => throw "unsupported writable CTE body"

def hasDerived : Nat → Select → Bool
  | 0, _ => true
  | fuel + 1, query => CoreScalarQuery.has query.compoundHeight query || CoreWindow.has query || query.sources.any (fun source => source.subquerySql.isSome || source.schema.isSome || source.functionArgs.isSome) ||
      query.compounds.any (fun arm => hasDerived fuel arm.2)

def executeRead (state : Core.State) (sql : Statement) :
    Except String (Core.State × List Core.Result) := do
  let results ← read 256 state [] sql
  return (state, results)

theorem executeRead_preserves_state (state next : Core.State) (sql : Statement)
    (results : List Core.Result) (success : executeRead state sql = .ok (next, results)) :
    next = state := by
  unfold executeRead at success
  cases outcome : read 256 state [] sql with
  | error message => simp [outcome, bind, Except.bind] at success
  | ok rows =>
      simp [outcome, bind, Except.bind, pure, Except.pure] at success
      exact success.1.symm

def executeStatement (state : Core.State) (sql : Statement) (source : String) :
    Except String (Core.State × List Core.Result) :=
  match sql with
  | .withCte .. | .withRecursive .. => executeRead state sql
  | .select query =>
      if hasDerived query.compoundHeight query then executeRead state sql
      else CoreConnectionSQL.executeStatement state sql source
  | _ => CoreConnectionSQL.executeStatement state sql source

end SQLeanite.CoreDerivedSQL
