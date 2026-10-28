import SQLeanite.CoreViewSQL
import SQLeanite.CoreViewRename
import SQLeanite.CoreDeclaredCollationSQL
import SQLeanite.CoreGeneratedSQL
import SQLeanite.CoreConnectionSQL
import SQLeanite.CorePragmaTable
import SQLeanite.CoreJsonTable
import SQLeanite.CoreWindow
import SQLeanite.CoreScalarQuery
import SQLeanite.CoreUpsertSQL
import SQLeanite.CoreForeignKey
import SQLeanite.CoreForeignKeyRename

namespace SQLeanite.CoreDerivedSQL

structure Binding where
  name : String
  table : String
  activeView : Bool := false

/-- Private materializations cannot collide with any user table. -/
def freshName (state : Core.State) : Except String String := do
  let candidates := (List.range (state.database.tables.length + 1)).map fun i => s!"__sqlean_derived_{i}"
  let some name := candidates.find? (fun name => (CoreNames.table? state.database name).isNone)
    | throw "cannot allocate a derived-table name"
  return name

/-- Private SQL carries the actual output declarations; the checked catalog
boundary independently verifies that it describes the unchanged physical schema. -/
def materializationSQL (schema : Core.Schema) (definitions : Array ColumnDef) : String :=
  let columns := schema.catalogColumns.map fun column =>
    let base := String.ofList (CanonicalSchemaSQL.columnChars column)
    match definitions.find? (fun definition => definition.name.toLower == column.name.toLower) with
    | none => base
    | some definition =>
        if definition.collation.toLower == "binary" then base
        else base ++ " COLLATE " ++ String.ofList (CanonicalSchemaSQL.quoteChars definition.collation)
  "CREATE TABLE " ++ String.ofList (CanonicalSchemaSQL.quoteChars schema.name) ++
    "(" ++ String.intercalate "," columns ++ ")"

def carryCollations (definitions : Array ColumnDef) (names : List (Option String)) : Array ColumnDef :=
  definitions.mapIdx fun position column =>
    { column with collation := (names[position]?.bind id).getD "binary" }

theorem carryCollations_names (definitions : Array ColumnDef) (names : List (Option String)) :
    ((carryCollations definitions names).map (·.name)) = definitions.map (·.name) := by
  ext position <;> simp [carryCollations]

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
  let next ← if definitions.all (fun definition => definition.collation.toLower == "binary") then pure next
    else CoreSourceSQL.retain next name (materializationSQL schema definitions)
  return ({ next with lastInsertRowid := state.lastInsertRowid }, name)

def resultDefinitions (state : Core.State) (query : Select) (aliases : Array String) :
    Except String (Array ColumnDef) := do
  let query ← CoreDeclaredCollationSQL.select state query
  let definitions ← CoreCreateTableAs.derivedColumns state.database query
  -- Subquery columns inherit the first projection, not the compound set key.
  -- VALUES has the same first expression list even when later rows are lowered.
  let collations ← CoreSQL.baseResultCollations state { query with valueRows := none, compounds := #[] }
  unless collations.length == definitions.size do throw "derived-table result metadata width mismatch"
  let definitions := carryCollations definitions collations
  unless aliases.isEmpty || aliases.size == definitions.size do
    throw s!"table has {definitions.size} values for {aliases.size} columns"
  return if aliases.isEmpty then definitions else
    definitions.mapIdx fun i column => { column with name := aliases[i]! }

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

mutual
/-- Source preparation and execution are distinct phases. Private preparation
checks the real expressions against real schemas with LIMIT 0 and keeps no
runtime rows; execution materializes the selected typed values unchanged. -/
def materializeWithSources (parents : List CoreScalarQuery.Frame) (preparing : Bool) :
    Nat → Core.State → List Binding → Select → Array String → Except String (Core.State × String)
  | 0, _, _, _, _ => .error "derived-table nesting limit exceeded"
  | fuel + 1, state, bindings, query, aliases => do
      let query := CoreConnectionSQL.select state query.compoundHeight query
      let input := if preparing then { query with limit := some 0 } else query
      let compile := fun mode _depth state parents query => prepareWithSources parents mode fuel state bindings query
      let (state,metadata,result) ← if !parents.isEmpty || CoreScalarQuery.has input.compoundHeight input then do
          let selected ← CoreScalarQuery.executePrepared compile preparing fuel state parents input
          pure (selected.inputState, selected.inputQuery, selected.result)
        else if CoreWindow.has input then do
          pure (state,query,← CoreWindow.execute state input)
        else do
          pure (state,query,(← CoreSQL.executeSelect state input).result)
      let definitions ← resultDefinitions state metadata aliases
      materializeRows state definitions result.rows

/-- Every captured subquery is independently certified; a SELECT result is
scoped to this evaluation and never becomes an on-disk table. -/
def prepareWithSources (parents : List CoreScalarQuery.Frame) (preparing : Bool) : Nat → Core.State → List Binding → Select → Except String (Core.State × Select)
  | 0, _, _, _ => .error "derived-table nesting limit exceeded"
  | fuel + 1, state, bindings, query => do
      let preparing := preparing || query.limit == some 0
      let mut current := { state with schemaHash := some state.schemaHashValue }
      let mut sources := #[]
      let mut derived := []
      let mut hidden := []
      for source in query.sources do
        let barePragma := CoreViewSQL.sourceName? source
        let source := if source.functionArgs.isNone && source.subquerySql.isNone &&
            barePragma.any (fun name => (CorePragmaTable.names name).isSome &&
              (CoreNames.table? current.database name).isNone && (CoreViewSQL.find? current name).isNone) then
            { source with functionArgs := some #[] }
          else source
        let localBinding := bindings.any (fun binding => !binding.activeView &&
          binding.name.toLower == source.name.toLower)
        let source := if bindings.any (·.activeView) && !localBinding && source.schema.isNone &&
            source.subquerySql.isNone && source.functionArgs.isNone then
            { source with name := "main." ++ source.name, schema := some "main" }
          else source
        let persistentName := CoreViewSQL.sourceName? source
        let binding := persistentName.bind fun name => bindings.find? (fun binding => binding.name.toLower == name.toLower)
        let view := if source.subquerySql.isNone && source.functionArgs.isNone &&
            !binding.any (fun binding => !binding.activeView && source.schema.isNone) then
            persistentName.bind (CoreViewSQL.find? current)
          else none
        if view.isSome && binding.any (·.activeView) then
          throw s!"view {(view.map (·.definition.name)).getD source.name} is circularly defined"
        let nestedBindings := match view with
          | none => bindings
          | some view => { name := view.definition.name, table := "", activeView := true } :: bindings.filter (·.activeView)
        let nestedParents := if view.isSome then [] else parents
        match source.subquerySql.orElse (fun _ => view.map (·.text)) with
        | some sql =>
            let inner ← match view with
              | some view => pure view.definition.query
              | none => do
                  let parsed ← CoreTokenGrammar.parseCertified sql
                  match parsed.statements.toList with
                  | [.select inner] => pure inner
                  | [.values rows] => pure (valuesQuery rows)
                  | _ => throw "a derived table requires one SELECT or VALUES query"
            let aliases := match view with
              | none => source.columnAliases
              | some view => view.definition.columns.getD #[]
            let flatten := view.isNone && query.sources.size == 1 && aliases.isEmpty &&
              CoreJsonTable.flattenable inner
            let original := inner
            let (nested, inner) ← prepareWithSources nestedParents preparing fuel current nestedBindings inner
            if flatten then
              let flattened ← CoreJsonTable.inlineProjection nested query inner source original
              let mut next := nested
              let mut arms := #[]
              for (op,arm) in flattened.compounds do
                let (prepared,arm) ← prepareWithSources parents preparing fuel next bindings arm
                next := prepared
                arms := arms.push (op,arm)
              return (next, { flattened with compounds := arms })
            if let some view := view then
              if let some expected := view.definition.columns then
                let actual ← resultDefinitions nested inner #[]
                unless actual.size == expected.size do
                  throw s!"expected {expected.size} columns for '{view.definition.name}' but got {actual.size}"
            let (next, name) ← materializeWithSources nestedParents preparing fuel nested nestedBindings inner aliases
            current := next
            derived := name :: derived
            sources := sources.push { source with
              name := name
              schema := none
              subquerySql := none
              alias := source.alias.orElse (fun _ => some ((view.map (·.definition.name)).getD source.name))
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
                else
                  CorePragmaTable.executeWith (fun state schema name target => viewInspection fuel state schema name target)
                    current name arguments
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
              unless (CoreNames.table? current.database name).isSome do throw s!"no such table: {source.name}"
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
        let (next, arm) ← prepareWithSources parents preparing fuel current bindings arm
        current := next
        compounds := compounds.push (op, arm)
      let query ← CorePragmaTable.bindHidden current.database hidden { query with sources, compounds }
      let query ← CoreDeclaredCollationSQL.select current query
      let query ← visibleQuery current.database derived query
      return (current, query)


/-- PRAGMA preparation obtains a view's actual column declarations without
executing its row expressions. The temporary named schema never escapes. -/
def viewMetadataState : Nat → Core.State → String → Except String Core.State
  | 0, _, _ => .error "view metadata nesting limit exceeded"
  | fuel + 1, state, name => do
      let query : Select := { columns := #[{ expr := .star none }], sources := #[{ name }], limit := some 0 }
      let (temporary,query) ← prepareWithSources [] true fuel state [] query
      let some source := query.sources[0]? | throw "missing view metadata source"
      let some table := temporary.database.findTable? source.name | throw "missing view metadata table"
      let table ← Core.Table.rebuild { table.schema with name } [] []
      let database ← Core.Database.rebuild (state.database.tables ++ [table])
      return { state with database }

def viewInspection : Nat → Core.State → Option String → String → Option String →
    Except String (List (List Value))
  | 0, _, _, _, _ => .error "view inspection nesting limit exceeded"
  | fuel + 1, state, schema, name, target => do
      let mut metadata := state
      let mut viewNames := []
      unless schema.any (fun name => name.toLower == "temp") do
        if name.toLower == "table_list" then
          for view in state.catalog.current.views do
            metadata ← viewMetadataState fuel metadata view.definition.name
            viewNames := viewNames ++ [view.definition.name]
        else if ["table_info","table_xinfo"].contains name.toLower then
          if let some view := target.bind (CoreViewSQL.find? state) then
            metadata ← viewMetadataState fuel state view.definition.name
            viewNames := [view.definition.name]
      CoreSchemaPragma.inspectionRows metadata.database schema name target (state.schemaHash.map (·.names)) viewNames

end

def prepare (fuel : Nat) (state : Core.State) (bindings : List Binding) (query : Select) :
    Except String (Core.State × Select) := prepareWithSources [] false fuel state bindings query

def materialize (state : Core.State) (query : Select) (aliases : Array String) :
    Except String (Core.State × String) := materializeWithSources [] false 256 state [] query aliases

def executeScalar (fuel : Nat) (state : Core.State) (bindings : List Binding) (query : Select) :
    Except String CoreScalarQuery.Result :=
  CoreScalarQuery.executePrepared
    (fun mode depth state parents query => prepareWithSources parents mode depth state bindings query)
    false fuel state [] query

/-- Recursive UNION uses a FIFO work queue and remembers all enqueued keys,
not only previously emitted rows. NULLs compare equal for UNION membership. -/
def enqueue (all : Bool) (seen : List (List Core.Value))
    (rows : List (List Core.Value)) : List (List Core.Value) × List (List Core.Value) :=
  rows.foldl (fun (seen, fresh) row =>
    let key := Core.distinctRowKey row
    if !all && seen.contains key then (seen, fresh)
    else (key :: seen, fresh ++ [row])) (seen, [])

/-- The global recursive UNION queue uses its full compound key, independently
of the first projection's declared field metadata. UNION ALL keeps every row. -/
def enqueueCollated (all : Bool) (kinds : List SQLite.Collation.Kind)
    (seen : List (List Core.Value)) (rows : List (List Core.Value)) :
    List (List Core.Value) × List (List Core.Value) :=
  if all || kinds.all (· == .binary) then enqueue all seen rows
  else rows.foldl (fun (seen,fresh) row =>
    let key := Core.distinctRowKey row
    if seen.any (fun other => CoreCompound.compareCollated kinds key other == .eq) then (seen,fresh)
    else (key :: seen, fresh ++ [row])) (seen,[])

/-- Every recursive term runs against the current row. SQLite lowers its
internal UNIONs to ALL and enforces uniqueness once in the global queue. -/
def recursiveStep (name : String) (all : Bool) : Nat → Select → Except String Select
  | 0, _ => .error "recursive CTE nesting limit exceeded"
  | fuel + 1, query => do
      unless query.groupBy.isEmpty && query.having.isNone &&
          !(query.columns.any fun column => CoreAggregate.containsAggregate column.expr) do
        throw "recursive aggregate queries not supported"
      unless query.orderBy.isEmpty && query.limit.isNone && query.offset == 0 do
        throw "unsupported recursive CTE queue ordering or limit"
      unless (query.sources.toList.filter (fun source => source.schema.isNone &&
          source.subquerySql.isNone && source.name.toLower == name.toLower)).length == 1 do
        throw "recursive CTE requires one recursive table reference"
      let compounds ← query.compounds.mapM fun (operation,arm) => do
        unless operation == (if all then .unionAll else .unionDistinct) do
          throw "recursive CTE requires matching UNION operators"
        return (.unionAll, ← recursiveStep name all fuel arm)
      return { query with compounds }

def recursiveRows (base : Core.State) (bindings : List Binding) (name : String)
    (definitions : Array ColumnDef) (step : Select) (all : Bool) (kinds : List SQLite.Collation.Kind) :
    Nat → List (List Core.Value) → List (List Core.Value) → List (List Core.Value) →
      Except String (List (List Core.Value))
  | _, [], _, reversed => .ok reversed.reverse
  | 0, _ :: _, _, _ => .error "recursive CTE work limit exceeded"
  | fuel + 1, row :: pending, seen, reversed => do
      let (temporary, table) ← materializeRows base definitions [row]
      let (temporary, query) ← prepare 256 temporary ({name, table} :: bindings) step
      let (_, results) ← CoreConnectionSQL.executeStatement temporary (.select query) ""
      let (seen, fresh) := enqueueCollated all kinds seen (results.flatMap (·.rows))
      recursiveRows base bindings name definitions step all kinds fuel (pending ++ fresh) seen (row :: reversed)

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

theorem enqueueCollated_all_keeps_rows (kinds : List SQLite.Collation.Kind)
    (seen rows : List (List Core.Value)) : (enqueueCollated true kinds seen rows).2 = rows := by
  simp [enqueueCollated, enqueue_all_keeps_rows]

theorem enqueueCollated_duplicate (kinds : List SQLite.Collation.Kind)
    (seen : List (List Core.Value)) (row : List Core.Value)
    (nonbinary : kinds.all (· == .binary) = false)
    (known : seen.any (fun other => CoreCompound.compareCollated kinds (Core.distinctRowKey row) other == .eq) = true) :
    enqueueCollated false kinds seen [row] = (seen,[]) := by
  simp only [enqueueCollated, Bool.false_or, nonbinary, Bool.false_eq_true, ↓reduceIte,
    List.foldl_cons, known, Bool.true_eq, List.foldl_nil]

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


/-- A later unused declaration must not force an earlier CTE's runtime values.
Only source dependencies reachable from the body cause materialization. -/
def statementReferences : Nat → String → Statement → Except String Bool
  | 0, _, _ => .error "CTE reference nesting limit exceeded"
  | fuel + 1, name, statement => do
      match statement with
      | .select query => references fuel name query
      | .withCte localName _ source body _ =>
          if ← statementReferences fuel name body then return true
          if ← statementReferences fuel localName body then statementReferences fuel name source else pure false
      | .withRecursive localName _ seed step _ body _ =>
          if ← statementReferences fuel name body then return true
          if ← statementReferences fuel localName body then
            return (← references fuel name seed) || (← references fuel name step)
          else pure false
      | _ => pure false


def read : Nat → Core.State → List Binding → Statement → Except String (List Core.Result)
  | 0, _, _, _ => .error "derived-query nesting limit exceeded"
  | fuel + 1, state, bindings, sql => do
      match sql with
      | .select query =>
          let (temporary, query) ← prepare fuel state bindings query
          if CoreScalarQuery.has query.compoundHeight query then
            return [(← executeScalar fuel temporary bindings query).result]
          if CoreWindow.has query then return [← CoreWindow.execute temporary query]
          let (_, results) ← CoreConnectionSQL.executeStatement temporary (.select query) ""
          return results
      | .values rows =>
          let (_, results) ← CoreConnectionSQL.executeStatement state (.select (valuesQuery rows)) ""
          return results
      | .withRecursive name aliases seed step all body _ =>
          unless ← statementReferences fuel name body do return ← read fuel state bindings body
          let lowered ← recursiveStep name all step.compoundHeight step
          let (temporary, seed) ← prepare fuel state bindings seed
          let seed := CoreConnectionSQL.select temporary seed.compoundHeight seed
          let definitions ← resultDefinitions temporary seed aliases
          let (metadataState, table) ← materializeRows temporary definitions []
          let (metadataState, boundStep) ← prepareWithSources [] true fuel metadataState ({name,table} :: bindings) step
          discard <| CoreScalarQuery.executePrepared
            (fun mode depth state parents query => prepareWithSources parents mode depth state bindings query)
            true fuel metadataState [] { boundStep with limit := some 0 }
          let compound := {
            seed with
            compounds := seed.compounds.push ((if all then .unionAll else .unionDistinct),boundStep) }
          let collations ← CoreSQL.resultCollationsFuel compound.compoundHeight metadataState compound
          let kinds ← collations.mapM (fun collation => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName collation))
          let selection ← CoreSQL.executeSelect temporary seed
          let (seen, initial) := enqueueCollated all kinds [] selection.result.rows
          let rows ← recursiveRows temporary bindings name definitions lowered all kinds 100000 initial seen []
          let (temporary, table) ← materializeRows temporary definitions rows
          read fuel temporary ({name, table} :: bindings) body
      | .withCte name aliases source body materialization =>
          unless ← statementReferences fuel name body do return ← read fuel state bindings body
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
  | fuel + 1, query => CoreScalarQuery.has query.compoundHeight query || CoreWindow.has query || query.sources.any (fun source => source.subquerySql.isSome || source.schema.isSome || source.functionArgs.isSome ||
        (CorePragmaTable.names source.name).isSome) ||
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

/-- A plain SELECT * over VALUES is a SQLite coroutine: later rows observe
last_insert_rowid from earlier insertions. Sorting/grouping and other read
shapes stay on the existing materialization path. -/
def streamingValues (query : Select) : Option (Array (Array Expr)) := do
  unless query.valueRows.isNone && query.where_.isNone && query.groupBy.isEmpty &&
      query.having.isNone && query.orderBy.isEmpty && !query.distinct &&
      query.limit.isNone && query.offset == 0 && query.compounds.isEmpty do none
  let [source] := query.sources.toList | none
  let [column] := query.columns.toList | none
  let .star qualifier := column.expr | none
  unless column.alias.isNone && qualifier.all (fun name => name.toLower == (source.alias.getD source.name).toLower) do none
  let sql ← source.subquerySql
  let parsed ← (CoreTokenGrammar.parseCertified sql).toOption
  match parsed.statements.toList with
  | [.values rows] => return rows
  | [.select inner] =>
      unless inner.sources.isEmpty && inner.where_.isNone && inner.groupBy.isEmpty &&
          inner.having.isNone && inner.orderBy.isEmpty && !inner.distinct &&
          inner.limit.isNone && inner.offset == 0 && inner.compounds.isEmpty do none
      inner.valueRows
  | _ => none

theorem streamingValues_ordered (query : Select) (ordered : query.orderBy.isEmpty = false) :
    streamingValues query = none := by
  simp [streamingValues, ordered]

/-- Connection-level row tracking reuses the existing per-row executors.
The source-free Core SQL command translation keeps its ordinary AST domain. -/
def executeConnectionStatement (state : Core.State) (sql : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  let sql ← CoreDeclaredCollationSQL.statement state sql
  let preparation ← match CoreForeignKey.target? sql with
    | none => pure none
    | some target => CoreGeneratedSQL.preparation state target
  if !state.foreignKeys && preparation.isNone then return ← CoreConnectionSQL.executeStatement state sql source
  let bound := CoreConnectionSQL.statement state sql
  let (next, results) ← match bound with
    | .insert table columns rows conflict returning =>
        if CoreSQL.automaticTable state table then
          CoreSQL.executeAutoInsert state table columns (.inl rows) conflict returning preparation
        else CoreSQL.executeInsertReturning state table columns (.inl rows) conflict returning preparation
    | .insertSelect table columns query conflict returning =>
        if CoreLastInsert.queryUses query.compoundHeight query then
          CoreSQL.executeRegisterInsertSelect state table columns query conflict returning preparation
        else if CoreSQL.automaticTable state table then
          CoreSQL.executeAutoInsert state table columns (.inr query) conflict returning preparation
        else CoreSQL.executeInsertReturning state table columns (.inr query) conflict returning preparation
    | .update table alias assignments condition conflict returning => do
        unless conflict == .default || conflict == .abort || conflict == .ignore || conflict == .replace do
          throw "unsupported general verified-MVP SQL: UPDATE conflict policy"
        let tableName := CoreSQL.resolveTableName state table
        let some stored := state.database.findTable? tableName | throw s!"no such table: {table}"
        unless CoreSQL.writeNamesBound stored.schema table alias assignments condition do
          let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := alias.getD table }
          for expression in assignments.toList.map (·.2) ++ condition.toList do
            if let some message := SQLite.Scalar.resolutionError (fun q n => (ctx.column? q n).isSome) expression then
              throw message
          throw "unsupported general verified-MVP SQL: unbound UPDATE name"
        let (next, results) ← CoreSQL.executeUpdateReturning state tableName alias stored
          assignments.toList condition conflict returning preparation
        pure (next, if returning.isEmpty then results.map (fun result => { result with rows := [] }) else results)
    | _ => CoreSourceSQL.executeStatement state bound source
  return (CoreConnectionSQL.account state next sql results, results)

/-- Derived SELECT inputs are evaluated in a private read state. Only their
values cross back into the original connection's ordinary INSERT machinery;
private table names, counters and transaction snapshots cannot escape. -/
def insertSelect (state : Core.State) (table : String) (columns : Option (Array String))
    (query : Select) (conflict : ConflictAction) (returning : Array ResultColumn)
    (source : String) : Except String (Core.State × List Core.Result) := do
  let some stored := CoreNames.table? state.database table | throw s!"no such table: {table}"
  if let some inputs := streamingValues query then
    return ← executeConnectionStatement state (.insert table columns inputs conflict returning) source
  let (temporary, query) ← prepare 256 state [] query
  let query := CoreConnectionSQL.select state query.compoundHeight query
  let definitions ← CoreCreateTableAs.columns temporary.database query
  let preparation ← CoreGeneratedSQL.preparation state table
  let targets ← CoreSQL.prepareInsertTargets columns (.inr query) preparation
  CoreSQL.checkInsertSelectColumns stored.schema targets.columns definitions.size targets.implicitWidth
  let selected ← if CoreScalarQuery.has query.compoundHeight query then
      (·.result) <$> executeScalar 256 temporary [] query
    else if CoreWindow.has query then CoreWindow.execute temporary query
    else (·.result) <$> CoreSQL.executeSelect temporary query
  let inputs ← selected.rows.mapM CoreSQL.selectedRowExpressions
  executeConnectionStatement state (.insert table columns inputs.toArray conflict returning) source

def createTableAs (state : Core.State) (name : String) (query : Select) (guard : Bool) :
    Except String (Core.State × List Core.Result) := do
  unless ← CoreSQL.prepareCreateTable state name guard do return (state,[{}])
  let (temporary,query) ← prepare 256 state [] query
  let query := CoreConnectionSQL.select state query.compoundHeight query
  let definitions ← CoreCreateTableAs.columns temporary.database query
  let selected ← if CoreScalarQuery.has query.compoundHeight query then
      (·.result) <$> executeScalar 256 temporary [] query
    else if CoreWindow.has query then CoreWindow.execute temporary query
    else (·.result) <$> CoreSQL.executeSelect temporary query
  let schema ← CoreSQL.schema name definitions #[]
  let inputs ← selected.rows.mapM CoreSQL.selectedRowExpressions
  let values ← inputs.mapM (CoreSQL.rowValues schema none)
  let (next,_) ← CoreSQL.runCoreCommands state (.createTable schema :: values.map (Core.Command.insert name))
  let next ← CoreSQL.retainCreateTableAsSQL next name
  let results := [({} : Core.Result)]
  return (CoreConnectionSQL.account state next (.createTableAs name query guard) results,results)

def inspectViewPragma (state : Core.State) (name : String) (argument : Option Expr) (schema : Option String) :
    Except String (Core.State × List Core.Result) := do
  if schema.any (fun name => !["main","temp"].contains name.toLower) then throw s!"unknown database {schema.getD ""}"
  let target ← argument.mapM fun argument => do
    let some target := CoreSchemaPragma.argumentName argument | throw "unsupported PRAGMA argument"
    return target
  let values ← viewInspection 256 state schema name target
  let rows ← values.mapM (List.mapM SQLSurface.value)
  return (state,[{ rows }])

def executeBase (state : Core.State) (sql : Statement) (source : String) :
    Except String (Core.State × List Core.Result) :=
  match sql with
  | .pragma name argument schema =>
      if name.toLower == "encoding" && argument.isNone then do
        if schema.any (fun name => !["main","temp"].contains name.toLower) then throw s!"unknown database {schema.getD ""}"
        let encoding := match state.catalog.current.textEncoding with
          | 2 => "UTF-16le" | 3 => "UTF-16be" | _ => "UTF-8"
        let value ← SQLSurface.value (.text encoding)
        return (state,[{ rows := [[value]] }])
      else if ["table_info","table_xinfo","table_list"].contains name.toLower && !state.catalog.current.views.isEmpty then
        inspectViewPragma state name argument schema
      else executeConnectionStatement state sql source
  | .createView .. | .dropView .. => CoreViewSQL.executeDDL state sql source
  | .createTable .. | .createStrictTable .. =>
      if CoreViewSQL.schemaNoop state sql then .ok (state,[{}])
      else executeConnectionStatement state sql source
  | .createTableAs name query guard =>
      if CoreViewSQL.schemaNoop state sql then .ok (state,[{}]) else

      if CoreViewSQL.uses query.compoundHeight state query || hasDerived query.compoundHeight query then createTableAs state name query guard
      else executeConnectionStatement state sql source
  | .insertSelect table columns query conflict returning =>
      if CoreViewSQL.uses query.compoundHeight state query || hasDerived query.compoundHeight query then insertSelect state table columns query conflict returning source
      else executeConnectionStatement state sql source
  | .upsert base alias clauses => do
      let transformed ← CoreDeclaredCollationSQL.statement state (.upsert base alias clauses)
      let .upsert base alias clauses := transformed | throw "invalid declared UPSERT preparation"
      let preparation ← match CoreForeignKey.target? base with
        | none => pure none
        | some target => CoreGeneratedSQL.preparation state target
      CoreUpsertSQL.execute state base alias clauses preparation
  | .withCte .. | .withRecursive .. => executeRead state sql
  | .select query =>
      if CoreViewSQL.uses query.compoundHeight state query || hasDerived query.compoundHeight query then executeRead state sql
      else executeConnectionStatement state sql source
  | _ => executeConnectionStatement state sql source

/-- Keep SQLite's live schema-hash insertion/removal order independently of
Core's physical table list. Transaction schema invalidation reloads catalog
order; private query materialization starts from the caller's cached order. -/
def schemaTransition (before next : Core.State) (sql : Statement) : Core.State := Id.run do
  let original := before.schemaHashValue
  let oldNames := before.database.tables.map (·.schema.name) ++ before.catalog.current.views.map (·.definition.name)
  let newNames := next.database.tables.map (·.schema.name) ++ next.catalog.current.views.map (·.definition.name)
  let mut cached := original
  for name in oldNames.filter (fun name => !newNames.contains name) do
    cached := SQLite.SchemaHash.remove cached name
  let catalogAdditions := (newNames.filter (fun name => !oldNames.contains name)).reverse
  let creation := cached.creation ++ catalogAdditions
  -- sqlite_sequence enters the live hash before its first AUTOINCREMENT
  -- owner, while its persistent sqlite_schema row follows that owner.
  let insertions := if catalogAdditions.contains CoreAutoIncrement.sequenceName then
      CoreAutoIncrement.sequenceName :: catalogAdditions.filter (· != CoreAutoIncrement.sequenceName)
    else catalogAdditions
  for name in insertions do
    cached := SQLite.SchemaHash.add cached name
  cached := { cached with creation }
  let mut result := { next with schemaHash := some cached }
  match sql with
  | .begin => result := { result with transactionSchemaHash := some original }
  | .commit => result := { result with transactionSchemaHash := none, schemaHashSavepoints := [] }
  | .rollback =>
      let snapshot := before.transactionSchemaHash.getD original
      result := { result with
        schemaHash := some (SQLite.SchemaHash.rollback original snapshot)
        transactionSchemaHash := none
        schemaHashSavepoints := [] }
  | .savepoint name =>
      result := { result with
        transactionSchemaHash := if before.transactionSnapshot.isNone then some original else before.transactionSchemaHash
        schemaHashSavepoints := (name, original) :: before.schemaHashSavepoints }
  | .rollbackTo name =>
      let marks := before.schemaHashSavepoints.dropWhile (fun mark => mark.1.toLower != name.toLower)
      if let some mark := marks.head? then
        result := { result with
          schemaHash := some (SQLite.SchemaHash.rollback original mark.2)
          schemaHashSavepoints := marks }
  | .release name =>
      let marks := before.schemaHashSavepoints.dropWhile (fun mark => mark.1.toLower != name.toLower)
      result := { result with
        schemaHashSavepoints := marks.drop 1
        transactionSchemaHash := if next.transactionSnapshot.isNone then none else before.transactionSchemaHash }
  | .alterRenameTable oldName newName =>
      let creation := original.creation.map fun name =>
        if name.toLower == oldName.toLower then newName else name
      result := { result with schemaHash := some (SQLite.SchemaHash.reload { original with creation }) }
  | .alterAddColumn .. | .alterDropColumn .. | .alterRenameColumn .. =>
      result := { result with schemaHash := some (SQLite.SchemaHash.reload original) }
  | _ => pure ()
  return result

def executeStatement (state : Core.State) (sql : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  let state := CoreViewSQL.prepareCatalog state
  CoreViewSQL.guard state sql
  if let .pragma name argument schema := sql then
    if name.toLower == "foreign_keys" then return ← CoreForeignKey.pragma state argument schema
  let sql ← CoreGeneratedSQL.statement state sql
  let edges ← if state.foreignKeys then CoreForeignKey.edges state sql else pure []
  let cached := { state with schemaHash := some state.schemaHashValue }
  let input := if state.foreignKeys then { cached with foreignWrites := [] } else cached
  let hasRename := (CoreForeignKeyRename.request state sql source).isSome
  if hasRename then
    for view in state.catalog.current.views do
      match viewMetadataState 256 state view.definition.name with
      | .ok _ => pure ()
      | .error message => throw s!"error in view {view.definition.name}: {message}"
  let (next, results) ← executeBase input sql source
  let next ← CoreForeignKeyRename.execute state next sql source
  let next ← CoreViewRename.execute state next sql source
  let droppedColumn := match sql with | .alterDropColumn .. => true | _ => false
  if hasRename || droppedColumn then
    for view in next.catalog.current.views do
      match viewMetadataState 256 next view.definition.name with
      | .ok _ => pure ()
      | .error message =>
          let operation := if droppedColumn then "drop column" else "rename"
          throw s!"error in view {view.definition.name} after {operation}: {message}"
  unless edges.isEmpty do CoreForeignKey.requireTransition state next edges
  let next := CoreViewSQL.transition state next sql
  let next ← CoreViewSQL.orderDatabase next
  let next := schemaTransition state next sql
  return (if state.foreignKeys then { next with foreignWrites := state.foreignWrites } else next, results)

end SQLeanite.CoreDerivedSQL
