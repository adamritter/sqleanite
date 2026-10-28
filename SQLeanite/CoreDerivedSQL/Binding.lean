import SQLeanite.CoreJsonTable
import SQLeanite.CoreScalarQuery
import SQLeanite.CoreViewSQL
import SQLeanite.CoreWindow
import SQLeanite.CoreWithoutRowidRead

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


/-- Rebase actual typed output representations onto the rowids assigned by
private insertion. A cache entry is retained only for the same logical cell. -/
def materializeTypedRows (state : Core.State) (definitions : Array ColumnDef)
    (rows : List (List Core.Value)) (typed : List (List SQLite.ScalarValue)) :
    Except String (Core.State × String) := do
  let (next,name) ← materializeRows state definitions rows
  if typed.isEmpty then return (next,name)
  unless typed.length == rows.length do throw "typed materialization row count mismatch"
  let some table := next.database.findTable? name | throw "missing typed materialization table"
  let mut origins := []
  for (values,index) in typed.zipIdx do
    let some row := table.rows.find? (fun row => row.rowid.value == Int.ofNat (index+1))
      | throw "missing typed materialization row"
    for (value,column) in values.zipIdx do
      let some bytes := value.encodedText | continue
      unless value.textEncoding == 2 || value.textEncoding == 3 do continue
      let some (.text cell) := row.values[column]? | continue
      unless SQLite.TextEncoding.fromStorage value.textEncoding bytes == cell.bytes.toArray do continue
      origins := origins ++ [{
        table := name
        rowid := row.rowid.value
        column
        encoding := value.textEncoding
        bytes }]
  return ({ next with catalog := { next.catalog with storedTexts := origins ++ next.catalog.storedTexts } },name)

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
          let candidates := CoreJoinUsing.nameCandidates
            (context.sources.map (fun ctx => { ctx with rowidAliases := true })) qualifier name
          let visible := candidates.filter fun (i, position) =>
            match context.sources[i]? with
            | none => false
            | some ctx => !((derived.contains ctx.schema.name ||
                  (CoreNames.table? database ctx.schema.name).any (·.withoutRowid)) &&
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
      let native := state.catalog.current.textEncoding == 2 || state.catalog.current.textEncoding == 3
      let (state,metadata,result,typed) ← if !parents.isEmpty || CoreScalarQuery.has input.compoundHeight input ||
          (native && !CoreWindow.has input) then do
          let selected ← CoreScalarQuery.executePrepared compile preparing fuel state parents input
          pure (selected.inputState, selected.inputQuery, selected.result,selected.typedRows)
        else if CoreWindow.has input then do
          pure (state,query,← CoreWindow.execute state input,[])
        else do
          pure (state,query,(← CoreSQL.executeSelect state input).result,[])
      let definitions ← resultDefinitions state metadata aliases
      materializeTypedRows state definitions result.rows typed

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
            let nestedInput := { current with schemaProgram := current.schemaProgram || view.isSome }
            let (nested, inner) ← prepareWithSources nestedParents preparing fuel nestedInput nestedBindings inner
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
            current := { next with schemaProgram := current.schemaProgram }
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
      let query ← if current.internalReturning then pure query else visibleQuery current.database derived query
      current ← CoreWithoutRowidRead.prepare current query
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
      if ["index_list","index_info","index_xinfo"].contains name.toLower && !state.catalog.current.filteredIndexes.isEmpty then
        return ← CoreSchemaPragma.scopedRowsWithState state schema name (target.getD "")
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

end SQLeanite.CoreDerivedSQL
