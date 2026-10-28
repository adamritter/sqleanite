import SQLeanite.Engine.YearAndDay

namespace SQLeanite

mutual
  def evalWithDbFuel : Nat → Database → Env → Expr → Except String Value
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, env, expr => do
      evalExpr env (← resolveSubqueriesFuel fuel db env expr)

  def resolveSubqueriesFuel : Nat → Database → Env → Expr → Except String Expr
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, env, expr => match expr with
    | .column none name =>
      let (date, time, timestamp) := dateTimeStrings db.currentTime
      if nameEq name "current_date" then pure (.literal (.text date))
      else if nameEq name "current_time" then pure (.literal (.text time))
      else if nameEq name "current_timestamp" then pure (.literal (.text timestamp))
      else pure (.column none name)
    | .scalarSubquery sql => do
      let statements ← parseLegacy sql
      let width := match statements[0]? with
        | some (Statement.select query) => (selectColumnSchema db query).size
        | some (Statement.values rows) => rows[0]?.map Array.size |>.getD 0
        | _ => 0
      if width != 1 then throw s!"sub-select returns {width} columns - expected 1"
      let rows ← evalMiniQueryFuel fuel db env sql
      pure (.literal (rows[0]?.bind (·[0]?) |>.getD .null))
    | .inSubquery arg sql negated => do
      let arg ← resolveSubqueriesFuel fuel db env arg
      let statements ← parseLegacy sql
      let width := match statements[0]? with
        | some (Statement.select query) => (selectColumnSchema db query).size
        | some (Statement.values rows) => rows[0]?.map Array.size |>.getD 0
        | _ => 0
      if width != 1 then throw s!"sub-select returns {width} columns - expected 1"
      let rows ← evalMiniQueryFuel fuel db env sql
      let applyLeftAffinity ← match (← parseLegacy sql)[0]? with
        | some (Statement.select query) =>
          pure <| !(selectColumnSchema db query)[0]?.any (fun column =>
            nameEq column.declaredType "BLOB")
        | _ => pure true
      pure (Expr.inList arg (rows.filterMap (·[0]?) |>.map Expr.literal) negated applyLeftAffinity)
    | .existsSubquery sql => do
      let rows ← evalMiniQueryFuel fuel db env sql
      pure (.literal (.integer (if rows.isEmpty then 0 else 1)))
    | .unary op e => do pure (.unary op (← resolveSubqueriesFuel fuel db env e))
    | .binary op a b => do pure (.binary op (← resolveSubqueriesFuel fuel db env a) (← resolveSubqueriesFuel fuel db env b))
    | .call name args star =>
      if nameEq name "lean_check_myfunc" && !db.checkMyfuncEnabled then
        throw "no such function: myfunc()"
      else if nameEq name "implies_nonnull_row" then
        match args.toList with
        | [expression, .column _ target] =>
          pure (.literal (.integer (if expressionMentionsColumn target expression then 1 else 0)))
        | _ => throw "wrong number of arguments to function implies_nonnull_row()"
      else if nameEq name "last_insert_rowid" then
        if star || !args.isEmpty then throw "wrong number of arguments to function last_insert_rowid()"
        else pure (.literal (.integer db.lastInsertRowid))
      else if ["time", "date", "datetime"].contains name.toLower then
        match args.toList with
        | [] =>
          let (date, time, timestamp) := dateTimeStrings db.currentTime
          pure (.literal (.text (if nameEq name "time" then time
            else if nameEq name "date" then date else timestamp)))
        | [.literal (.text argument)] =>
          if nameEq argument "now" then
            let (date, time, timestamp) := dateTimeStrings db.currentTime
            pure (.literal (.text (if nameEq name "time" then time
              else if nameEq name "date" then date else timestamp)))
          else do pure (.call name (← args.mapM (resolveSubqueriesFuel fuel db env)) star)
        | _ => do pure (.call name (← args.mapM (resolveSubqueriesFuel fuel db env)) star)
      else if nameEq name "lean_dqs" then
        match args.toList with
        | [.literal (.text identifier)] =>
          match resolveColumn env none identifier with
          | .ok value => pure (.literal value)
          | .error message => if message.startsWith "no such column: " && db.doubleQuotedStrings then
              pure (.literal (.text identifier))
            else if message.startsWith "no such column: " then
              throw s!"no such column: \"{identifier}\" - should this be a string literal in single-quotes?"
            else throw message
        | _ => throw "malformed double-quoted string expression"
      else do pure (.call name (← args.mapM (resolveSubqueriesFuel fuel db env)) star)
    | .isNull e n => do pure (.isNull (← resolveSubqueriesFuel fuel db env e) n)
    | .inList e values n applyAffinity => do
      pure (.inList (← resolveSubqueriesFuel fuel db env e) (← values.mapM (resolveSubqueriesFuel fuel db env)) n applyAffinity)
    | .collate e name => do pure (.collate (← resolveSubqueriesFuel fuel db env e) name)
    | .case_ base branches else_ => do
      let base ← base.mapM (resolveSubqueriesFuel fuel db env)
      let branches ← branches.mapM fun (a, b) => do
        pure (← resolveSubqueriesFuel fuel db env a, ← resolveSubqueriesFuel fuel db env b)
      let else_ ← else_.mapM (resolveSubqueriesFuel fuel db env)
      pure (.case_ base branches else_)
    | e => pure e

  def evalMiniQueryFuel : Nat → Database → Env → String →
      Except String (Array (Array Value))
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, outer, sql => do
    let statements ← parseLegacy sql
    match statements[0]? with
    | some (Statement.select query) => evalMiniSelectFuel fuel db outer query
    | some (Statement.values rows) => rows.mapM fun row => row.mapM (evalWithDbFuel fuel db outer)
    | _ => throw "subquery must be a SELECT or VALUES"

  def evalMiniSelectFuel : Nat → Database → Env → Select →
      Except String (Array (Array Value))
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, outer, query => do
    if let some expressionRows := query.valueRows then
      let mut result ← expressionRows.mapM fun row => row.mapM (evalWithDbFuel fuel db outer)
      let width := query.columns.size
      let collations := (selectColumnSchema db query).map (·.collation)
      unless result.all (fun row => row.size == width) do
        throw "all VALUES must have the same number of terms"
      for (operation, right) in query.compounds do
        let next ← evalMiniSelectFuel fuel db outer right
        unless (selectColumnSchema db right).size == width && next.all (fun row => row.size == width) do
          throw s!"SELECTs to the left and right of {operation.sqlName} do not have the same number of result columns"
        result := combineCompoundRowsCollated collations operation result next
        unless operation == .unionAll do result := sortRowsCollated collations result
      if !query.orderBy.isEmpty then
        let names := selectColumnNames db query
        let keys ← compoundOrderKeys db query names
        result := sortOrderedValueRows keys result
      return result.extract query.offset (query.offset + query.limit.getD result.size)
    -- Hidden outer bindings remain addressable when no local binding matches,
    -- while local bindings correctly win unqualified-name resolution.
    let hiddenOuter := outer.map Binding.outerScoped
    let mut envs : Array Env := #[hiddenOuter]
    let mut template := hiddenOuter
    for ref in query.sources do
      let table ← if let some nestedSql := ref.subquerySql then
          let rows ← evalMiniQueryFuel fuel db outer nestedSql
          let nestedStatements ← parseLegacy nestedSql
          let columns ← match nestedStatements[0]? with
            | some (Statement.select nested) => pure (selectColumnSchema db nested)
            | some (Statement.values values) => pure ((valuesColumnNames
                (values[0]?.map Array.size |>.getD 0)).map fun name => ({ name } : Column))
            | _ => throw "derived table must be a SELECT or VALUES"
          let columns := applyColumnAliases ref.columnAliases columns
          let stored := rows.mapIdx fun i values => StoredRow.mk (Int.ofNat (i + 1)) values
          let rowStore ← RowStore.checked stored columns.size
          pure (Table.mk ref.name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[])
        else if let some view := findView? db ref.name then
          evalViewTableFuel fuel db ref.name view
        else if nameEq ref.name "sqlite_master" || nameEq ref.name "sqlite_schema" then
          let columns : Array Column := #[{ name := "type" }, { name := "name" }, { name := "tbl_name" },
            { name := "rootpage" }, { name := "sql" }]
          let viewRows := db.views.toArray.mapIdx fun i view => StoredRow.mk (Int.ofNat (i + 1))
            #[.text "view", .text view.name, .text view.name, .integer 0, .text view.sourceSql]
          let tableRows := db.tables.toArray.mapIdx fun i t => StoredRow.mk
            (Int.ofNat (db.views.length + i + 1))
            #[.text "table", .text t.name, .text t.name, .integer (Int.ofNat (i + 2)),
              .text s!"CREATE TABLE {t.name}"]
          let triggerRows := db.triggers.toArray.mapIdx fun i trigger => StoredRow.mk
            (Int.ofNat (db.views.length + db.tables.length + i + 1))
            #[.text "trigger", .text trigger.name, .text trigger.table, .integer 0,
              .text trigger.sourceSql]
          let indexRows := db.indexes.toArray.mapIdx fun i index => StoredRow.mk
            (Int.ofNat (db.views.length + db.tables.length + db.triggers.length + i + 1))
            #[.text "index", .text index.name, .text index.table, .integer 0, .text index.sql]
          let stored := viewRows ++ tableRows ++ triggerRows ++ indexRows
          let rowStore ← RowStore.checked stored columns.size
          pure (Table.mk ref.name columns rowStore (Int.ofNat (stored.size + 1)) #[] #[])
        else optionOr (findTable? db ref.name) s!"no such table: {ref.name}"
      if let some alias := ref.alias then
        if let some duplicate := table.columns.find? (fun column => template.any (fun binding =>
            !binding.hidden && nameEq binding.alias alias && nameEq binding.column column.name)) then
          throw s!"ambiguous column name: {alias}.{duplicate.name}"
      if ref.naturalJoin && (ref.joinOn.isSome || !ref.usingColumns.isEmpty) then
        throw "a NATURAL join may not have an ON or USING clause"
      let leftTemplate := template
      for column in ref.usingColumns do
        unless leftTemplate.any (fun binding => !binding.hidden && nameEq binding.column column) &&
            table.columns.any (fun candidate => nameEq candidate.name column) do
          throw s!"cannot join using column {column} - column not present in both tables"
      let naturalTemplateColumns := if ref.naturalJoin then table.columns.filterMap fun column =>
        if leftTemplate.any (fun left => !left.hidden && nameEq left.column column.name)
        then some column.name else none
        else #[]
      let templateUsingColumns := ref.usingColumns ++ naturalTemplateColumns
      let nullRow : StoredRow := { rowid := 0, values := table.columns.map fun _ => .null }
      let rightTemplate := (miniBindings ref table nullRow).map fun binding =>
        if templateUsingColumns.any (nameEq binding.column) then { binding with hidden := true }
        else binding
      let mut next := #[]
      let mut matchedRight := Std.HashSet.emptyWithCapacity (capacity := table.rows.size)
      for baseEnv in envs do
        let mut matched := false
        let naturalColumns := if ref.naturalJoin then table.columns.filterMap fun column =>
          if baseEnv.any (fun left => !left.hidden && nameEq left.column column.name)
          then some column.name else none
          else #[]
        let usingColumns := ref.usingColumns ++ naturalColumns
        for rowIndex in [:table.rows.size] do
          let row := table.rows[rowIndex]!
          let right := miniBindings ref table row
          let combined := baseEnv ++ right
          let usingMatches ← usingColumns.allM (joinColumnMatches baseEnv right)
          let onMatches ← match ref.joinOn with
            | none => pure true
            | some condition => pure ((← evalWithDbFuel fuel db combined condition).truth == .true)
          if usingMatches && onMatches then
            let projectedRight := right.map fun binding =>
              if usingColumns.any (nameEq binding.column) then { binding with hidden := true }
              else binding
            next := next.push (baseEnv ++ projectedRight)
            matched := true
            matchedRight := matchedRight.insert rowIndex
        if ref.leftJoin && !matched then
          let projectedRight := (miniBindings ref table nullRow).map fun binding =>
            if usingColumns.any (nameEq binding.column) then { binding with hidden := true }
            else binding
          next := next.push (baseEnv ++ projectedRight)
      if ref.rightJoin then
        for rowIndex in [:table.rows.size] do
          unless matchedRight.contains rowIndex do
            let right := miniBindings ref table table.rows[rowIndex]!
            let projectedRight := right.map fun binding =>
              if templateUsingColumns.any (nameEq binding.column) then { binding with hidden := true }
              else binding
            next := next.push (leftTemplate.map (fun binding => { binding with value := .null }) ++ projectedRight)
      envs := next
      template := leftTemplate ++ rightTemplate
    let mut filtered := #[]
    for candidate in envs do
      let keep ← match query.where_ with
        | none => pure true
        | some condition => do pure ((← evalWithDbFuel fuel db candidate condition).truth == .true)
      if keep then filtered := filtered.push candidate
    let isAggregate := !query.groupBy.isEmpty || query.columns.any (fun col => miniHasAggregate col.expr) ||
      query.having.any miniHasAggregate
    let mut groupedInput := #[]
    for env in filtered do
      let mut enriched := env
      for column in query.columns do
        if let some alias := column.alias then
          unless miniHasAggregate column.expr || enriched.any (fun binding =>
              binding.hidden && nameEq binding.column alias) do
            let value ← evalWithDbFuel fuel db env column.expr
            enriched := enriched.push (Binding.mk "" "" alias value true 0 "binary" "LEAN_HIDDEN")
      groupedInput := groupedInput.push enriched
    let mut groups : Array (Array Env) := #[]
    if query.groupBy.isEmpty then groups := #[groupedInput]
    else
      let mut keys : Array (Array Value) := #[]
      for env in groupedInput do
        let key ← query.groupBy.mapM fun term =>
          match term with
          | .literal (.integer index) =>
            if index > 0 && index.toNat <= query.columns.size then
              match query.columns[index.toNat - 1]!.expr with
              | .star qualifier => pure <| env.find? (fun binding => binding.depth == 0 &&
                  (!binding.hidden || (qualifier.isSome && binding.declaredType != "LEAN_HIDDEN")) &&
                  qualifier.all (fun q => nameEq q binding.alias || nameEq q binding.table))
                |>.map (·.value) |>.getD .null
              | expression => evalWithDbFuel fuel db env expression
            else evalWithDbFuel fuel db env term
          | _ => evalWithDbFuel fuel db env term
        match keys.findIdx? (· == key) with
        | some index => groups := groups.set! index (groups[index]!.push env)
        | none => keys := keys.push key; groups := groups.push #[env]
      let preserveInputOrder := query.groupBy.any fun term => term matches .unary .neg _
      unless preserveInputOrder do groups := (sortValueKeyed (keys.zip groups)).map (·.2)
    let baseRows ← if isAggregate then
      let mut rows := #[]
      for group in groups do
        unless group.isEmpty && !query.groupBy.isEmpty do
          let mut row := #[]
          for column in query.columns do
            match column.expr with
            | .star qualifier =>
              let representative := group[0]?.getD #[]
              for binding in representative do
                if binding.depth == 0 &&
                    (!binding.hidden || (qualifier.isSome && binding.declaredType != "LEAN_HIDDEN")) &&
                    qualifier.all (fun q => nameEq q binding.alias || nameEq q binding.table) then
                  row := row.push binding.value
            | expression => row := row.push (← evalMiniAggregateFuel fuel db group expression)
          let mut aliases : Env := #[]
          for i in [:query.columns.size] do
            if let some alias := query.columns[i]!.alias then
              aliases := aliases.push (Binding.mk "" "" alias (row[i]?.getD .null)
                true 0 "binary" "LEAN_HIDDEN")
          let withAliases := group.map fun env => env ++ aliases
          let keep ← match query.having with
            | none => pure true
            | some condition =>
              pure ((← evalMiniAggregateFuel fuel db withAliases condition).truth == .true)
          if keep then rows := rows.push row
      pure rows
    else
      filtered.mapM fun e => do
        let mut row := #[]
        for col in query.columns do
          match col.expr with
          | .star qualifier =>
            unless e.any (fun b => b.depth == 0 &&
                (!b.hidden || (qualifier.isSome && b.declaredType != "LEAN_HIDDEN")) &&
                qualifier.all (fun q => nameEq q b.alias || nameEq q b.table)) do
              throw "no tables specified"
            for b in e do
              if b.depth == 0 && (!b.hidden || (qualifier.isSome && b.declaredType != "LEAN_HIDDEN")) &&
                  qualifier.all (fun q => nameEq q b.alias || nameEq q b.table) then
                row := row.push b.value
          | expr => row := row.push (← evalWithDbFuel fuel db e expr)
        pure row
    let mut result := baseRows
    let collations := (selectColumnSchema db query).map (·.collation)
    let mut aggregateOrderHandled := false
    if query.compounds.isEmpty && isAggregate && query.having.isNone && !query.orderBy.isEmpty then
      let names := selectColumnNames db query
      let mut keyed := #[]
      for index in [:min result.size groups.size] do
        let values := result[index]!
        let group := groups[index]!
        let representative := group[0]?.getD #[]
        let keys ← query.orderBy.mapM fun term => do
          let value ← match term.expr with
            | .literal (.integer ordinal) =>
              if ordinal > 0 && ordinal.toNat <= values.size then pure values[ordinal.toNat - 1]!
              else throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
            | .column none name => match names.findIdx? (nameEq name) with
              | some output => pure values[output]!
              | none => evalMiniAggregateFuel fuel db group term.expr
            | expression => evalMiniAggregateFuel fuel db group expression
          pure (value, term.descending,
            term.expr.explicitOrderCollation?.getD (term.expr.collationIn representative), term.nullsFirst)
        keyed := keyed.push { values, keys }
      result := sortKeyedRows keyed
      aggregateOrderHandled := true
    if query.compounds.isEmpty && !query.orderBy.isEmpty && !isAggregate then
      let names := selectColumnNames db query
      let mut keyed := #[]
      for index in [:result.size] do
        let env := filtered[index]!
        let values := result[index]!
        let keys ← query.orderBy.mapM fun term => do
          let value ← match term.expr with
            | .literal (.integer ordinal) =>
              if ordinal > 0 && ordinal.toNat <= values.size then pure values[ordinal.toNat - 1]!
              else throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
            | .unary .plus (.literal (.integer ordinal)) =>
              if ordinal > 0 && ordinal.toNat <= values.size then pure values[ordinal.toNat - 1]!
              else throw s!"1st ORDER BY term out of range - should be between 1 and {values.size}"
            | .column none name => match names.findIdx? (nameEq name) with
              | some output => pure values[output]!
              | none => evalWithDbFuel fuel db env term.expr
            | expression => evalWithDbFuel fuel db env expression
          let inherited := term.expr.collationIn env
          pure (value, term.descending, term.expr.explicitOrderCollation?.getD inherited, term.nullsFirst)
        keyed := keyed.push { values, keys }
      result := sortKeyedRows keyed
    if query.distinct then
      let mut unique := #[]
      for row in result do
        unless containsCollated collations unique row do unique := unique.push row
      result := unique
      if query.orderBy.isEmpty && shouldSortDistinctByIndex db query then
        result := sortRowsCollated collations result
    for (operation, right) in query.compounds do
      let next ← evalMiniSelectFuel fuel db outer right
      if (selectColumnSchema db query).size != (selectColumnSchema db right).size then
        throw s!"SELECTs to the left and right of {operation.sqlName} do not have the same number of result columns"
      result := combineCompoundRowsCollated collations operation result next
      unless operation == .unionAll do result := sortRowsCollated collations result
    if !query.orderBy.isEmpty && (!query.compounds.isEmpty || (isAggregate && !aggregateOrderHandled)) then
      let names := selectColumnNames db query
      let keys ← compoundOrderKeys db query names
      result := sortOrderedValueRows keys result
    pure (result.extract query.offset (query.offset + query.limit.getD result.size))

  def evalMiniAggregateFuel : Nat → Database → Array Env → Expr → Except String Value
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, envs, expr => do
    match expr with
    | .call name args star =>
      let distinct := isDistinctAggregateName name
      let lname := aggregateFunctionName name
      if distinct && args.size != 1 then
        throw "DISTINCT aggregates must have exactly one argument"
      else if lname == "count" then
        if star || args.isEmpty then pure (.integer envs.size)
        else if args.size == 1 then
          let mut values ← envs.mapM fun env => evalWithDbFuel fuel db env args[0]!
          if distinct then
            values := deduplicateNonNullValues
              (args[0]!.collationIn (envs[0]?.getD #[])) values
          pure (.integer (values.filter (fun value => !(value matches .null))).size)
        else throw "wrong number of arguments to function count()"
      else if ["sum", "total", "avg"].contains lname && args.size == 1 then
        let mut values ← envs.mapM fun env => evalWithDbFuel fuel db env args[0]!
        if distinct then
          values := deduplicateNonNullValues
            (args[0]!.collationIn (envs[0]?.getD #[])) values
        let numbers := values.filterMap Value.toFloat?
        if numbers.isEmpty then pure (if lname == "total" then .real 0.0 else .null)
        else
          let total := numbers.foldl (· + ·) 0.0
          if lname == "avg" then pure (.real (total / numbers.size.toFloat))
          else if lname == "sum" && values.all (fun value => value matches .integer _) then
            pure (.integer (values.foldl (init := 0) fun sum value => sum + value.toInt?.getD 0))
          else pure (.real total)
      else if (lname == "min" || lname == "max") && args.size == 1 then
        let mut values ← envs.mapM fun env => evalWithDbFuel fuel db env args[0]!
        if distinct then
          values := deduplicateNonNullValues
            (args[0]!.collationIn (envs[0]?.getD #[])) values
        pure (scalarMinMax (lname == "max") (values.filter fun value => !(value matches .null)))
      else
        let values ← args.mapM (evalMiniAggregateFuel fuel db envs)
        evalExpr #[] (.call name (values.map Expr.literal) star)
    | .binary op left right =>
      let left ← evalMiniAggregateFuel fuel db envs left
      let right ← evalMiniAggregateFuel fuel db envs right
      evalExpr #[] (.binary op (.literal left) (.literal right))
    | .unary op argument =>
      evalExpr #[] (.unary op (.literal (← evalMiniAggregateFuel fuel db envs argument)))
    | .isNull argument negated =>
      evalExpr #[] (.isNull (.literal (← evalMiniAggregateFuel fuel db envs argument)) negated)
    | .collate argument name =>
      evalExpr #[] (.collate (.literal (← evalMiniAggregateFuel fuel db envs argument)) name)
    | other => evalWithDbFuel fuel db (envs[0]?.getD #[]) other

  def evalViewTableFuel : Nat → Database → String → View → Except String Table
    | 0, _, _, _ => throw "query evaluation nested too deeply"
    | fuel + 1, db, tableName, view => do
    unless db.viewsEnabled || view.temporary do throw s!"access to view \"{view.name}\" prohibited"
    if view.query.callsDirectOnly then throw "unsafe use of testdirectonly()"
    if db.viewStack.length + 1 >= db.viewDepthLimit then
      throw "VIEWs and/or subqueries nested too deep"
    if db.viewStack.any (nameEq view.name) then throw s!"view {view.name} is circularly defined"
    let nestedDb := { db with
      viewStack := view.name :: db.viewStack
      ignoreTempViews := !view.temporary }
    let rows ← match evalMiniSelectFuel fuel nestedDb #[] view.query with
      | .ok rows => pure rows
      | .error message =>
        if !view.temporary && message.startsWith "no such table: " &&
            !(message.drop "no such table: ".length).toString.toList.contains '.' then
          throw ("no such table: main." ++ (message.drop "no such table: ".length).toString)
        else throw message
    let inferred := selectColumnSchema nestedDb view.query
    let columns := match view.columns with
      | none => inferred
      | some names => inferred.mapIdx fun i column => { column with name := names[i]?.getD column.name }
    let columns := deduplicateColumns columns
    unless rows.all (fun row => row.size == columns.size) do
      throw s!"expected {columns.size} columns for view {view.name}"
    let stored := rows.mapIdx fun i values => StoredRow.mk (Int.ofNat (i + 1)) values
    let rowStore ← RowStore.checked stored columns.size
    pure (Table.mk tableName columns rowStore (Int.ofNat (stored.size + 1)) #[] #[])
end

def evaluationDepth (db : Database) : Nat := db.viewDepthLimit + 2001

theorem evaluationDepth_exceeds_view_limit (db : Database) :
    db.viewDepthLimit < evaluationDepth db := by
  unfold evaluationDepth
  omega

def evalWithDb (db : Database) (env : Env) (expression : Expr) : Except String Value :=
  evalWithDbFuel (evaluationDepth db + expression.height) db env expression

end SQLeanite
