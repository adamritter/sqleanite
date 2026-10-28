import SQLeanite.CoreTriggerProgram.Scope

namespace SQLeanite.CoreTriggerProgram

/-- Scope metadata uses the same prepared source schemas as ordinary reads.
Dummy rows serve preparation only; no projected value contributes to demand. -/
def scopeFrames (state : Core.State) (contexts : List CoreExpr.Context) :
    Except String (List CoreScalarQuery.Frame) :=
  contexts.mapM fun context => do
    let declarations ← match CoreNames.table? state.database context.schema.name with
      | none => pure []
      | some table => match table.catalogSource with
          | none => pure [] | some source => source.compiledCollations
    return { context, row := List.replicate context.schema.columns.length .null, declarations }

def shadowsNew (contexts : List CoreExpr.Context) (name : String) : Bool :=
  contexts.any (fun context => (context.column? (some "new") name).isSome)

mutual

def newExpression (read : ScopedRead) : Nat → Core.State → Core.Table → List CoreScalarQuery.Frame →
    List CoreExpr.Context → Expr → Except String (List Nat)
  | 0, _, _, _, _, _ => .error "trigger column demand depth exceeded"
  | fuel + 1, state, table, parents, contexts, expression => do
      let visit := newExpression read fuel state table parents contexts
      let nested := fun sql => do
        let localFrames ← scopeFrames state contexts
        newQuery read fuel state table (localFrames ++ parents) (← CoreScalarQuery.parseQuery sql)
      match expression with
      | .column (some qualifier) name =>
          if qualifier.toLower == "new" && !shadowsNew contexts name then
            let position ← CoreSQL.column table.schema name
            return if position == table.schema.primaryKey then [] else [position]
          return []
      | .scalarSubquery sql | .existsSubquery sql => nested sql
      | .inSubquery value sql _ => return (← visit value) ++ (← nested sql)
      | .unary _ value | .isNull value _ | .collate value _ => visit value
      | .binary _ a b => return (← visit a) ++ (← visit b)
      | .call _ arguments _ => return (← arguments.toList.mapM visit).flatten
      | .inList value arguments _ _ => return (← visit value) ++ (← arguments.toList.mapM visit).flatten
      | .case_ base branches other =>
          let inputs := base.toList ++ branches.toList.flatMap (fun pair => [pair.1,pair.2]) ++ other.toList
          return (← inputs.mapM visit).flatten
      | _ => return []

def newQuery (read : ScopedRead) : Nat → Core.State → Core.Table → List CoreScalarQuery.Frame → Select →
    Except String (List Nat)
  | 0, _, _, _, _ => .error "trigger query demand depth exceeded"
  | fuel + 1, state, table, parents, query => do
      let metadata ← read true state parents { query with limit := some 0 }
      let context ← CoreCreateTableAs.contexts metadata.inputState.database metadata.inputQuery
      let values ← (CoreScalarQuery.expressions query).mapM
        (newExpression read fuel metadata.inputState table parents context.sources)
      let mut columns := values.flatten
      for source in query.sources do
        if let some sql := source.subquerySql then
          columns := columns ++ (← newQuery read fuel state table parents (← CoreScalarQuery.parseQuery sql))
      for (_,arm) in query.compounds do columns := columns ++ (← newQuery read fuel state table parents arm)
      return columns

end

def newStatement (read : ScopedRead) (state : Core.State) (table : Core.Table)
    (parents : List CoreScalarQuery.Frame) (statement : Statement) : Except String (List Nat) := do
  match statement with
  | .select query | .insertSelect _ _ query .. => newQuery read 262144 state table parents query
  | .insert _ _ rows .. =>
      return (← rows.toList.mapM fun row => do
        return (← row.toList.mapM (newExpression read 262144 state table parents [])).flatten).flatten
  | .update target alias _ condition .. | .delete target alias condition _ =>
      let stored ← tableFor state target
      let contexts : List CoreExpr.Context := [{ schema := stored.schema, rowidAliases := !stored.withoutRowid, sourceName := alias.getD target }]
      let expressions := match statement with
        | .update _ _ assignments .. => assignments.toList.map Prod.snd ++ condition.toList
        | _ => condition.toList
      return (← expressions.mapM (newExpression read 262144 state table parents contexts)).flatten
  | _ => throw "unsupported trigger column-demand statement"

def newColumns (read : ScopedRead) (state : Core.State) (table : Core.Table) (statement : Statement) :
    Except String (List Nat) := do
  let values : List Core.Value := List.replicate table.schema.columns.length .null
  let parents ← frames state table statement values values
  let mut columns := []
  for program in (programs state statement).filter (fun program => program.definition.timing == .before) do
    if let some condition := program.definition.when_ then
      columns := columns ++ (← newExpression read 262144 state table parents [] condition)
    for action in program.definition.body do columns := columns ++ (← newStatement read state table parents action)
  return columns

end SQLeanite.CoreTriggerProgram
