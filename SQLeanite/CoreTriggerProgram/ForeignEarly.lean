import SQLeanite.CoreTriggerProgram.ForeignCounter

namespace SQLeanite.CoreTriggerProgram.ForeignEarly

/-- Native replacement code can require a statement journal even when no
existing row conflicts. An omitted rowid avoids that primary-key check; an
explicit NULL still supplies ipkColumn and compiles the replacement branch. -/
def replacementWrites (table : Core.Table) (columns : Option (Array String))
    (rows : Array (Array Expr)) (action : ConflictAction) : Bool :=
  let explicitKey := rows.any (fun row => !row.isEmpty) && match columns with
    | none => table.schema.visibleColumnIndices.contains table.schema.primaryKey
    | some names => names.any fun name => table.schema.column? name == some table.schema.primaryKey
  let declaredIndex := table.schema.hasHiddenRowid && table.schema.declaredPrimaryKey?.isSome
  if action == .replace then explicitKey || declaredIndex || table.indexes.any (·.unique)
  else action == .default && CoreDefaultConflict.primaryPolicy table.schema == .replace &&
    (if table.schema.hasHiddenRowid then declaredIndex else explicitKey)

/-- The native single-write INSERT path has no statement journal: immediate
parent lookup failure halts before OP_Insert. SELECT/multiple/RETURNING/program
and compiled replacement-write paths use the statement counter boundary. -/
def eligible (state : Core.State) (statement : Statement) : Bool :=
  state.foreignKeys && state.triggerDepth == 0 && match statement with
    | .insert target columns rows action outputs =>
        rows.size == 1 && outputs.isEmpty && (programs state statement).isEmpty &&
          ((CoreNames.table? state.database target).any fun table =>
            !replacementWrites table columns rows action &&
              !(action == .replace && state.catalog.current.filteredIndexes.any
                (fun index => index.owner.toLower == table.schema.name.toLower && index.definition.unique)))
    | _ => false

/-- Reuse the actual checked candidate without publishing its temporary state.
The early native branch checks child lookups before any parent scan can cancel
an old orphan. Self-referencing NEW keys and NULLs retain ordinary FK rules. -/
def require (base : Executor) (capture : Statement → Except String Statement)
    (state : Core.State) (table : Core.Table) (statement : Statement) : Except String Unit := do
  let (_,results) ← base state (← capture statement) ""
  if (results.map (·.changes)).sum == 0 then return ()
  let [image] := results.flatMap (·.rows) | throw "early FK check lost its accepted candidate"
  let values := image.take table.schema.columns.length
  let edges ← CoreForeignKey.edges state statement
  for edge in edges do
    if edge.child.toLower != table.schema.name.toLower then continue
    let value := values[edge.column]?.getD .null
    let self := edge.parent.toLower == table.schema.name.toLower &&
      ForeignCounter.equal edge value (values[edge.parentColumn]?.getD .null)
    if !self && ForeignCounter.missing state.database edge value then
      throw "FOREIGN KEY constraint failed"

theorem eligible_disabled (state : Core.State) (statement : Statement)
    (disabled : state.foreignKeys = false) : eligible state statement = false := by
  simp [eligible, disabled]

end SQLeanite.CoreTriggerProgram.ForeignEarly
