import SQLeanite.CoreEngine.ChooseExtremeEqLeftOrRight

namespace SQLeanite
namespace Core

theorem executeUncertifiedQueryWithCandidates_eq_execute (state : State)
    (tableName : String) (query : Query) (candidates : List Row) :
    executeUncertifiedQueryWithCandidates state tableName query candidates =
      execute state (.query tableName query) := by
  unfold executeUncertifiedQueryWithCandidates
  cases found : state.database.findTable? tableName with
  | none =>
      simp only [execute, found]
      rfl
  | some table =>
      simp only [found]
      split
      next same =>
        rw [same]
        simp only [execute, found]
        rfl
      next different => rfl

theorem execute_createTable_exact {state next : State} {schema : Schema}
    {result : Result}
    (success : execute state (.createTable schema) = .ok (next, result)) :
    ∃ table,
      emptyTable schema = .ok table ∧
      next.database.tables = table :: state.database.tables ∧
      next.database.findTable? schema.name = some table ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = {} ∧
      ∀ other, other ≠ schema.name →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases created : state.database.createTable schema with
  | error message =>
      simp [created, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | ok database =>
      simp [created, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
      rcases success with ⟨stateEqual, resultEqual⟩
      subst next
      subst result
      rcases Database.createTable_exact created with
        ⟨table, empty, tables⟩
      have tableSchema : table.schema = schema := by
        apply (Table.rebuild_exact (by simpa [emptyTable] using empty)).1
      refine ⟨table, empty, tables, ?_, rfl, rfl, ?_⟩
      · unfold Database.findTable?
        rw [tables]
        simp [tableSchema]
      · intro other different
        unfold Database.findTable?
        rw [tables]
        simp [tableSchema, Ne.symm different]

theorem execute_createIndex_exact {state next : State}
    {tableName : String} {index : Index} {result : Result}
    (success : execute state (.createIndex tableName index) =
      .ok (next, result)) :
    ∃ table replacement,
      state.database.findTable? tableName = some table ∧
      replacement.schema = table.schema ∧
      replacement.indexes = table.indexes ++ [index] ∧
      replacement.rows = table.rows ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = {} ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases modified : state.database.modifyTable tableName
      (fun table => table.addIndex index) with
  | error message =>
      simp [modified, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | ok database =>
      simp [modified, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
      rcases success with ⟨stateEqual, resultEqual⟩
      subst next
      subst result
      rcases Database.modifyTable_exact modified with
        ⟨table, replacement, found, added, updated⟩
      rcases Table.addIndex_exact added with
        ⟨replacementSchema, replacementIndexes, replacementRows⟩
      have replacementName : replacement.schema.name = tableName :=
        (congrArg Schema.name replacementSchema).trans
          (findTable?_some_schemaName found)
      refine ⟨table, replacement, found, replacementSchema,
        replacementIndexes, replacementRows, ?_, rfl, rfl, ?_⟩
      · exact Database.updateTable_target found replacementName updated
      · intro other different
        exact Database.updateTable_frame updated other fun equal =>
          different (equal.trans replacementName)

/-- The exact effect of a successful live `INSERT`.

`freshRowid` and the declared-key freshness are checked by `insertValues` and are
now carried up: an `INSERT` is an insert, not an upsert, and downstream theorems
can say so. `execute_replace_exact` deliberately does *not* carry them, which is
where the two statements differ. -/
theorem execute_insert_exact {state next : State} {tableName : String}
    {values : List Value} {result : Result}
    (success : execute state (.insert tableName values) = .ok (next, result)) :
    ∃ table replacement row,
      state.database.findTable? tableName = some table ∧
      table.createRow values = .ok row ∧
      row.WellFormed table.schema ∧
      (∀ existing ∈ table.rows, existing.rowid.value ≠ row.rowid.value) ∧
      table.findDeclaredPrimary? row = none ∧
      replacement.rows = orderedUpsert row table.rows ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes := 1 } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases inserted : table.insertValues values with
      | error message =>
          simp [found, inserted, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok replacement =>
          cases updated : state.database.updateTable replacement with
          | error message =>
              simp [found, inserted, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok database =>
              simp [found, inserted, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              rcases success with ⟨stateEqual, resultEqual⟩
              subst next
              subst result
              rcases Table.insertValues_exact inserted with
                ⟨row, created, valid, freshRowid, declaredFresh, replacementRows⟩
              have replacementName : replacement.schema.name = tableName :=
                (congrArg Schema.name (Table.insertValues_schema inserted)).trans
                  (findTable?_some_schemaName found)
              refine ⟨table, replacement, row, rfl, created, valid, freshRowid,
                declaredFresh, replacementRows, ?_, rfl, rfl, ?_⟩
              · exact Database.updateTable_target found replacementName updated
              · intro other different
                exact Database.updateTable_frame updated other fun equal =>
                  different (equal.trans replacementName)

theorem execute_replace_exact {state next : State} {tableName : String}
    {values : List Value} {result : Result}
    (success : execute state (.replace tableName values) = .ok (next, result)) :
    ∃ table replacement row,
      state.database.findTable? tableName = some table ∧
      table.createReplacementRow values = .ok row ∧
      replacement.rows = orderedUpsert row table.rows ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes := 1 } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases replaced : table.replaceValues values with
      | error message =>
          simp [found, replaced, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok replacement =>
          cases updated : state.database.updateTable replacement with
          | error message =>
              simp [found, replaced, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok database =>
              simp [found, replaced, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              rcases success with ⟨stateEqual, resultEqual⟩
              subst next
              subst result
              rcases Table.replaceValues_rows replaced with
                ⟨row, created, replacementRows⟩
              have replacementName : replacement.schema.name = tableName :=
                (congrArg Schema.name
                  (Table.replaceValues_schema replaced)).trans
                  (findTable?_some_schemaName found)
              refine ⟨table, replacement, row, rfl, created,
                replacementRows, ?_, rfl, rfl, ?_⟩
              · exact Database.updateTable_target found replacementName updated
              · intro other different
                exact Database.updateTable_frame updated other fun equal =>
                  different (equal.trans replacementName)

theorem execute_deleteWhere_exact {state next : State} {tableName : String}
    {predicate : Option Predicate} {result : Result}
    (success : execute state (.deleteWhere tableName predicate) =
      .ok (next, result)) :
    ∃ table replacement,
      state.database.findTable? tableName = some table ∧
      replacement.rows = table.rows.filter
        (fun row => !selects predicate row) ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes := table.rows.length - replacement.rows.length } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases retained : table.retainRows (fun row => !selects predicate row) with
      | error message =>
          simp [found, retained, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok replacement =>
          cases updated : state.database.updateTable replacement with
          | error message =>
              simp [found, retained, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok database =>
              simp [found, retained, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              rcases success with ⟨stateEqual, resultEqual⟩
              subst next
              subst result
              have replacementName : replacement.schema.name = tableName :=
                (congrArg Schema.name
                  (Table.retainRows_schema retained)).trans
                  (findTable?_some_schemaName found)
              refine ⟨table, replacement, rfl,
                Table.retainRows_exact retained, ?_, rfl, rfl, ?_⟩
              · exact Database.updateTable_target found replacementName updated
              · intro other different
                exact Database.updateTable_frame updated other fun equal =>
                  different (equal.trans replacementName)

theorem execute_updateWhere_exact {state next : State} {tableName : String}
    {assignments : List (Nat × Value)} {predicate : Option Predicate}
    {result : Result}
    (success : execute state (.updateWhere tableName assignments predicate) =
      .ok (next, result)) :
    ∃ table replacement changes,
      state.database.findTable? tableName = some table ∧
      table.updateWhere assignments predicate = .ok (replacement, changes) ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases changed : table.updateWhere assignments predicate with
      | error message =>
          simp [found, changed, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok outcome =>
          rcases outcome with ⟨replacement, changes⟩
          cases updated : state.database.updateTable replacement with
          | error message =>
              simp [found, changed, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok database =>
              simp [found, changed, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              rcases success with ⟨stateEqual, resultEqual⟩
              subst next
              subst result
              have replacementName : replacement.schema.name = tableName :=
                (congrArg Schema.name
                  (Table.updateWhere_schema changed)).trans
                  (findTable?_some_schemaName found)
              refine ⟨table, replacement, changes, rfl, changed, ?_, rfl,
                rfl, ?_⟩
              · exact Database.updateTable_target found replacementName updated
              · intro other different
                exact Database.updateTable_frame updated other fun equal =>
                  different (equal.trans replacementName)

theorem execute_query_exact {state next : State} {tableName : String}
    {query : Query} {result : Result}
    (success : execute state (.query tableName query) = .ok (next, result)) :
    ∃ table, state.database.findTable? tableName = some table ∧
      next = state ∧ result.rows = query.eval table.rows := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      change Except.error _ = Except.ok _ at success
      contradiction
  | some table =>
      simp only [found] at success
      have pairEqual := Except.ok.inj success
      injection pairEqual with stateEqual resultEqual
      subst next
      subst result
      -- The executor now runs the index plan; the observable spec is still the
      -- full scan, and stays true because planning is semantics-preserving.
      have planned := Query.eval_plannedRows table query.optimize
      have resultExact : query.optimize.eval (table.plannedRows query.optimize) =
          query.eval table.rows := by
        calc
          _ = query.optimize.eval table.rows := planned
          _ = query.eval table.rows := Query.eval_optimize query table.rows
      exact ⟨table, rfl, rfl, resultExact⟩

theorem execute_count_exact {state next : State} {tableName : String}
    {target : CountTarget} {predicate : Option Predicate} {result : Result}
    (success : execute state (.count tableName target predicate) = .ok (next, result)) :
    ∃ table count,
      state.database.findTable? tableName = some table ∧
      countInteger (countRows target predicate table.rows) = .ok count ∧
      next = state ∧ result.rows = [[.integer count]] ∧
      count.value = Int.ofNat (countRows target predicate table.rows) := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      change Except.error _ = Except.ok _ at success
      contradiction
  | some table =>
      simp only [found] at success
      cases counted : countInteger (countRows target predicate table.rows) with
      | error message =>
          simp [counted] at success
      | ok count =>
          simp [counted] at success
          rcases success with ⟨stateEqual, resultEqual⟩
          subst next
          subst result
          exact ⟨table, count, rfl, counted, rfl, rfl,
            countInteger_exact counted⟩

theorem execute_group_exact {state next : State} {tableName : String}
    {query : GroupQuery} {result : Result}
    (success : execute state (.group tableName query) = .ok (next, result)) :
    ∃ table, state.database.findTable? tableName = some table ∧
      query.eval table.rows = .ok result.rows ∧ next = state := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      contradiction
  | some table =>
      simp only [found] at success
      cases evaluated : query.eval table.rows with
      | error message => simp [evaluated] at success
      | ok rows =>
          simp [evaluated] at success
          rcases success with ⟨stateEqual, resultEqual⟩
          subst next
          subst result
          exact ⟨table, rfl, evaluated, rfl⟩

theorem execute_sum_exact {state next : State} {tableName : String}
    {column : Nat} {predicate : Option Predicate} {result : Result}
    (success : execute state (.sum tableName column predicate) = .ok (next, result)) :
    ∃ table value, state.database.findTable? tableName = some table ∧
      sumColumn column (table.rows.filter (selects predicate)) = .ok value ∧
      next = state ∧ result.rows = [[value]] := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      contradiction
  | some table =>
      simp only [found] at success
      cases summed : sumColumn column (table.rows.filter (selects predicate)) with
      | error message => simp [summed] at success
      | ok value =>
          simp [summed] at success
          rcases success with ⟨stateEqual, resultEqual⟩
          subst next
          subst result
          exact ⟨table, value, rfl, summed, rfl, rfl⟩

theorem execute_extreme_exact {state next : State} {tableName : String}
    {minimum : Bool} {column : Nat} {predicate : Option Predicate}
    {result : Result}
    (success : execute state (.extreme tableName minimum column predicate) =
      .ok (next, result)) :
    ∃ table, state.database.findTable? tableName = some table ∧
      next = state ∧ result.rows = [[extremeColumn minimum column
        (table.rows.filter (selects predicate))]] := by
  simp only [execute] at success
  cases found : state.database.findTable? tableName with
  | none =>
      rw [found] at success
      contradiction
  | some table =>
      simp [found] at success
      rcases success with ⟨stateEqual, resultEqual⟩
      subst next
      subst result
      exact ⟨table, rfl, rfl, rfl⟩

theorem execute_join_exact {state next : State} {leftName rightName : String}
    {query : CoreJoin.Query} {result : Result}
    (success : execute state (.join leftName rightName query) = .ok (next, result)) :
    ∃ left right, state.database.findTable? leftName = some left ∧
      state.database.findTable? rightName = some right ∧ next = state ∧
      result.rows = query.eval left.rows right.rows := by
  simp only [execute] at success
  cases leftFound : state.database.findTable? leftName with
  | none =>
      rw [leftFound] at success
      change Except.error _ = Except.ok _ at success
      contradiction
  | some left =>
      simp only [leftFound, Option.bind_eq_bind, Option.bind] at success
      cases rightFound : state.database.findTable? rightName with
      | none =>
          rw [rightFound] at success
          change Except.error _ = Except.ok _ at success
          contradiction
      | some right =>
        simp only [rightFound] at success
        have pairEqual := Except.ok.inj success
        injection pairEqual with stateEqual resultEqual
        subst next
        subst result
        exact ⟨left, right, rfl, rfl, rfl, query.evalPlanned_eq_eval left right⟩

theorem execute_commit_exact {state next : State} {result : Result}
    (success : execute state .commit = .ok (next, result)) :
    state.transactionSnapshot.isSome = true ∧
      next.database = state.database ∧
      next.transactionSnapshot = none ∧ result = {} ∧
      ∀ tableName,
        next.database.findTable? tableName =
          state.database.findTable? tableName := by
  unfold execute at success
  cases snapshot : state.transactionSnapshot with
  | none => simp [snapshot] at success
  | some database =>
      simp [snapshot] at success
      rcases success with ⟨stateEqual, resultEqual⟩
      subst next
      subst result
      exact ⟨by simp [snapshot], rfl, rfl, rfl, fun _ => rfl⟩

theorem execute_rollback_restores {state next : State} {result : Result}
    (success : execute state .rollback = .ok (next, result)) :
    next.database = state.transactionSnapshot.getD state.database := by
  unfold execute at success
  cases snapshot : state.transactionSnapshot with
  | none => simp [snapshot] at success
  | some database =>
      simp only [snapshot] at success
      have pairEqual := Except.ok.inj success
      have databaseEqual := congrArg (fun pair => pair.1.database) pairEqual
      simp only at databaseEqual
      rw [← databaseEqual]
      simp [snapshot]

end Core

end SQLeanite
