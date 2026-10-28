import SQLeanite.Core.FindOrderedUpsertOfTrue

/-! INSERT OR IGNORE for the Core's NOT NULL, rowid, declared primary-key and
explicit UNIQUE constraints. Expression and datatype errors are not ignored. -/
namespace SQLeanite.CoreInsertIgnore

/-- A NULL rowid requests allocation. Other non-integer rowid values retain
SQLite's datatype-mismatch error even when a NOT NULL constraint also fails. -/
def rowidInput (schema : Core.Schema) (values : List Core.Value) : Bool :=
  match values[schema.primaryKey]? with
  | some .null | some (.integer _) => true
  | _ => false

def missingRequired (schema : Core.Schema) (values : List Core.Value) : Bool :=
  (schema.columns.zip values).zipIdx.any fun ((column, value), index) =>
    index != schema.primaryKey && column.notNull && value == .null

def conflict (stored : Core.Table) (row : Core.Row) : Bool :=
  stored.uniqueConflict row || (stored.findRowid? row.rowid).isSome ||
    (stored.findDeclaredPrimary? row).isSome

/-- Constraint checks use actual typed values and the current table. They do
not classify exceptions by message or suppress evaluator/storage failures. -/
def shouldInsert (stored : Core.Table) (values : List Core.Value) : Except String Bool :=
  if values.length != stored.schema.columns.length then .error "INSERT row width mismatch"
  else if !rowidInput stored.schema values then .error "datatype mismatch"
  else if missingRequired stored.schema values then .ok false
  else do
    let row ← stored.prepareRow values
    if (← stored.checkFailure row).isSome then return false
    return !conflict stored row

theorem shouldInsert_no_conflict {stored : Core.Table} {values : List Core.Value}
    (success : shouldInsert stored values = .ok true) :
    ∃ row, stored.createRow values = .ok row ∧ conflict stored row = false := by
  unfold shouldInsert at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success
  · simp at success
  · cases prepared : stored.prepareRow values with
    | error message => simp [prepared, bind, Except.bind] at success
    | ok row =>
        cases checked : stored.checkFailure row with
        | error message => simp [prepared, checked, bind, Except.bind] at success
        | ok failure =>
            cases failure with
            | some message => simp [prepared, checked, bind, Except.bind, pure, Except.pure] at success
            | none =>
                refine ⟨row, ?_, ?_⟩
                · simp [Core.Table.createRow, Core.Table.requireChecks, prepared, checked,
                    bind, Except.bind, pure, Except.pure]
                · simpa [prepared, checked, bind, Except.bind, pure, Except.pure] using success

end SQLeanite.CoreInsertIgnore
