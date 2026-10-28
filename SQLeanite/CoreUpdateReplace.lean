import SQLeanite.CoreNullConflict

/-! UPDATE REPLACE compiles the validated candidate to ordinary Core commands.
Its old row and every key conflict are removed before the single insertion.
The caller first freezes selected rowids, then re-seeks each in the current
state: earlier replacements can remove or overwrite a later pending row. -/
namespace SQLeanite.CoreUpdateReplace

def commands (stored : Core.Table) (old : Core.Integer) (row : Core.Row) : List Core.Command :=
  let declared := stored.findDeclaredPrimary? row
  let conflicts := stored.rows.filter fun existing =>
    existing.rowid == old || existing.rowid == row.rowid ||
      declared.any (fun previous => previous.rowid == existing.rowid) ||
      stored.indexes.any (fun index => index.rowConflict row existing)
  conflicts.map (fun existing => Core.Command.deleteWhere stored.schema.name
    (some (.equal stored.schema.primaryKey (.integer existing.rowid)))) ++
      [.insert stored.schema.name row.values]

/-- Resolve explicit REPLACE defaults before constructing the checked row.
The physical rowid still requires an integer on UPDATE. -/
def plan (stored : Core.Table) (old : Core.Integer) (values : List Core.Value) :
    Except String (List Core.Command) := do
  let some prepared ← CoreNullConflict.prepare stored.schema values true (some .replace)
    | throw "unexpected ignored REPLACE row"
  commands stored old <$> Core.Row.create stored.schema prepared

theorem plan_validated {stored : Core.Table} {old : Core.Integer}
    {values : List Core.Value} {trace : List Core.Command}
    (success : plan stored old values = .ok trace) :
    ∃ prepared row,
      CoreNullConflict.prepare stored.schema values true (some .replace) = .ok (some prepared) ∧
      Core.Row.create stored.schema prepared = .ok row ∧ trace = commands stored old row := by
  cases resolved : CoreNullConflict.prepare stored.schema values true (some .replace) with
  | error message => simp [plan, resolved, bind, Except.bind] at success
  | ok prepared =>
      cases prepared with
      | none => simp [plan, resolved, bind, Except.bind] at success
      | some prepared =>
          cases created : Core.Row.create stored.schema prepared with
          | error message => simp [plan, resolved, created, bind, Except.bind, Functor.map, Except.map] at success
          | ok row =>
              refine ⟨prepared, row, rfl, created, ?_⟩
              simpa [plan, resolved, created, bind, Except.bind, Functor.map, Except.map] using success.symm

/-- Accept only the exact point-delete selection trace produced by the SQL
predicate planner; malformed command shapes cannot silently omit a target. -/
def pending (table : String) (primaryKey : Nat) : List Core.Command → Except String (List Core.Integer)
  | [] => .ok []
  | .deleteWhere name (some (.equal column (.integer rowid))) :: rest => do
      unless name == table && column == primaryKey do throw "invalid UPDATE selection trace"
      return rowid :: (← pending table primaryKey rest)
  | _ => .error "invalid UPDATE selection trace"

theorem pending_length (table : String) (primaryKey : Nat) (trace : List Core.Command)
    (ids : List Core.Integer) (success : pending table primaryKey trace = .ok ids) :
    ids.length = trace.length := by
  induction trace generalizing ids with
  | nil => simpa [pending] using success
  | cons command rest ih =>
      cases command <;> try simp only [pending] at success
      all_goals try contradiction
      next name condition =>
        cases condition with
        | none => simp [pending] at success
        | some predicate =>
          cases predicate <;> try simp only [pending] at success
          all_goals try contradiction
          next column value =>
            cases value <;> try simp only [pending] at success
            all_goals try contradiction
            next rowid =>
              split at success
              · cases tail : pending table primaryKey rest with
                | error message => simp [tail, bind, Except.bind] at success
                | ok more =>
                    simp [tail, bind, Except.bind, pure, Except.pure] at success
                    subst ids
                    simpa using ih more tail
              · simp [bind, Except.bind] at success

end SQLeanite.CoreUpdateReplace
