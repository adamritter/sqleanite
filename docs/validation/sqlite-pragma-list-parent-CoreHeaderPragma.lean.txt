import SQLeanite.CoreSchemaPragma

namespace SQLeanite.CoreHeaderPragma

def writes (name : String) (argument : Option Expr) : Bool :=
  SQLite.ApplicationHeader.supported name && argument.isSome

def persistentWrites (name : String) (argument : Option Expr) (schema : Option String) : Bool :=
  writes name argument && !schema.any (fun name => name.toLower == "temp")

def execute (state : Core.State) (name : String) (argument : Option Expr)
    (schema : Option String) : Except String (Core.State × List Core.Result) :=
  if schema.any (fun name => !["main", "temp"].contains name.toLower) then
    .error s!"unknown database {schema.getD ""}"
  else
    let temporary := schema.any (fun name => name.toLower == "temp")
    let metadata := state.headers.get temporary
    match argument with
    | none =>
        (fun value => (state, [{ rows := [[value]] }])) <$>
          SQLSurface.value (.integer (SQLite.ApplicationHeader.signed (metadata.get name)))
    | some argument =>
        match CoreSchemaPragma.argumentName argument with
        | none => .error "unsupported PRAGMA argument"
        | some source =>
            let value := SQLite.ApplicationHeader.word (SQLite.ApplicationHeader.atoi source)
            .ok ({ state with headers := state.headers.set temporary (metadata.set name value) }, [{}])

theorem execute_preserves_tables {state next : Core.State} {name : String}
    {argument : Option Expr} {schema : Option String} {results : List Core.Result}
    (success : execute state name argument schema = .ok (next, results)) :
    next.database = state.database := by
  unfold execute at success
  split at success
  · contradiction
  · cases argument with
    | none =>
        simp only [Functor.map, Except.map] at success
        split at success
        · contradiction
        · exact (congrArg (fun pair => pair.1.database) (Except.ok.inj success)).symm
    | some argument =>
        simp only at success
        split at success
        · contradiction
        · exact (congrArg (fun pair => pair.1.database) (Except.ok.inj success)).symm

theorem persistentWrites_temp (name : String) (argument : Option Expr) (schema : String)
    (temporary : schema.toLower = "temp") :
    persistentWrites name argument (some schema) = false := by
  simp [persistentWrites, temporary]

theorem execute_read_preserves_state {state next : Core.State} {name : String}
    {schema : Option String} {results : List Core.Result}
    (success : execute state name none schema = .ok (next, results)) : next = state := by
  unfold execute at success
  split at success
  · contradiction
  · simp only [Functor.map, Except.map] at success
    split at success
    · contradiction
    · exact (congrArg Prod.fst (Except.ok.inj success)).symm

end SQLeanite.CoreHeaderPragma
