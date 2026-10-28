import SQLeanite.Syntax.UnaryOp

namespace SQLeanite

structure TableConstraintDef where
  columns : Array String
  /-- Per-key-column syntax retained for checked admission and foreign schemas. -/
  collations : Array (Option String) := #[]
  descending : Array Bool := #[]
  primaryKey : Bool := false
  autoIncrement : Bool := false
  conflict : ConflictAction := .abort
  check : Option CheckDef := none
  references : Option ForeignKeyDef := none
  deriving Repr

inductive CompoundOp where
  | unionAll | unionDistinct | except | intersect
  deriving Repr, DecidableEq

/-- Original LIMIT expressions and spelling, retained for independent token
replay even after the admitted constant expressions are evaluated. -/
structure LimitClause where
  count : Expr
  offset : Option Expr := none
  comma : Bool := false
  deriving Repr

structure Select where
  columns : Array ResultColumn
  valueRows : Option (Array (Array Expr)) := none
  sources : Array TableRef := #[]
  where_ : Option Expr := none
  groupBy : Array Expr := #[]
  having : Option Expr := none
  orderBy : Array OrderTerm := #[]
  distinct : Bool := false
  limit : Option Nat := none
  offset : Nat := 0
  compounds : Array (CompoundOp × Select) := #[]
  limitClause : Option LimitClause := none
  deriving Repr

mutual
  /-- Maximum nesting of compound SELECT arms.  Exposing the list stored in
  the array makes this measure structurally recursive and kernel-transparent. -/
  def Select.compoundHeight : Select → Nat
    | { compounds := ⟨arms⟩, .. } => selectCompoundListHeight arms + 1

  def selectCompoundListHeight : List (CompoundOp × Select) → Nat
    | [] => 0
    | (_, query) :: queries => max query.compoundHeight (selectCompoundListHeight queries)
end

theorem selectCompoundListHeight_ge_of_mem {arm : CompoundOp × Select}
    {arms : List (CompoundOp × Select)} (member : arm ∈ arms) :
    arm.2.compoundHeight ≤ selectCompoundListHeight arms := by
  induction arms with
  | nil => simp at member
  | cons head tail induction =>
      obtain ⟨operation, query⟩ := head
      simp only [List.mem_cons] at member
      simp only [selectCompoundListHeight]
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (induction member) (Nat.le_max_right _ _)

theorem selectCompoundArrayHeight_ge_of_mem {arm : CompoundOp × Select}
    {arms : Array (CompoundOp × Select)} (member : arm ∈ arms) :
    arm.2.compoundHeight ≤ selectCompoundListHeight arms.toList := by
  exact selectCompoundListHeight_ge_of_mem (Array.mem_toList_iff.mpr member)

theorem Select.compoundHeight_positive (query : Select) : 0 < query.compoundHeight := by
  cases query
  simp only [Select.compoundHeight]
  omega

inductive CteMaterialization where
  | default | materialized | notMaterialized
  deriving Repr, DecidableEq, Inhabited

structure UpsertClause where
  target : Option (Array Expr) := none
  targetWhere : Option Expr := none
  assignments : Option (Array (String × Expr)) := none
  where_ : Option Expr := none
  deriving Repr

inductive Statement where
  | createTable (name : String) (columns : Array ColumnDef)
      (constraints : Array TableConstraintDef := #[]) (ifNotExists : Bool := false)
  | createStrictTable (name : String) (columns : Array ColumnDef)
      (constraints : Array TableConstraintDef := #[]) (ifNotExists : Bool := false)
  | createTableAs (name : String) (query : Select) (ifNotExists : Bool := false)
  | createView (name : String) (columns : Option (Array String)) (query : Select)
      (ifNotExists : Bool := false) (temporary : Bool := false) (sourceSql : String := "")
  | dropTable (name : String) (ifExists : Bool := false)
  | dropView (name : String) (ifExists : Bool := false)
  | createIndex (name table : String) (expressions : Array Expr := #[]) (unique : Bool := false)
      (where_ : Option Expr := none) (ifNotExists : Bool := false)
  | dropIndex (name : String) (ifExists : Bool := false)
  | createTrigger (name table : String) (event : TriggerEvent) (timing : TriggerTiming)
      (when_ : Option Expr) (body : Array Statement) (ifNotExists : Bool := false)
      (temporary : Bool := false) (displayName : String := "") (sourceSql : String := "")
  | dropTrigger (name : String) (ifExists : Bool := false)
  | alterAddColumn (table : String) (column : ColumnDef)
  | alterDropColumn (table column : String)
  | alterRenameTable (table newName : String)
  | alterRenameColumn (table oldName newName : String)
  | insert (table : String) (columns : Option (Array String)) (rows : Array (Array Expr))
      (conflict : ConflictAction := .default) (returning : Array ResultColumn := #[])
  | upsert (source : Statement) (alias : Option String) (clauses : Array UpsertClause)
  | insertSelect (table : String) (columns : Option (Array String)) (query : Select)
      (conflict : ConflictAction := .default) (returning : Array ResultColumn := #[])
  | delete (table : String) (alias : Option String) (where_ : Option Expr)
      (returning : Array ResultColumn := #[])
  | update (table : String) (alias : Option String) (assignments : Array (String × Expr))
      (where_ : Option Expr) (conflict : ConflictAction := .default) (returning : Array ResultColumn := #[])
  | withRecursive (name : String) (columns : Array String) (seed : Select)
      (step : Select) (all : Bool) (body : Statement)
      (materialization : CteMaterialization := .default)
  | withCte (name : String) (columns : Array String) (source body : Statement)
      (materialization : CteMaterialization := .default)
  | select (query : Select)
  | values (rows : Array (Array Expr))
  | begin | commit | rollback
  | savepoint (name : String)
  | release (name : String)
  | rollbackTo (name : String)
  | reindex
  | pragma (name : String) (argument : Option Expr) (schema : Option String := none)
  deriving Repr

mutual
  /-- Maximum nesting of executable statement containers (`WITH` and trigger
  bodies), including statements stored in arrays. -/
  def Statement.height : Statement → Nat
    | .createTrigger _ _ _ _ _ ⟨body⟩ _ _ _ _ => statementListHeight body + 1
    | .withRecursive _ _ _ _ _ body _ => body.height + 1
    | .upsert source _ _ => source.height + 1
    | .withCte _ _ source body _ => max source.height body.height + 1
    | _ => 1

  def statementListHeight : List Statement → Nat
    | [] => 0
    | statement :: statements => max statement.height (statementListHeight statements)
end

theorem statementListHeight_ge_of_mem {statement : Statement} {statements : List Statement}
    (member : statement ∈ statements) :
    statement.height ≤ statementListHeight statements := by
  induction statements with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      simp only [statementListHeight]
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (induction member) (Nat.le_max_right _ _)

theorem statementArrayHeight_ge_of_mem {statement : Statement} {statements : Array Statement}
    (member : statement ∈ statements) :
    statement.height ≤ statementListHeight statements.toList := by
  exact statementListHeight_ge_of_mem (Array.mem_toList_iff.mpr member)

theorem Statement.height_positive (statement : Statement) : 0 < statement.height := by
  cases statement <;> simp only [Statement.height] <;> omega

end SQLeanite
