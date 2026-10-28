import SQLeanite.Value

namespace SQLeanite

inductive UnaryOp where
  | plus | neg | not | bitNot
  deriving Repr, DecidableEq

inductive BinaryOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge | is | isNot
  | like | glob | match
  | and | or | concat | bitAnd | bitOr | shiftLeft | shiftRight | arrow | arrowText
  deriving Repr, DecidableEq

inductive Expr where
  /-- Numeric tokens retain non-compact source spellings for SQLite expression
  identity and signed-literal preparation. The token checker verifies both
  the spelling and its parsed value. -/
  | literal (value : Value) (spelling : Option String := none)
  | column (qualifier : Option String) (name : String)
  | star (qualifier : Option String := none)
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinaryOp) (left right : Expr)
  | call (name : String) (args : Array Expr) (star : Bool := false)
  | isNull (arg : Expr) (negated : Bool := false)
  | inList (arg : Expr) (values : Array Expr) (negated : Bool := false)
      (applyLeftAffinity : Bool := true)
  | collate (arg : Expr) (name : String)
  | case_ (base : Option Expr) (branches : Array (Expr × Expr)) (else_ : Option Expr)
  | scalarSubquery (sql : String)
  | inSubquery (arg : Expr) (sql : String) (negated : Bool := false)
  | existsSubquery (sql : String)
  deriving Repr, Inhabited

mutual
  /-- Maximum constructor nesting in an expression.  This is an executable,
  kernel-transparent measure over the nested arrays in `Expr`; unlike a
  `partial def`, it is available both to generated code and to termination
  proofs for the live evaluator. -/
  def Expr.height : Expr → Nat
    | .literal _ _ | .column _ _ | .star _ | .scalarSubquery _ | .existsSubquery _ => 1
    | .unary _ argument | .isNull argument _ | .collate argument _ |
        .inSubquery argument _ _ => argument.height + 1
    | .binary _ left right => max left.height right.height + 1
    | .call _ ⟨arguments⟩ _ => exprListHeight arguments + 1
    | .inList argument ⟨values⟩ _ _ => max argument.height (exprListHeight values) + 1
    | .case_ base ⟨branches⟩ else_ =>
        max (exprOptionHeight base)
          (max (exprPairListHeight branches) (exprOptionHeight else_)) + 1

  def exprListHeight : List Expr → Nat
    | [] => 0
    | expression :: expressions => max expression.height (exprListHeight expressions)

  def exprPairListHeight : List (Expr × Expr) → Nat
    | [] => 0
    | (first, second) :: branches =>
        max first.height (max second.height (exprPairListHeight branches))

  def exprOptionHeight : Option Expr → Nat
    | none => 0
    | some expression => expression.height
end

theorem exprListHeight_ge_of_mem {expression : Expr} {expressions : List Expr}
    (member : expression ∈ expressions) :
    expression.height ≤ exprListHeight expressions := by
  induction expressions with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      simp only [exprListHeight]
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (induction member) (Nat.le_max_right _ _)

theorem exprArrayHeight_ge_of_mem {expression : Expr} {expressions : Array Expr}
    (member : expression ∈ expressions) :
    expression.height ≤ exprListHeight expressions.toList := by
  exact exprListHeight_ge_of_mem (Array.mem_toList_iff.mpr member)

theorem exprArrayHeight_ge_get (expressions : Array Expr) (index : Nat)
    (valid : index < expressions.size) :
    expressions[index].height ≤ exprListHeight expressions.toList :=
  exprArrayHeight_ge_of_mem (Array.getElem_mem valid)

theorem exprPairListHeight_ge_first_of_mem {branch : Expr × Expr}
    {branches : List (Expr × Expr)} (member : branch ∈ branches) :
    branch.1.height ≤ exprPairListHeight branches := by
  induction branches with
  | nil => simp at member
  | cons head tail induction =>
      obtain ⟨first, second⟩ := head
      simp only [List.mem_cons] at member
      simp only [exprPairListHeight]
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (induction member)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem exprPairListHeight_ge_second_of_mem {branch : Expr × Expr}
    {branches : List (Expr × Expr)} (member : branch ∈ branches) :
    branch.2.height ≤ exprPairListHeight branches := by
  induction branches with
  | nil => simp at member
  | cons head tail induction =>
      obtain ⟨first, second⟩ := head
      simp only [List.mem_cons] at member
      simp only [exprPairListHeight]
      rcases member with rfl | member
      · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      · exact Nat.le_trans (induction member)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem exprPairArrayHeight_ge_first_of_mem {branch : Expr × Expr}
    {branches : Array (Expr × Expr)} (member : branch ∈ branches) :
    branch.1.height ≤ exprPairListHeight branches.toList := by
  exact exprPairListHeight_ge_first_of_mem (Array.mem_toList_iff.mpr member)

theorem exprPairArrayHeight_ge_second_of_mem {branch : Expr × Expr}
    {branches : Array (Expr × Expr)} (member : branch ∈ branches) :
    branch.2.height ≤ exprPairListHeight branches.toList := by
  exact exprPairListHeight_ge_second_of_mem (Array.mem_toList_iff.mpr member)

theorem Expr.height_positive (expression : Expr) : 0 < expression.height := by
  cases expression <;> simp only [Expr.height] <;> omega

mutual
  /-- Short-circuiting traversal over every expression node, including nodes
  stored in nested arrays and optional branches.  Predicates built from this
  operator inherit one total, kernel-transparent recursion scheme. -/
  def Expr.any (predicate : Expr → Bool) : Expr → Bool
    | expression@(.literal _ _) | expression@(.column _ _) | expression@(.star _) |
        expression@(.scalarSubquery _) | expression@(.existsSubquery _) =>
      predicate expression
    | expression@(.unary _ argument) | expression@(.isNull argument _) |
        expression@(.collate argument _) | expression@(.inSubquery argument _ _) =>
      predicate expression || argument.any predicate
    | expression@(.binary _ left right) =>
      predicate expression || left.any predicate || right.any predicate
    | expression@(.call _ ⟨arguments⟩ _) =>
      predicate expression || exprListAny predicate arguments
    | expression@(.inList argument ⟨values⟩ _ _) =>
      predicate expression || argument.any predicate || exprListAny predicate values
    | expression@(.case_ base ⟨branches⟩ else_) =>
      predicate expression || exprOptionAny predicate base ||
        exprPairListAny predicate branches || exprOptionAny predicate else_

  def exprListAny (predicate : Expr → Bool) : List Expr → Bool
    | [] => false
    | expression :: expressions => expression.any predicate || exprListAny predicate expressions

  def exprPairListAny (predicate : Expr → Bool) : List (Expr × Expr) → Bool
    | [] => false
    | (first, second) :: branches => first.any predicate || second.any predicate ||
        exprPairListAny predicate branches

  def exprOptionAny (predicate : Expr → Bool) : Option Expr → Bool
    | none => false
    | some expression => expression.any predicate
end

mutual
  /-- Variant used by SQL analyses whose scope deliberately stops at a
  subquery boundary.  For `IN`, the left operand belongs to the outer query,
  but SQLite's aggregate/default analyses treat the complete node as a
  boundary, matching their existing executable semantics. -/
  def Expr.anyOutsideSubqueries (predicate : Expr → Bool) : Expr → Bool
    | expression@(.literal _ _) | expression@(.column _ _) | expression@(.star _) |
        expression@(.scalarSubquery _) | expression@(.inSubquery _ _ _) |
        expression@(.existsSubquery _) => predicate expression
    | expression@(.unary _ argument) | expression@(.isNull argument _) |
        expression@(.collate argument _) =>
      predicate expression || argument.anyOutsideSubqueries predicate
    | expression@(.binary _ left right) => predicate expression ||
      left.anyOutsideSubqueries predicate || right.anyOutsideSubqueries predicate
    | expression@(.call _ ⟨arguments⟩ _) =>
      predicate expression || exprListAnyOutsideSubqueries predicate arguments
    | expression@(.inList argument ⟨values⟩ _ _) => predicate expression ||
      argument.anyOutsideSubqueries predicate || exprListAnyOutsideSubqueries predicate values
    | expression@(.case_ base ⟨branches⟩ else_) => predicate expression ||
      exprOptionAnyOutsideSubqueries predicate base ||
      exprPairListAnyOutsideSubqueries predicate branches ||
      exprOptionAnyOutsideSubqueries predicate else_

  def exprListAnyOutsideSubqueries (predicate : Expr → Bool) : List Expr → Bool
    | [] => false
    | expression :: expressions => expression.anyOutsideSubqueries predicate ||
        exprListAnyOutsideSubqueries predicate expressions

  def exprPairListAnyOutsideSubqueries (predicate : Expr → Bool) : List (Expr × Expr) → Bool
    | [] => false
    | (first, second) :: branches => first.anyOutsideSubqueries predicate ||
        second.anyOutsideSubqueries predicate || exprPairListAnyOutsideSubqueries predicate branches

  def exprOptionAnyOutsideSubqueries (predicate : Expr → Bool) : Option Expr → Bool
    | none => false
    | some expression => expression.anyOutsideSubqueries predicate
end

theorem exprListAny_of_mem {predicate : Expr → Bool} {expression : Expr}
    {expressions : List Expr} (member : expression ∈ expressions)
    (found : expression.any predicate = true) :
    exprListAny predicate expressions = true := by
  induction expressions with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      simp only [exprListAny, Bool.or_eq_true]
      rcases member with rfl | member
      · exact Or.inl found
      · exact Or.inr (induction member)

theorem Expr.any_call_of_argument {predicate : Expr → Bool} {name : String}
    {arguments : Array Expr} {star : Bool} {argument : Expr}
    (member : argument ∈ arguments) (found : argument.any predicate = true) :
    (Expr.call name arguments star).any predicate = true := by
  obtain ⟨arguments⟩ := arguments
  simp only [Expr.any, Bool.or_eq_true]
  exact Or.inr (exprListAny_of_mem (Array.mem_toList_iff.mpr member) found)

theorem Expr.any_of_root {predicate : Expr → Bool} {expression : Expr}
    (root : predicate expression = true) : expression.any predicate = true := by
  cases expression <;> simp_all only [Expr.any, Bool.true_or]

def distinctAggregatePrefix : String := "lean_distinct_aggregate_"

def distinctAggregateName (name : String) : String := distinctAggregatePrefix ++ name

def isDistinctAggregateName (name : String) : Bool :=
  name.startsWith distinctAggregatePrefix

def aggregateFunctionName (name : String) : String :=
  if name.startsWith distinctAggregatePrefix then
    (name.drop distinctAggregatePrefix.length).toString.toLower
  else name.toLower

def UnaryOp.sql : UnaryOp → String
  | .plus => "+" | .neg => "-" | .not => "NOT " | .bitNot => "~"

def BinaryOp.sql : BinaryOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "=" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .is => " IS " | .isNot => " IS NOT "
  | .like => " LIKE " | .glob => " GLOB " | .match => " MATCH "
  | .and => " AND " | .or => " OR " | .concat => "||" | .bitAnd => "&" | .bitOr => "|"
  | .shiftLeft => "<<" | .shiftRight => ">>" | .arrow => "->" | .arrowText => "->>"

private def exprSqlFuel : Nat → Expr → String
  | 0, _ => "..."
  | _fuel + 1, .literal .null _ => "NULL"
  | _fuel + 1, .literal (.text s) _ => "'" ++ s.replace "'" "''" ++ "'"
  | _fuel + 1, .literal v spelling => spelling.getD (toString v)
  | _fuel + 1, .column none name => name
  | _fuel + 1, .column (some q) name => q ++ "." ++ name
  | _fuel + 1, .star none => "*"
  | _fuel + 1, .star (some q) => q ++ ".*"
  | fuel + 1, .unary op e => op.sql ++ exprSqlFuel fuel e
  | fuel + 1, .binary op a b => exprSqlFuel fuel a ++ op.sql ++ exprSqlFuel fuel b
  | fuel + 1, .call "__sqlean_between" arguments false =>
      match arguments.toList with
      | [argument, lower, upper] =>
          exprSqlFuel fuel argument ++ " BETWEEN " ++ exprSqlFuel fuel lower ++ " AND " ++ exprSqlFuel fuel upper
      | _ => "..."
  | _fuel + 1, .call "__sqlean_boolean_true" #[] false => "TRUE"
  | _fuel + 1, .call "__sqlean_boolean_false" #[] false => "FALSE"
  | fuel + 1, .call "__sqlean_window" #[function, .literal (.text specification) _] false =>
      exprSqlFuel fuel function ++ " OVER " ++ specification
  | fuel + 1, .call "__sqlean_aggregate_filter" #[aggregate, condition] false =>
      exprSqlFuel fuel aggregate ++ " FILTER (WHERE " ++ exprSqlFuel fuel condition ++ ")"
  | fuel + 1, .call "__sqlean_aggregate_order" args false =>
      match args.toList with
      | .call name inputs false :: ordering =>
          let render (term : Expr) := match term with
            | .call direction #[expression] false =>
                exprSqlFuel fuel expression ++
                  (if direction.startsWith "__sqlean_order_desc" then " DESC" else " ASC") ++
                  (if direction.endsWith "_first" then " NULLS FIRST"
                    else if direction.endsWith "_last" then " NULLS LAST" else "")
            | _ => exprSqlFuel fuel term
          aggregateFunctionName name ++ "(" ++
            (if isDistinctAggregateName name then "DISTINCT " else "") ++
            String.intercalate "," (inputs.toList.map (exprSqlFuel fuel)) ++ " ORDER BY " ++
            String.intercalate "," (ordering.map render) ++ ")"
      | _ => "invalid aggregate ordering"
  | fuel + 1, .call name args isStar => aggregateFunctionName name ++ "(" ++
      (if isDistinctAggregateName name then "DISTINCT " else "") ++
      (if isStar then "*" else String.intercalate "," (args.toList.map (exprSqlFuel fuel))) ++ ")"
  | fuel + 1, .isNull e false => exprSqlFuel fuel e ++ " IS NULL"
  | fuel + 1, .isNull e true => exprSqlFuel fuel e ++ " IS NOT NULL"
  | fuel + 1, .inList e values false _ => exprSqlFuel fuel e ++ " IN (" ++
      String.intercalate "," (values.toList.map (exprSqlFuel fuel)) ++ ")"
  | fuel + 1, .inList e values true _ => exprSqlFuel fuel e ++ " NOT IN (" ++
      String.intercalate "," (values.toList.map (exprSqlFuel fuel)) ++ ")"
  | fuel + 1, .collate e name => exprSqlFuel fuel e ++ " COLLATE " ++ name
  | _fuel + 1, .case_ _ _ _ => "CASE ... END"
  | _fuel + 1, .scalarSubquery sql => "(" ++ sql ++ ")"
  | fuel + 1, .inSubquery e sql false => exprSqlFuel fuel e ++ " IN (" ++ sql ++ ")"
  | fuel + 1, .inSubquery e sql true => exprSqlFuel fuel e ++ " NOT IN (" ++ sql ++ ")"
  | _fuel + 1, .existsSubquery sql => "EXISTS (" ++ sql ++ ")"

def Expr.sql (expression : Expr) : String :=
  exprSqlFuel expression.height expression

theorem Expr.sql_text_literal (value : String) :
    (Expr.literal (.text value)).sql = "'" ++ value.replace "'" "''" ++ "'" := by
  rfl

structure ForeignKeyDef where
  table : String
  column : Option String := none
  onDeleteCascade : Bool := false
  deriving Repr, DecidableEq

structure CheckDef where
  expression : Expr
  name : Option String := none
  sourceSql : String := ""
  deriving Repr

/-- sqlite3Dequote stops at the first non-doubled closing quote. CHECK's
unnamed diagnostic runs this over the entire original expression span. -/
def CheckDef.dequoteChars (quote : Char) : List Char → List Char
  | [] => []
  | first :: rest =>
      if first == quote then
        match rest with
        | second :: tail => if second == quote then quote :: dequoteChars quote tail else []
        | [] => []
      else first :: dequoteChars quote rest

def CheckDef.dequote (source : String) : String :=
  match source.toList with
  | first :: rest =>
      if ['\'', '"', '`', '['].contains first then
        String.ofList (dequoteChars (if first == '[' then ']' else first) rest)
      else source
  | [] => source

def CheckDef.diagnostic (check : CheckDef) : String :=
  check.name.getD (dequote (if check.sourceSql.isEmpty then check.expression.sql else
    check.sourceSql.replace "lean_check_myfunc" "myfunc"))

theorem CheckDef.diagnostic_named (expression : Expr) (name sourceSql : String) :
    (CheckDef.mk expression (some name) sourceSql).diagnostic = name := by
  simp [CheckDef.diagnostic]

inductive ConflictAction where
  | default | abort | fail | rollback | replace | ignore
  deriving Repr, DecidableEq, Inhabited

def ConflictAction.resolve (statement constraint : ConflictAction) : ConflictAction :=
  if statement == .default then constraint else statement

theorem ConflictAction.resolve_default (constraint : ConflictAction) :
    ConflictAction.resolve .default constraint = constraint := by rfl

theorem ConflictAction.resolve_explicit_abort (constraint : ConflictAction) :
    ConflictAction.resolve .abort constraint = .abort := by rfl

structure ColumnDef where
  name : String
  declaredType : String := ""
  defaultValue : Option Expr := none
  generated : Option Expr := none
  notNull : Bool := false
  notNullConflict : ConflictAction := .abort
  primaryKey : Bool := false
  unique : Bool := false
  conflict : ConflictAction := .abort
  collation : String := "binary"
  references : Option ForeignKeyDef := none
  check : Option CheckDef := none
  defaultSql : Option String := none
  autoIncrement : Bool := false
  /-- Earlier DEFAULT clauses are checked even when a later clause overrides them. -/
  earlierDefaults : Array (Expr × String) := #[]
  /-- Earlier CHECK clauses are independent constraints, not overwritten declarations. -/
  earlierChecks : Array CheckDef := #[]
  generatedStored : Bool := false
  deriving Repr

inductive TriggerEvent where
  | insert | update | delete
  | updateOf (columns : Array String)
  deriving Repr, DecidableEq, Inhabited

inductive TriggerTiming where
  | before | after | insteadOf
  deriving Repr, DecidableEq, Inhabited

structure TableRef where
  name : String
  schema : Option String := none
  alias : Option String := none
  columnAliases : Array String := #[]
  subquerySql : Option String := none
  functionArgs : Option (Array Expr) := none
  joinOn : Option Expr := none
  usingColumns : Array String := #[]
  naturalJoin : Bool := false
  leftJoin : Bool := false
  rightJoin : Bool := false
  crossJoin : Bool := false
  deriving Repr

structure ResultColumn where
  expr : Expr
  alias : Option String := none
  sourceSql : Option String := none
  deriving Repr, Inhabited

structure OrderTerm where
  expr : Expr
  descending : Bool := false
  nullsFirst : Option Bool := none
  deriving Repr, Inhabited

inductive WindowBound where
  | unboundedPreceding | unboundedFollowing | current
  | preceding (offset : Expr) | following (offset : Expr)
  deriving Repr, Inhabited

structure WindowSpec where
  partition : Array Expr := #[]
  ordering : Array OrderTerm := #[]
  kind : String := "range"
  first : WindowBound := .unboundedPreceding
  last : WindowBound := .current
  explicitFrame : Bool := false
  deriving Repr
namespace AggregateOrder

/-- Internal syntax nodes retain ORDER direction and NULL placement without
changing the user function's actual argument list. The token grammar checks
these nodes only inside aggregate ORDER BY syntax. -/
def encode (term : OrderTerm) : Expr :=
  let direction := if term.descending then "desc" else "asc"
  let nulls := match term.nullsFirst with | none => "" | some true => "_first" | some false => "_last"
  .call ("__sqlean_order_" ++ direction ++ nulls) #[term.expr] false

def decode? : Expr → Option OrderTerm
  | .call name arguments false =>
      match arguments.toList with
      | [expression] => match name with
        | "__sqlean_order_asc" => some { expr := expression }
        | "__sqlean_order_desc" => some { expr := expression, descending := true }
        | "__sqlean_order_asc_first" => some { expr := expression, nullsFirst := some true }
        | "__sqlean_order_asc_last" => some { expr := expression, nullsFirst := some false }
        | "__sqlean_order_desc_first" => some { expr := expression, descending := true, nullsFirst := some true }
        | "__sqlean_order_desc_last" => some { expr := expression, descending := true, nullsFirst := some false }
        | _ => none
      | _ => none
  | _ => none

theorem decode_encode (term : OrderTerm) : decode? (encode term) = some term := by
  cases term with
  | mk expression descending nulls =>
      cases descending <;> cases nulls with
      | none => rfl
      | some first => cases first <;> rfl

end AggregateOrder

end SQLeanite
